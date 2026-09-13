// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use oxc_ast::ast::RegExpFlags;
use std::borrow::Cow;

use regex::bytes::{Regex, RegexBuilder};
use wtf8::Wtf8Buf;

use crate::{
    ecmascript::{OrdinaryObject, PropertyDescriptor, String, Value, execution::Agent},
    engine::bindable_handle,
    heap::{CompactionLists, HeapMarkAndSweep, WorkQueues},
};

/// ## Optimistic storage for the RegExp "lastIndex" property
///
/// The property can take any JavaScript Value, but under any reasonable use it
/// is an index into a JavaScript String which then means it is a 32-bit
/// unsigned integer since strings of 4 GiB length or larger are rare.
///
/// As such, the optimistic storage is a 32-bit unsigned integer with the
/// `u32::MAX` value used as a sentinel to signify that the backing object
/// should be asked for the actual value. If the backing object doesn't exist,
/// then the property value is `undefined`.
///
/// ### Writability of the "lastIndex" property
///
/// The `lastIndex` property can be made read-only using
/// `Object.defineProperty` or `Object.freeze`. These are rare operations and
/// as such, the writable bit of the "lastIndex" property is not stored in the
/// RegExp data at all. This means that if the backing object does not exists,
/// then the writable bit is guaranteed to be `true`. If the backing object
/// does exist, the writable bit must be asked from the backing object in all
/// cases.
#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub(crate) struct RegExpLastIndex(u32);

impl Default for RegExpLastIndex {
    fn default() -> Self {
        Self(u32::MAX)
    }
}

impl RegExpLastIndex {
    pub(crate) const ZERO: Self = Self(0);
    const INVALID: Self = Self(u32::MAX);

    /// Create a RegExpLastIndex from a JavaScript Value.
    pub(super) fn from_value(value: Value) -> Self {
        let Value::Integer(value) = value else {
            return Self::INVALID;
        };
        let value = value.into_i64();
        if let Ok(value) = u32::try_from(value) {
            if value == u32::MAX {
                Self::INVALID
            } else {
                Self(value)
            }
        } else {
            Self::INVALID
        }
    }

    /// Check if the RegExpLastIndex is an accurate JavaScript value.
    ///
    /// Note: If backing object does not exist, `undefined` is also accurately
    /// represented by an invalid RegExpLastIndex.
    #[inline]
    pub(super) fn is_valid(self) -> bool {
        self.0 != u32::MAX
    }

    /// Get the current lastIndex property index value.
    ///
    /// If the current value is not a 32-bit unsigned integer, then None is
    /// returned.
    pub(super) fn get_value(self) -> Option<u32> {
        if self.0 == u32::MAX {
            None
        } else {
            Some(self.0)
        }
    }

    /// Get the lastIndex property descriptor value.
    ///
    /// This property descriptor is only valid if the backing object does not
    /// exist. If it does exist, then this both the value and the writable bit
    /// of this descriptor may differ from the real values.
    pub(super) fn into_property_descriptor(self) -> PropertyDescriptor<'static> {
        PropertyDescriptor {
            value: Some(self.get_value().map_or(Value::Undefined, |i| i.into())),
            writable: Some(true),
            get: None,
            set: None,
            enumerable: Some(false),
            configurable: Some(false),
        }
    }
}

impl From<usize> for RegExpLastIndex {
    fn from(value: usize) -> Self {
        if let Ok(value) = u32::try_from(value) {
            if value == u32::MAX {
                Self::INVALID
            } else {
                Self(value)
            }
        } else {
            Self::INVALID
        }
    }
}

#[derive(Debug)]
pub(crate) struct RegExpHeapData<'a> {
    pub(super) object_index: Option<OrdinaryObject<'a>>,
    pub(super) reg_exp_matcher: Result<Regex, regex::Error>,
    pub(super) original_source: String<'a>,
    pub(super) original_flags: RegExpFlags,
    pub(super) last_index: RegExpLastIndex,
}

impl<'a> RegExpHeapData<'a> {
    /// JavaScript's pattern grammar is not the regex crate's. Rewrites the two
    /// pieces that mean something else there and leaves the rest alone: a
    /// literal `[` inside a character class, which the crate reads as a nested
    /// class, and `\0`, which it reads as a backreference and has none of.
    fn translate(pattern: &str) -> Cow<'_, str> {
        if !pattern.contains('[') && !pattern.contains("\\0") {
            return Cow::Borrowed(pattern);
        }

        let mut out = std::string::String::with_capacity(pattern.len());
        let mut chars = pattern.chars().peekable();
        let mut in_class = false;

        while let Some(ch) = chars.next() {
            match ch {
                '\\' => match chars.next() {
                    // A digit after it is an octal escape, which is its own
                    // thing; a bare one is the NUL character.
                    Some('0') if !chars.peek().is_some_and(char::is_ascii_digit) => {
                        out.push_str("\\x00")
                    }
                    Some(next) => {
                        out.push('\\');
                        out.push(next);
                    }
                    None => out.push('\\'),
                },
                '[' if in_class => out.push_str("\\["),
                '[' => {
                    // JavaScript's two empty classes: `[]` matches nothing and
                    // `[^]` matches anything, where the crate reads both as a
                    // class nobody closed.
                    let negated = chars.peek() == Some(&'^');

                    if negated {
                        chars.next();
                    }

                    if chars.peek() == Some(&']') {
                        chars.next();
                        out.push_str(if negated { "[\\s\\S]" } else { "[^\\s\\S]" });
                    } else {
                        in_class = true;
                        out.push('[');

                        if negated {
                            out.push('^');
                        }
                    }
                }
                ']' if in_class => {
                    in_class = false;
                    out.push(']');
                }
                _ => out.push(ch),
            }
        }

        Cow::Owned(out)
    }

    pub(crate) fn compile_pattern(
        pattern: &str,
        flags: RegExpFlags,
    ) -> Result<Regex, regex::Error> {
        RegexBuilder::new(&Self::translate(pattern))
            .dot_matches_new_line((flags & RegExpFlags::M).bits() > 0)
            .case_insensitive((flags & RegExpFlags::I).bits() > 0)
            .unicode(true)
            .dot_matches_new_line((flags & RegExpFlags::S).bits() > 0)
            .octal(false) // TODO: !strict
            .build()
    }

    pub(crate) fn new(agent: &Agent, source: String<'a>, flags: RegExpFlags) -> Self {
        let str = source.to_string_lossy_(agent);
        let regex = Self::compile_pattern(&str, flags);
        Self {
            object_index: None,
            reg_exp_matcher: regex,
            original_source: source,
            original_flags: flags,
            last_index: RegExpLastIndex::ZERO,
        }
    }

    pub(super) fn create_regexp_string(&self, agent: &Agent) -> Wtf8Buf {
        let string_length = self.original_source.len_(agent);
        let flags_length = self.original_flags.bits().count_ones();
        let mut regexp_string =
            Wtf8Buf::with_capacity(1 + string_length + 1 + flags_length as usize);
        regexp_string.push_char('/');
        regexp_string.push_wtf8(self.original_source.as_wtf8_(agent));
        regexp_string.push_char('/');
        self.original_flags.iter_names().for_each(|(flag, _)| {
            regexp_string.push_str(flag);
        });
        regexp_string
    }
}

impl Default for RegExpHeapData<'_> {
    fn default() -> Self {
        Self {
            object_index: Default::default(),
            reg_exp_matcher: Err(regex::Error::CompiledTooBig(usize::MAX)),
            original_source: String::EMPTY_STRING,
            original_flags: RegExpFlags::empty(),
            last_index: Default::default(),
        }
    }
}

bindable_handle!(RegExpHeapData);

impl HeapMarkAndSweep for RegExpHeapData<'static> {
    fn mark_values(&self, queues: &mut WorkQueues) {
        let Self {
            object_index,
            reg_exp_matcher: _,
            original_source,
            original_flags: _,
            last_index: _,
        } = self;
        object_index.mark_values(queues);
        original_source.mark_values(queues);
    }

    fn sweep_values(&mut self, compactions: &CompactionLists) {
        let Self {
            object_index,
            reg_exp_matcher: _,
            original_source,
            original_flags: _,
            last_index: _,
        } = self;
        object_index.sweep_values(compactions);
        original_source.sweep_values(compactions);
    }
}

#[cfg(test)]
mod translate_tests {
    use super::RegExpFlags;
    use super::RegExpHeapData;

    fn compiles(pattern: &str) -> bool {
        RegExpHeapData::compile_pattern(pattern, RegExpFlags::empty()).is_ok()
    }

    #[test]
    fn a_literal_bracket_inside_a_class_compiles() {
        // What every escapeRegExp in the wild is written with.
        assert!(compiles(r"[.*+?^${}()|[\]\\]"));
        assert!(compiles(r"[[]"));
    }

    #[test]
    fn a_nul_escape_is_the_character_not_a_backreference() {
        assert!(compiles(r"[\0\n\r]"));
        assert!(compiles(r"\0"));
    }

    #[test]
    fn a_pattern_with_neither_is_left_alone() {
        assert!(matches!(
            RegExpHeapData::translate(r"a+b*c?"),
            std::borrow::Cow::Borrowed(_)
        ));
    }

    #[test]
    fn the_empty_classes_compile_to_what_they_mean() {
        // `[^]` is how a JavaScript pattern says "including newlines".
        let any = RegExpHeapData::compile_pattern(r"[^]", RegExpFlags::empty()).unwrap();
        assert!(any.is_match(b"\n"));

        let none = RegExpHeapData::compile_pattern(r"[]", RegExpFlags::empty()).unwrap();
        assert!(!none.is_match(b"a"));
    }

    #[test]
    fn a_class_that_was_closed_takes_a_bracket_again() {
        assert!(compiles(r"[a][b]"));
    }
}
