//! Unicode property definitions and combinators.

use super::Property;
#[allow(unused_imports)]
use icu_properties::{self as icup, maps, sets};

#[doc(inline)]
pub use crate::{unicode_prop_all as all, unicode_prop_any as any};

#[doc(hidden)]
#[macro_export]
macro_rules! unicode_prop_all {
    ($prop:expr) => {{
        $prop
    }};
    ($prop0:expr, $($propn:expr),+) => {{
        $crate::unicode::prop::and($prop0, $crate::unicode::prop::all!($($propn),+))
    }};
    ($($prop:expr,)+) => {{
        $crate::unicode::prop::all!($($prop),*)
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! unicode_prop_any {
    ($prop:expr) => {{
        $prop
    }};
    ($prop0:expr, $($propn:expr),+) => {{
        $crate::unicode::prop::or($prop0, $crate::unicode::prop::any!($($propn),+))
    }};
    ($($prop:expr,)+) => {{
        $crate::unicode::prop::any!($($prop),*)
    }};
}

#[derive(Debug, Clone, Copy)]
pub struct Not<P: Property>(P);

#[derive(Debug, Clone, Copy)]
pub struct And<L: Property, R: Property>(L, R);

#[derive(Debug, Clone, Copy)]
pub struct Or<L: Property, R: Property>(L, R);

pub const fn not<P: Property>(property: P) -> Not<P> {
    Not(property)
}

pub const fn and<L: Property, R: Property>(lhs: L, rhs: R) -> And<L, R> {
    And(lhs, rhs)
}

pub const fn or<L: Property, R: Property>(lhs: L, rhs: R) -> Or<L, R> {
    Or(lhs, rhs)
}

impl<P: Property> Property for Not<P> {
    fn contains(self, ch: char) -> bool {
        !self.0.contains(ch)
    }
}

impl<L: Property, R: Property> core::ops::BitAnd<R> for Not<L> {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<L: Property, R: Property> core::ops::BitOr<R> for Not<L> {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

impl<L: Property, R: Property> Property for And<L, R> {
    fn contains(self, ch: char) -> bool {
        self.0.contains(ch) && self.1.contains(ch)
    }
}

impl<L: Property, R: Property> core::ops::Not for And<L, R> {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<LL: Property, LR: Property, R: Property> core::ops::BitAnd<R> for And<LL, LR> {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<LL: Property, LR: Property, R: Property> core::ops::BitOr<R> for And<LL, LR> {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

impl<L: Property, R: Property> Property for Or<L, R> {
    fn contains(self, ch: char) -> bool {
        self.0.contains(ch) || self.1.contains(ch)
    }
}

impl<L: Property, R: Property> core::ops::Not for Or<L, R> {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<LL: Property, LR: Property, R: Property> core::ops::BitAnd<R> for Or<LL, LR> {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<LL: Property, LR: Property, R: Property> core::ops::BitOr<R> for Or<LL, LR> {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

macro_rules! def_bool_prop {
    ($(#[$($attr:tt)*])* $ty:ident => $set:expr) => {
        $(#[$($attr)*])*
        #[derive(Debug, Clone, Copy)]
        pub struct $ty;

        impl Property for $ty {
            fn contains(self, ch: char) -> bool {
                const { $set }.contains(ch)
            }
        }

        impl core::ops::Not for $ty {
            type Output = Not<Self>;

            fn not(self) -> Not<Self> {
                Not(self)
            }
        }

        impl<R: Property> core::ops::BitAnd<R> for $ty {
            type Output = And<Self, R>;

            fn bitand(self, rhs: R) -> And<Self, R> {
                And(self, rhs)
            }
        }

        impl<R: Property> core::ops::BitOr<R> for $ty {
            type Output = Or<Self, R>;

            fn bitor(self, rhs: R) -> Or<Self, R> {
                Or(self, rhs)
            }
        }
    };
}

def_bool_prop!(Alphabetic => sets::alphabetic());
def_bool_prop!(AsciiHexDigit => sets::ascii_hex_digit());
def_bool_prop!(BidiControl => sets::bidi_control());
def_bool_prop!(BidiMirrored => sets::bidi_mirrored());
def_bool_prop!(CaseIgnorable => sets::case_ignorable());
def_bool_prop!(Cased => sets::cased());
def_bool_prop!(ChangesWhenCasefolded => sets::changes_when_casefolded());
def_bool_prop!(ChangesWhenCasemapped => sets::changes_when_casemapped());
def_bool_prop!(ChangesWhenLowercased => sets::changes_when_lowercased());
def_bool_prop!(ChangesWhenNfkcCasefolded => sets::changes_when_nfkc_casefolded());
def_bool_prop!(ChangesWhenTitlecased => sets::changes_when_titlecased());
def_bool_prop!(ChangesWhenUppercased => sets::changes_when_uppercased());
def_bool_prop!(Dash => sets::dash());
def_bool_prop!(DefaultIgnorableCodePoint => sets::default_ignorable_code_point());
def_bool_prop!(Deprecated => sets::deprecated());
def_bool_prop!(Diacritic => sets::diacritic());
def_bool_prop!(Emoji => sets::emoji());
def_bool_prop!(EmojiComponent => sets::emoji_component());
def_bool_prop!(EmojiModifier => sets::emoji_modifier());
def_bool_prop!(EmojiModifierBase => sets::emoji_modifier_base());
def_bool_prop!(EmojiPresentation => sets::emoji_presentation());
def_bool_prop!(ExtendedPictographic => sets::extended_pictographic());
def_bool_prop!(Extender => sets::extender());
def_bool_prop!(FullCompositionExclusion => sets::full_composition_exclusion());
def_bool_prop!(GraphemeBase => sets::grapheme_base());
def_bool_prop!(GraphemeExtend => sets::grapheme_extend());
def_bool_prop!(GraphemeLink => sets::grapheme_link());
def_bool_prop!(HexDigit => sets::hex_digit());
def_bool_prop!(Hyphen => sets::hyphen());
def_bool_prop!(IdContinue => sets::id_continue());
def_bool_prop!(IdStart => sets::id_start());
def_bool_prop!(Ideographic => sets::ideographic());
def_bool_prop!(IdsBinaryOperator => sets::ids_binary_operator());
def_bool_prop!(IdsTrinaryOperator => sets::ids_trinary_operator());
def_bool_prop!(JoinControl => sets::join_control());
def_bool_prop!(LogicalOrderException => sets::logical_order_exception());
def_bool_prop!(Lowercase => sets::lowercase());
def_bool_prop!(Math => sets::math());
def_bool_prop!(NoncharacterCodePoint => sets::noncharacter_code_point());
def_bool_prop!(PatternSyntax => sets::pattern_syntax());
def_bool_prop!(PatternWhiteSpace => sets::pattern_white_space());
def_bool_prop!(PrependedConcatenationMark => sets::prepended_concatenation_mark());
def_bool_prop!(QuotationMark => sets::quotation_mark());
def_bool_prop!(Radical => sets::radical());
def_bool_prop!(RegionalIndicator => sets::regional_indicator());
def_bool_prop!(SentenceTerminal => sets::sentence_terminal());
def_bool_prop!(SoftDotted => sets::soft_dotted());
def_bool_prop!(TerminalPunctuation => sets::terminal_punctuation());
def_bool_prop!(UnifiedIdeograph => sets::unified_ideograph());
def_bool_prop!(Uppercase => sets::uppercase());
def_bool_prop!(VariationSelector => sets::variation_selector());
def_bool_prop!(WhiteSpace => sets::white_space());
def_bool_prop!(XidContinue => sets::xid_continue());
def_bool_prop!(XidStart => sets::xid_start());

macro_rules! def_enum_prop {
    ($(#[$($attr:tt)*])* enum $name:ident { $($(#[$($vattr:tt)*])* $var:ident => $val:path),* $(,)* } => $map:expr , default = $dvar:ident) => {
        $(#[$($attr)*])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub enum $name {
            $(
                $(#[$($vattr)*])*
                $var,
            )*
        }

        impl $name {
            /// Gets the property value of a code point.
            pub fn of(ch: char) -> Self {
                let val = const { &($map) }.get(ch);
                match val {
                    $(
                        $val => Self::$var,
                    )*
                    #[allow(unreachable_patterns)]
                    _ => Self::$dvar,
                }
            }
        }

        impl Property for $name {
            fn contains(self, ch: char) -> bool {
                self == Self::of(ch)
            }
        }

        impl core::ops::Not for $name {
            type Output = Not<Self>;

            fn not(self) -> Not<Self> {
                Not(self)
            }
        }

        impl<R: Property> core::ops::BitAnd<R> for $name {
            type Output = And<Self, R>;

            fn bitand(self, rhs: R) -> And<Self, R> {
                And(self, rhs)
            }
        }

        impl<R: Property> core::ops::BitOr<R> for $name {
            type Output = Or<Self, R>;

            fn bitor(self, rhs: R) -> Or<Self, R> {
                Or(self, rhs)
            }
        }
    };
}

def_enum_prop! {
    enum BidiClass {
        LeftToRight => icup::BidiClass::LeftToRight,
        RightToLeft => icup::BidiClass::RightToLeft,
        EuropeanNumber => icup::BidiClass::EuropeanNumber,
        EuropeanSeparator => icup::BidiClass::EuropeanSeparator,
        EuropeanTerminator => icup::BidiClass::EuropeanTerminator,
        ArabicNumber => icup::BidiClass::ArabicNumber,
        CommonSeparator => icup::BidiClass::CommonSeparator,
        ParagraphSeparator => icup::BidiClass::ParagraphSeparator,
        SegmentSeparator => icup::BidiClass::SegmentSeparator,
        WhiteSpace => icup::BidiClass::WhiteSpace,
        OtherNeutral => icup::BidiClass::OtherNeutral,
        LeftToRightEmbedding => icup::BidiClass::LeftToRightEmbedding,
        LeftToRightOverride => icup::BidiClass::LeftToRightOverride,
        ArabicLetter => icup::BidiClass::ArabicLetter,
        RightToLeftEmbedding => icup::BidiClass::RightToLeftEmbedding,
        RightToLeftOverride => icup::BidiClass::RightToLeftOverride,
        PopDirectionalFormat => icup::BidiClass::PopDirectionalFormat,
        NonspacingMark => icup::BidiClass::NonspacingMark,
        BoundaryNeutral => icup::BidiClass::BoundaryNeutral,
        FirstStrongIsolate => icup::BidiClass::FirstStrongIsolate,
        LeftToRightIsolate => icup::BidiClass::LeftToRightIsolate,
        RightToLeftIsolate => icup::BidiClass::RightToLeftIsolate,
        PopDirectionalIsolate => icup::BidiClass::PopDirectionalIsolate,
    } => maps::bidi_class(),
    default = LeftToRight
}

def_enum_prop! {
    enum CanonicalCombiningClass {
        NotReordered => icup::CanonicalCombiningClass::NotReordered,
        Overlay => icup::CanonicalCombiningClass::Overlay,
        HanReading => icup::CanonicalCombiningClass::HanReading,
        Nukta => icup::CanonicalCombiningClass::Nukta,
        KanaVoicing => icup::CanonicalCombiningClass::KanaVoicing,
        Virama => icup::CanonicalCombiningClass::Virama,
        CCC10 => icup::CanonicalCombiningClass::CCC10,
        CCC11 => icup::CanonicalCombiningClass::CCC11,
        CCC12 => icup::CanonicalCombiningClass::CCC12,
        CCC13 => icup::CanonicalCombiningClass::CCC13,
        CCC14 => icup::CanonicalCombiningClass::CCC14,
        CCC15 => icup::CanonicalCombiningClass::CCC15,
        CCC16 => icup::CanonicalCombiningClass::CCC16,
        CCC17 => icup::CanonicalCombiningClass::CCC17,
        CCC18 => icup::CanonicalCombiningClass::CCC18,
        CCC19 => icup::CanonicalCombiningClass::CCC19,
        CCC20 => icup::CanonicalCombiningClass::CCC20,
        CCC21 => icup::CanonicalCombiningClass::CCC21,
        CCC22 => icup::CanonicalCombiningClass::CCC22,
        CCC23 => icup::CanonicalCombiningClass::CCC23,
        CCC24 => icup::CanonicalCombiningClass::CCC24,
        CCC25 => icup::CanonicalCombiningClass::CCC25,
        CCC26 => icup::CanonicalCombiningClass::CCC26,
        CCC27 => icup::CanonicalCombiningClass::CCC27,
        CCC28 => icup::CanonicalCombiningClass::CCC28,
        CCC29 => icup::CanonicalCombiningClass::CCC29,
        CCC30 => icup::CanonicalCombiningClass::CCC30,
        CCC31 => icup::CanonicalCombiningClass::CCC31,
        CCC32 => icup::CanonicalCombiningClass::CCC32,
        CCC33 => icup::CanonicalCombiningClass::CCC33,
        CCC34 => icup::CanonicalCombiningClass::CCC34,
        CCC35 => icup::CanonicalCombiningClass::CCC35,
        CCC36 => icup::CanonicalCombiningClass::CCC36,
        CCC84 => icup::CanonicalCombiningClass::CCC84,
        CCC91 => icup::CanonicalCombiningClass::CCC91,
        CCC103 => icup::CanonicalCombiningClass::CCC103,
        CCC107 => icup::CanonicalCombiningClass::CCC107,
        CCC118 => icup::CanonicalCombiningClass::CCC118,
        CCC122 => icup::CanonicalCombiningClass::CCC122,
        CCC129 => icup::CanonicalCombiningClass::CCC129,
        CCC130 => icup::CanonicalCombiningClass::CCC130,
        CCC132 => icup::CanonicalCombiningClass::CCC132,
        AttachedBelowLeft => icup::CanonicalCombiningClass::AttachedBelowLeft,
        AttachedBelow => icup::CanonicalCombiningClass::AttachedBelow,
        AttachedAbove => icup::CanonicalCombiningClass::AttachedAbove,
        AttachedAboveRight => icup::CanonicalCombiningClass::AttachedAboveRight,
        BelowLeft => icup::CanonicalCombiningClass::BelowLeft,
        Below => icup::CanonicalCombiningClass::Below,
        BelowRight => icup::CanonicalCombiningClass::BelowRight,
        Left => icup::CanonicalCombiningClass::Left,
        Right => icup::CanonicalCombiningClass::Right,
        AboveLeft => icup::CanonicalCombiningClass::AboveLeft,
        Above => icup::CanonicalCombiningClass::Above,
        AboveRight => icup::CanonicalCombiningClass::AboveRight,
        DoubleBelow => icup::CanonicalCombiningClass::DoubleBelow,
        DoubleAbove => icup::CanonicalCombiningClass::DoubleAbove,
        IotaSubscript => icup::CanonicalCombiningClass::IotaSubscript,
    } => maps::canonical_combining_class(),
    default = NotReordered
}

def_enum_prop! {
    enum EastAsianWidth {
        Neutral => icup::EastAsianWidth::Neutral,
        Ambiguous => icup::EastAsianWidth::Ambiguous,
        Halfwidth => icup::EastAsianWidth::Halfwidth,
        Fullwidth => icup::EastAsianWidth::Fullwidth,
        Narrow => icup::EastAsianWidth::Narrow,
        Wide => icup::EastAsianWidth::Wide,
    } => maps::east_asian_width(),
    default = Neutral
}

def_enum_prop! {
    enum GeneralCategory {
        Unassigned => icup::GeneralCategory::Unassigned,
        UppercaseLetter => icup::GeneralCategory::UppercaseLetter,
        LowercaseLetter => icup::GeneralCategory::LowercaseLetter,
        TitlecaseLetter => icup::GeneralCategory::TitlecaseLetter,
        ModifierLetter => icup::GeneralCategory::ModifierLetter,
        OtherLetter => icup::GeneralCategory::OtherLetter,
        NonspacingMark => icup::GeneralCategory::NonspacingMark,
        SpacingMark => icup::GeneralCategory::SpacingMark,
        EnclosingMark => icup::GeneralCategory::EnclosingMark,
        DecimalNumber => icup::GeneralCategory::DecimalNumber,
        LetterNumber => icup::GeneralCategory::LetterNumber,
        OtherNumber => icup::GeneralCategory::OtherNumber,
        SpaceSeparator => icup::GeneralCategory::SpaceSeparator,
        LineSeparator => icup::GeneralCategory::LineSeparator,
        ParagraphSeparator => icup::GeneralCategory::ParagraphSeparator,
        Control => icup::GeneralCategory::Control,
        Format => icup::GeneralCategory::Format,
        PrivateUse => icup::GeneralCategory::PrivateUse,
        Surrogate => icup::GeneralCategory::Surrogate,
        DashPunctuation => icup::GeneralCategory::DashPunctuation,
        OpenPunctuation => icup::GeneralCategory::OpenPunctuation,
        ClosePunctuation => icup::GeneralCategory::ClosePunctuation,
        ConnectorPunctuation => icup::GeneralCategory::ConnectorPunctuation,
        InitialPunctuation => icup::GeneralCategory::InitialPunctuation,
        FinalPunctuation => icup::GeneralCategory::FinalPunctuation,
        OtherPunctuation => icup::GeneralCategory::OtherPunctuation,
        MathSymbol => icup::GeneralCategory::MathSymbol,
        CurrencySymbol => icup::GeneralCategory::CurrencySymbol,
        ModifierSymbol => icup::GeneralCategory::ModifierSymbol,
        OtherSymbol => icup::GeneralCategory::OtherSymbol,
    } => maps::general_category(),
    default = Unassigned
}

impl GeneralCategory {
    #[allow(non_upper_case_globals)]
    pub const Cc: Self = Self::Control;

    #[allow(non_upper_case_globals)]
    pub const Cf: Self = Self::Format;

    #[allow(non_upper_case_globals)]
    pub const Co: Self = Self::PrivateUse;

    #[allow(non_upper_case_globals)]
    pub const Cs: Self = Self::Surrogate;

    #[allow(non_upper_case_globals)]
    pub const Ll: Self = Self::LowercaseLetter;

    #[allow(non_upper_case_globals)]
    pub const Lm: Self = Self::ModifierLetter;

    #[allow(non_upper_case_globals)]
    pub const Lo: Self = Self::OtherLetter;

    #[allow(non_upper_case_globals)]
    pub const Lt: Self = Self::TitlecaseLetter;

    #[allow(non_upper_case_globals)]
    pub const Lu: Self = Self::UppercaseLetter;

    #[allow(non_upper_case_globals)]
    pub const Mc: Self = Self::SpacingMark;

    #[allow(non_upper_case_globals)]
    pub const Me: Self = Self::EnclosingMark;

    #[allow(non_upper_case_globals)]
    pub const Mn: Self = Self::NonspacingMark;

    #[allow(non_upper_case_globals)]
    pub const Nd: Self = Self::DecimalNumber;

    #[allow(non_upper_case_globals)]
    pub const Nl: Self = Self::LetterNumber;

    #[allow(non_upper_case_globals)]
    pub const No: Self = Self::OtherNumber;

    #[allow(non_upper_case_globals)]
    pub const Pc: Self = Self::ConnectorPunctuation;

    #[allow(non_upper_case_globals)]
    pub const Pd: Self = Self::DashPunctuation;

    #[allow(non_upper_case_globals)]
    pub const Pe: Self = Self::ClosePunctuation;

    #[allow(non_upper_case_globals)]
    pub const Pf: Self = Self::FinalPunctuation;

    #[allow(non_upper_case_globals)]
    pub const Pi: Self = Self::InitialPunctuation;

    #[allow(non_upper_case_globals)]
    pub const Po: Self = Self::OtherPunctuation;

    #[allow(non_upper_case_globals)]
    pub const Ps: Self = Self::OpenPunctuation;

    #[allow(non_upper_case_globals)]
    pub const Sc: Self = Self::CurrencySymbol;

    #[allow(non_upper_case_globals)]
    pub const Sk: Self = Self::ModifierSymbol;

    #[allow(non_upper_case_globals)]
    pub const Sm: Self = Self::MathSymbol;

    #[allow(non_upper_case_globals)]
    pub const So: Self = Self::OtherSymbol;

    #[allow(non_upper_case_globals)]
    pub const Zl: Self = Self::LineSeparator;

    #[allow(non_upper_case_globals)]
    pub const Zp: Self = Self::ParagraphSeparator;

    #[allow(non_upper_case_globals)]
    pub const Zs: Self = Self::SpaceSeparator;

    pub const L: Or<Self, Or<Self, Or<Self, Or<Self, Self>>>> =
        or(Self::Ll, or(Self::Lu, or(Self::Lt, or(Self::Lm, Self::Lo))));

    pub const C: Or<Self, Or<Self, Or<Self, Self>>> =
        or(Self::Cc, or(Self::Cf, or(Self::Co, Self::Cs)));

    pub const M: Or<Self, Or<Self, Self>> = or(Self::Mc, or(Self::Me, Self::Mn));

    pub const N: Or<Self, Or<Self, Self>> = or(Self::Nd, or(Self::Nl, Self::No));

    pub const P: Or<Self, Or<Self, Or<Self, Or<Self, Or<Self, Or<Self, Self>>>>>> = or(
        Self::Pc,
        or(
            Self::Pd,
            or(Self::Pe, or(Self::Pf, or(Self::Pi, or(Self::Po, Self::Ps)))),
        ),
    );

    pub const S: Or<Self, Or<Self, Or<Self, Self>>> =
        or(Self::Sc, or(Self::Sk, or(Self::Sm, Self::So)));

    pub const Z: Or<Self, Or<Self, Self>> = or(Self::Zl, or(Self::Zp, Self::Zs));
}

def_enum_prop! {
    enum GraphemeClusterBreak {
        Other => icup::GraphemeClusterBreak::Other,
        Control => icup::GraphemeClusterBreak::Control,
        CR => icup::GraphemeClusterBreak::CR,
        Extend => icup::GraphemeClusterBreak::Extend,
        L => icup::GraphemeClusterBreak::L,
        LF => icup::GraphemeClusterBreak::LF,
        LV => icup::GraphemeClusterBreak::LV,
        LVT => icup::GraphemeClusterBreak::LVT,
        T => icup::GraphemeClusterBreak::T,
        V => icup::GraphemeClusterBreak::V,
        SpacingMark => icup::GraphemeClusterBreak::SpacingMark,
        Prepend => icup::GraphemeClusterBreak::Prepend,
        RegionalIndicator => icup::GraphemeClusterBreak::RegionalIndicator,
        EBase => icup::GraphemeClusterBreak::EBase,
        EBaseGAZ => icup::GraphemeClusterBreak::EBaseGAZ,
        EModifier => icup::GraphemeClusterBreak::EModifier,
        GlueAfterZwj => icup::GraphemeClusterBreak::GlueAfterZwj,
        ZWJ => icup::GraphemeClusterBreak::ZWJ,
    } => maps::grapheme_cluster_break(),
    default = Other
}

def_enum_prop! {
    enum HangulSyllableType {
        NotApplicable => icup::HangulSyllableType::NotApplicable,
        VowelJamo => icup::HangulSyllableType::VowelJamo,
        TrailingJamo => icup::HangulSyllableType::TrailingJamo,
        LeadingVowelSyllable => icup::HangulSyllableType::LeadingVowelSyllable,
        LeadingVowelTrailingSyllable => icup::HangulSyllableType::LeadingVowelTrailingSyllable,
    } => maps::hangul_syllable_type(),
    default = NotApplicable
}

def_enum_prop! {
    enum IndicSyllabicCategory {
        Other => icup::IndicSyllabicCategory::Other,
        Avagraha => icup::IndicSyllabicCategory::Avagraha,
        Bindu => icup::IndicSyllabicCategory::Bindu,
        BrahmiJoiningNumber => icup::IndicSyllabicCategory::BrahmiJoiningNumber,
        CantillationMark => icup::IndicSyllabicCategory::CantillationMark,
        Consonant => icup::IndicSyllabicCategory::Consonant,
        ConsonantDead => icup::IndicSyllabicCategory::ConsonantDead,
        ConsonantFinal => icup::IndicSyllabicCategory::ConsonantFinal,
        ConsonantHeadLetter => icup::IndicSyllabicCategory::ConsonantHeadLetter,
        ConsonantInitialPostfixed => icup::IndicSyllabicCategory::ConsonantInitialPostfixed,
        ConsonantKiller => icup::IndicSyllabicCategory::ConsonantKiller,
        ConsonantMedial => icup::IndicSyllabicCategory::ConsonantMedial,
        ConsonantPlaceholder => icup::IndicSyllabicCategory::ConsonantPlaceholder,
        ConsonantPrecedingRepha => icup::IndicSyllabicCategory::ConsonantPrecedingRepha,
        ConsonantPrefixed => icup::IndicSyllabicCategory::ConsonantPrefixed,
        ConsonantSucceedingRepha => icup::IndicSyllabicCategory::ConsonantSucceedingRepha,
        ConsonantSubjoined => icup::IndicSyllabicCategory::ConsonantSubjoined,
        ConsonantWithStacker => icup::IndicSyllabicCategory::ConsonantWithStacker,
        GeminationMark => icup::IndicSyllabicCategory::GeminationMark,
        InvisibleStacker => icup::IndicSyllabicCategory::InvisibleStacker,
        Joiner => icup::IndicSyllabicCategory::Joiner,
        ModifyingLetter => icup::IndicSyllabicCategory::ModifyingLetter,
        NonJoiner => icup::IndicSyllabicCategory::NonJoiner,
        Nukta => icup::IndicSyllabicCategory::Nukta,
        Number => icup::IndicSyllabicCategory::Number,
        NumberJoiner => icup::IndicSyllabicCategory::NumberJoiner,
        PureKiller => icup::IndicSyllabicCategory::PureKiller,
        RegisterShifter => icup::IndicSyllabicCategory::RegisterShifter,
        SyllableModifier => icup::IndicSyllabicCategory::SyllableModifier,
        ToneLetter => icup::IndicSyllabicCategory::ToneLetter,
        ToneMark => icup::IndicSyllabicCategory::ToneMark,
        Virama => icup::IndicSyllabicCategory::Virama,
        Visarga => icup::IndicSyllabicCategory::Visarga,
        Vowel => icup::IndicSyllabicCategory::Vowel,
        VowelDependent => icup::IndicSyllabicCategory::VowelDependent,
        VowelIndependent => icup::IndicSyllabicCategory::VowelIndependent,
    } => maps::indic_syllabic_category(),
    default = Other
}

def_enum_prop! {
    enum JoiningType {
        NonJoining => icup::JoiningType::NonJoining,
        JoinCausing => icup::JoiningType::JoinCausing,
        DualJoining => icup::JoiningType::DualJoining,
        LeftJoining => icup::JoiningType::LeftJoining,
        RightJoining => icup::JoiningType::RightJoining,
        Transparent => icup::JoiningType::Transparent,
    } => maps::joining_type(),
    default = NonJoining
}

def_enum_prop! {
    enum LineBreak {
        Unknown => icup::LineBreak::Unknown,
        Ambiguous => icup::LineBreak::Ambiguous,
        Alphabetic => icup::LineBreak::Alphabetic,
        BreakBoth => icup::LineBreak::BreakBoth,
        BreakAfter => icup::LineBreak::BreakAfter,
        BreakBefore => icup::LineBreak::BreakBefore,
        MandatoryBreak => icup::LineBreak::MandatoryBreak,
        ContingentBreak => icup::LineBreak::ContingentBreak,
        ClosePunctuation => icup::LineBreak::ClosePunctuation,
        CombiningMark => icup::LineBreak::CombiningMark,
        CarriageReturn => icup::LineBreak::CarriageReturn,
        Exclamation => icup::LineBreak::Exclamation,
        Glue => icup::LineBreak::Glue,
        Hyphen => icup::LineBreak::Hyphen,
        Ideographic => icup::LineBreak::Ideographic,
        InfixNumeric => icup::LineBreak::InfixNumeric,
        LineFeed => icup::LineBreak::LineFeed,
        Nonstarter => icup::LineBreak::Nonstarter,
        Numeric => icup::LineBreak::Numeric,
        OpenPunctuation => icup::LineBreak::OpenPunctuation,
        PostfixNumeric => icup::LineBreak::PostfixNumeric,
        PrefixNumeric => icup::LineBreak::PrefixNumeric,
        Quotation => icup::LineBreak::Quotation,
        ComplexContext => icup::LineBreak::ComplexContext,
        Surrogate => icup::LineBreak::Surrogate,
        Space => icup::LineBreak::Space,
        BreakSymbols => icup::LineBreak::BreakSymbols,
        ZWSpace => icup::LineBreak::ZWSpace,
        NextLine => icup::LineBreak::NextLine,
        WordJoiner => icup::LineBreak::WordJoiner,
        H2 => icup::LineBreak::H2,
        H3 => icup::LineBreak::H3,
        JL => icup::LineBreak::JL,
        JT => icup::LineBreak::JT,
        JV => icup::LineBreak::JV,
        CloseParenthesis => icup::LineBreak::CloseParenthesis,
        ConditionalJapaneseStarter => icup::LineBreak::ConditionalJapaneseStarter,
        HebrewLetter => icup::LineBreak::HebrewLetter,
        RegionalIndicator => icup::LineBreak::RegionalIndicator,
        EBase => icup::LineBreak::EBase,
        EModifier => icup::LineBreak::EModifier,
        ZWJ => icup::LineBreak::ZWJ,
        Aksara => icup::LineBreak::Aksara,
        AksaraPrebase => icup::LineBreak::AksaraPrebase,
        AksaraStart => icup::LineBreak::AksaraStart,
        ViramaFinal => icup::LineBreak::ViramaFinal,
        Virama => icup::LineBreak::Virama,
    } => maps::line_break(),
    default = Unknown
}

def_enum_prop! {
    enum Script {
        Adlam => icup::Script::Adlam,
        Ahom => icup::Script::Ahom,
        AnatolianHieroglyphs => icup::Script::AnatolianHieroglyphs,
        Arabic => icup::Script::Arabic,
        Armenian => icup::Script::Armenian,
        Avestan => icup::Script::Avestan,
        Balinese => icup::Script::Balinese,
        Bamum => icup::Script::Bamum,
        BassaVah => icup::Script::BassaVah,
        Batak => icup::Script::Batak,
        Bengali => icup::Script::Bengali,
        Bhaiksuki => icup::Script::Bhaiksuki,
        Bopomofo => icup::Script::Bopomofo,
        Brahmi => icup::Script::Brahmi,
        Braille => icup::Script::Braille,
        Buginese => icup::Script::Buginese,
        Buhid => icup::Script::Buhid,
        CanadianAboriginal => icup::Script::CanadianAboriginal,
        Carian => icup::Script::Carian,
        CaucasianAlbanian => icup::Script::CaucasianAlbanian,
        Chakma => icup::Script::Chakma,
        Cham => icup::Script::Cham,
        Cherokee => icup::Script::Cherokee,
        Chorasmian => icup::Script::Chorasmian,
        Common => icup::Script::Common,
        Coptic => icup::Script::Coptic,
        Cuneiform => icup::Script::Cuneiform,
        Cypriot => icup::Script::Cypriot,
        CyproMinoan => icup::Script::CyproMinoan,
        Cyrillic => icup::Script::Cyrillic,
        Deseret => icup::Script::Deseret,
        Devanagari => icup::Script::Devanagari,
        DivesAkuru => icup::Script::DivesAkuru,
        Dogra => icup::Script::Dogra,
        Duployan => icup::Script::Duployan,
        EgyptianHieroglyphs => icup::Script::EgyptianHieroglyphs,
        Elbasan => icup::Script::Elbasan,
        Elymaic => icup::Script::Elymaic,
        Ethiopian => icup::Script::Ethiopian,
        Georgian => icup::Script::Georgian,
        Glagolitic => icup::Script::Glagolitic,
        Gothic => icup::Script::Gothic,
        Grantha => icup::Script::Grantha,
        Greek => icup::Script::Greek,
        Gujarati => icup::Script::Gujarati,
        GunjalaGondi => icup::Script::GunjalaGondi,
        Gurmukhi => icup::Script::Gurmukhi,
        Han => icup::Script::Han,
        Hangul => icup::Script::Hangul,
        HanifiRohingya => icup::Script::HanifiRohingya,
        Hanunoo => icup::Script::Hanunoo,
        Hatran => icup::Script::Hatran,
        Hebrew => icup::Script::Hebrew,
        Hiragana => icup::Script::Hiragana,
        ImperialAramaic => icup::Script::ImperialAramaic,
        Inherited => icup::Script::Inherited,
        InscriptionalPahlavi => icup::Script::InscriptionalPahlavi,
        InscriptionalParthian => icup::Script::InscriptionalParthian,
        Javanese => icup::Script::Javanese,
        Kaithi => icup::Script::Kaithi,
        Kannada => icup::Script::Kannada,
        Katakana => icup::Script::Katakana,
        Kawi => icup::Script::Kawi,
        KayahLi => icup::Script::KayahLi,
        Kharoshthi => icup::Script::Kharoshthi,
        KhitanSmallScript => icup::Script::KhitanSmallScript,
        Khmer => icup::Script::Khmer,
        Khojki => icup::Script::Khojki,
        Khudawadi => icup::Script::Khudawadi,
        Lao => icup::Script::Lao,
        Latin => icup::Script::Latin,
        Lepcha => icup::Script::Lepcha,
        Limbu => icup::Script::Limbu,
        LinearA => icup::Script::LinearA,
        LinearB => icup::Script::LinearB,
        Lisu => icup::Script::Lisu,
        Lycian => icup::Script::Lycian,
        Lydian => icup::Script::Lydian,
        Mahajani => icup::Script::Mahajani,
        Makasar => icup::Script::Makasar,
        Malayalam => icup::Script::Malayalam,
        Mandaic => icup::Script::Mandaic,
        Manichaean => icup::Script::Manichaean,
        Marchen => icup::Script::Marchen,
        MasaramGondi => icup::Script::MasaramGondi,
        Medefaidrin => icup::Script::Medefaidrin,
        MeeteiMayek => icup::Script::MeeteiMayek,
        MendeKikakui => icup::Script::MendeKikakui,
        MeroiticCursive => icup::Script::MeroiticCursive,
        MeroiticHieroglyphs => icup::Script::MeroiticHieroglyphs,
        Miao => icup::Script::Miao,
        Modi => icup::Script::Modi,
        Mongolian => icup::Script::Mongolian,
        Mro => icup::Script::Mro,
        Multani => icup::Script::Multani,
        Myanmar => icup::Script::Myanmar,
        Nabataean => icup::Script::Nabataean,
        NagMundari => icup::Script::NagMundari,
        Nandinagari => icup::Script::Nandinagari,
        Nastaliq => icup::Script::Nastaliq,
        NewTaiLue => icup::Script::NewTaiLue,
        Newa => icup::Script::Newa,
        Nko => icup::Script::Nko,
        Nushu => icup::Script::Nushu,
        NyiakengPuachueHmong => icup::Script::NyiakengPuachueHmong,
        Ogham => icup::Script::Ogham,
        OlChiki => icup::Script::OlChiki,
        OldHungarian => icup::Script::OldHungarian,
        OldItalic => icup::Script::OldItalic,
        OldNorthArabian => icup::Script::OldNorthArabian,
        OldPermic => icup::Script::OldPermic,
        OldPersian => icup::Script::OldPersian,
        OldSouthArabian => icup::Script::OldSouthArabian,
        OldTurkic => icup::Script::OldTurkic,
        OldUyghur => icup::Script::OldUyghur,
        Oriya => icup::Script::Oriya,
        Osage => icup::Script::Osage,
        Osmanya => icup::Script::Osmanya,
        PahawhHmong => icup::Script::PahawhHmong,
        Palmyrene => icup::Script::Palmyrene,
        PauCinHau => icup::Script::PauCinHau,
        PhagsPa => icup::Script::PhagsPa,
        Phoenician => icup::Script::Phoenician,
        PsalterPahlavi => icup::Script::PsalterPahlavi,
        Rejang => icup::Script::Rejang,
        Runic => icup::Script::Runic,
        Samaritan => icup::Script::Samaritan,
        Saurashtra => icup::Script::Saurashtra,
        Sharada => icup::Script::Sharada,
        Shavian => icup::Script::Shavian,
        Siddham => icup::Script::Siddham,
        SignWriting => icup::Script::SignWriting,
        Sinhala => icup::Script::Sinhala,
        Sogdian => icup::Script::Sogdian,
        SoraSompeng => icup::Script::SoraSompeng,
        Soyombo => icup::Script::Soyombo,
        Sundanese => icup::Script::Sundanese,
        SylotiNagri => icup::Script::SylotiNagri,
        Syriac => icup::Script::Syriac,
        Tagalog => icup::Script::Tagalog,
        Tagbanwa => icup::Script::Tagbanwa,
        TaiLe => icup::Script::TaiLe,
        TaiTham => icup::Script::TaiTham,
        TaiViet => icup::Script::TaiViet,
        Takri => icup::Script::Takri,
        Tamil => icup::Script::Tamil,
        Tangsa => icup::Script::Tangsa,
        Tangut => icup::Script::Tangut,
        Telugu => icup::Script::Telugu,
        Thaana => icup::Script::Thaana,
        Thai => icup::Script::Thai,
        Tibetan => icup::Script::Tibetan,
        Tifinagh => icup::Script::Tifinagh,
        Tirhuta => icup::Script::Tirhuta,
        Toto => icup::Script::Toto,
        Ugaritic => icup::Script::Ugaritic,
        Unknown => icup::Script::Unknown,
        Vai => icup::Script::Vai,
        Vithkuqi => icup::Script::Vithkuqi,
        Wancho => icup::Script::Wancho,
        WarangCiti => icup::Script::WarangCiti,
        Yezidi => icup::Script::Yezidi,
        Yi => icup::Script::Yi,
        ZanabazarSquare => icup::Script::ZanabazarSquare,
    } => maps::script(),
    default = Unknown
}

def_enum_prop! {
    enum SentenceBreak {
        Other => icup::SentenceBreak::Other,
        ATerm => icup::SentenceBreak::ATerm,
        Close => icup::SentenceBreak::Close,
        Format => icup::SentenceBreak::Format,
        Lower => icup::SentenceBreak::Lower,
        Numeric => icup::SentenceBreak::Numeric,
        OLetter => icup::SentenceBreak::OLetter,
        Sep => icup::SentenceBreak::Sep,
        Sp => icup::SentenceBreak::Sp,
        STerm => icup::SentenceBreak::STerm,
        Upper => icup::SentenceBreak::Upper,
        CR => icup::SentenceBreak::CR,
        Extend => icup::SentenceBreak::Extend,
        LF => icup::SentenceBreak::LF,
        SContinue => icup::SentenceBreak::SContinue,
    } => maps::sentence_break(),
    default = Other
}

def_enum_prop! {
    enum WordBreak {
        Other => icup::WordBreak::Other,
        ALetter => icup::WordBreak::ALetter,
        Format => icup::WordBreak::Format,
        Katakana => icup::WordBreak::Katakana,
        MidLetter => icup::WordBreak::MidLetter,
        MidNum => icup::WordBreak::MidNum,
        Numeric => icup::WordBreak::Numeric,
        ExtendNumLet => icup::WordBreak::ExtendNumLet,
        CR => icup::WordBreak::CR,
        Extend => icup::WordBreak::Extend,
        LF => icup::WordBreak::LF,
        MidNumLet => icup::WordBreak::MidNumLet,
        Newline => icup::WordBreak::Newline,
        RegionalIndicator => icup::WordBreak::RegionalIndicator,
        HebrewLetter => icup::WordBreak::HebrewLetter,
        SingleQuote => icup::WordBreak::SingleQuote,
        DoubleQuote => icup::WordBreak::DoubleQuote,
        EBase => icup::WordBreak::EBase,
        EBaseGAZ => icup::WordBreak::EBaseGAZ,
        EModifier => icup::WordBreak::EModifier,
        GlueAfterZwj => icup::WordBreak::GlueAfterZwj,
        ZWJ => icup::WordBreak::ZWJ,
        WSegSpace => icup::WordBreak::WSegSpace,
    } => maps::word_break(),
    default = Other
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IndicConjunctBreak {
    None,
    Linker,
    Consonant,
    Extend,
}

impl IndicConjunctBreak {
    /// Gets the property value of a code point.
    pub fn of(ch: char) -> Self {
        if let Script::Bengali
        | Script::Devanagari
        | Script::Gujarati
        | Script::Malayalam
        | Script::Oriya
        | Script::Telugu = Script::of(ch)
        {
            match IndicSyllabicCategory::of(ch) {
                IndicSyllabicCategory::Virama => Self::Linker,
                IndicSyllabicCategory::Consonant => Self::Consonant,
                _ => Self::None,
            }
        } else if let GraphemeClusterBreak::ZWJ | GraphemeClusterBreak::Extend =
            GraphemeClusterBreak::of(ch)
        {
            if ch != '\u{200c}' {
                Self::Extend
            } else {
                Self::None
            }
        } else {
            Self::None
        }
    }
}

impl Property for IndicConjunctBreak {
    fn contains(self, ch: char) -> bool {
        self == Self::of(ch)
    }
}

impl core::ops::Not for IndicConjunctBreak {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for IndicConjunctBreak {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for IndicConjunctBreak {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}
