//! Unicode property definitions and combinators.

use super::Property;
#[allow(unused_imports)]
use icu_properties::props::{self as icup, BinaryProperty, EnumeratedProperty};

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
    ($(#[$($attr:tt)*])* $ty:ident => $prop:ty) => {
        $(#[$($attr)*])*
        #[derive(Debug, Clone, Copy)]
        pub struct $ty;

        impl Property for $ty {
            fn contains(self, ch: char) -> bool {
                <$prop as BinaryProperty>::for_char(ch)
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

def_bool_prop!(Alphabetic => icup::Alphabetic);
def_bool_prop!(AsciiHexDigit => icup::AsciiHexDigit);
def_bool_prop!(BidiControl => icup::BidiControl);
def_bool_prop!(BidiMirrored => icup::BidiMirrored);
def_bool_prop!(CaseIgnorable => icup::CaseIgnorable);
def_bool_prop!(Cased => icup::Cased);
def_bool_prop!(ChangesWhenCasefolded => icup::ChangesWhenCasefolded);
def_bool_prop!(ChangesWhenCasemapped => icup::ChangesWhenCasemapped);
def_bool_prop!(ChangesWhenLowercased => icup::ChangesWhenLowercased);
def_bool_prop!(ChangesWhenNfkcCasefolded => icup::ChangesWhenNfkcCasefolded);
def_bool_prop!(ChangesWhenTitlecased => icup::ChangesWhenTitlecased);
def_bool_prop!(ChangesWhenUppercased => icup::ChangesWhenUppercased);
def_bool_prop!(Dash => icup::Dash);
def_bool_prop!(DefaultIgnorableCodePoint => icup::DefaultIgnorableCodePoint);
def_bool_prop!(Deprecated => icup::Deprecated);
def_bool_prop!(Diacritic => icup::Diacritic);
def_bool_prop!(Emoji => icup::Emoji);
def_bool_prop!(EmojiComponent => icup::EmojiComponent);
def_bool_prop!(EmojiModifier => icup::EmojiModifier);
def_bool_prop!(EmojiModifierBase => icup::EmojiModifierBase);
def_bool_prop!(EmojiPresentation => icup::EmojiPresentation);
def_bool_prop!(ExtendedPictographic => icup::ExtendedPictographic);
def_bool_prop!(Extender => icup::Extender);
def_bool_prop!(FullCompositionExclusion => icup::FullCompositionExclusion);
def_bool_prop!(GraphemeBase => icup::GraphemeBase);
def_bool_prop!(GraphemeExtend => icup::GraphemeExtend);
def_bool_prop!(GraphemeLink => icup::GraphemeLink);
def_bool_prop!(HexDigit => icup::HexDigit);
def_bool_prop!(Hyphen => icup::Hyphen);
def_bool_prop!(IdContinue => icup::IdContinue);
def_bool_prop!(IdStart => icup::IdStart);
def_bool_prop!(Ideographic => icup::Ideographic);
def_bool_prop!(IdsBinaryOperator => icup::IdsBinaryOperator);
def_bool_prop!(IdsTrinaryOperator => icup::IdsTrinaryOperator);
def_bool_prop!(JoinControl => icup::JoinControl);
def_bool_prop!(LogicalOrderException => icup::LogicalOrderException);
def_bool_prop!(Lowercase => icup::Lowercase);
def_bool_prop!(Math => icup::Math);
def_bool_prop!(NoncharacterCodePoint => icup::NoncharacterCodePoint);
def_bool_prop!(PatternSyntax => icup::PatternSyntax);
def_bool_prop!(PatternWhiteSpace => icup::PatternWhiteSpace);
def_bool_prop!(PrependedConcatenationMark => icup::PrependedConcatenationMark);
def_bool_prop!(QuotationMark => icup::QuotationMark);
def_bool_prop!(Radical => icup::Radical);
def_bool_prop!(RegionalIndicator => icup::RegionalIndicator);
def_bool_prop!(SentenceTerminal => icup::SentenceTerminal);
def_bool_prop!(SoftDotted => icup::SoftDotted);
def_bool_prop!(TerminalPunctuation => icup::TerminalPunctuation);
def_bool_prop!(UnifiedIdeograph => icup::UnifiedIdeograph);
def_bool_prop!(Uppercase => icup::Uppercase);
def_bool_prop!(VariationSelector => icup::VariationSelector);
def_bool_prop!(WhiteSpace => icup::WhiteSpace);
def_bool_prop!(XidContinue => icup::XidContinue);
def_bool_prop!(XidStart => icup::XidStart);

macro_rules! def_enum_prop {
    ($(#[$($attr:tt)*])* enum $name:ident { $($(#[$($vattr:tt)*])* $var:ident => $val:ident),* $(,)* } => $prop:ty , default = $dvar:ident) => {
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
                match <$prop as EnumeratedProperty>::for_char(ch) {
                    $(
                        <$prop>::$val => Self::$var,
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
        LeftToRight => LeftToRight,
        RightToLeft => RightToLeft,
        EuropeanNumber => EuropeanNumber,
        EuropeanSeparator => EuropeanSeparator,
        EuropeanTerminator => EuropeanTerminator,
        ArabicNumber => ArabicNumber,
        CommonSeparator => CommonSeparator,
        ParagraphSeparator => ParagraphSeparator,
        SegmentSeparator => SegmentSeparator,
        WhiteSpace => WhiteSpace,
        OtherNeutral => OtherNeutral,
        LeftToRightEmbedding => LeftToRightEmbedding,
        LeftToRightOverride => LeftToRightOverride,
        ArabicLetter => ArabicLetter,
        RightToLeftEmbedding => RightToLeftEmbedding,
        RightToLeftOverride => RightToLeftOverride,
        PopDirectionalFormat => PopDirectionalFormat,
        NonspacingMark => NonspacingMark,
        BoundaryNeutral => BoundaryNeutral,
        FirstStrongIsolate => FirstStrongIsolate,
        LeftToRightIsolate => LeftToRightIsolate,
        RightToLeftIsolate => RightToLeftIsolate,
        PopDirectionalIsolate => PopDirectionalIsolate,
    } => icup::BidiClass,
    default = LeftToRight
}

def_enum_prop! {
    enum CanonicalCombiningClass {
        NotReordered => NotReordered,
        Overlay => Overlay,
        HanReading => HanReading,
        Nukta => Nukta,
        KanaVoicing => KanaVoicing,
        Virama => Virama,
        CCC10 => CCC10,
        CCC11 => CCC11,
        CCC12 => CCC12,
        CCC13 => CCC13,
        CCC14 => CCC14,
        CCC15 => CCC15,
        CCC16 => CCC16,
        CCC17 => CCC17,
        CCC18 => CCC18,
        CCC19 => CCC19,
        CCC20 => CCC20,
        CCC21 => CCC21,
        CCC22 => CCC22,
        CCC23 => CCC23,
        CCC24 => CCC24,
        CCC25 => CCC25,
        CCC26 => CCC26,
        CCC27 => CCC27,
        CCC28 => CCC28,
        CCC29 => CCC29,
        CCC30 => CCC30,
        CCC31 => CCC31,
        CCC32 => CCC32,
        CCC33 => CCC33,
        CCC34 => CCC34,
        CCC35 => CCC35,
        CCC36 => CCC36,
        CCC84 => CCC84,
        CCC91 => CCC91,
        CCC103 => CCC103,
        CCC107 => CCC107,
        CCC118 => CCC118,
        CCC122 => CCC122,
        CCC129 => CCC129,
        CCC130 => CCC130,
        CCC132 => CCC132,
        AttachedBelowLeft => AttachedBelowLeft,
        AttachedBelow => AttachedBelow,
        AttachedAbove => AttachedAbove,
        AttachedAboveRight => AttachedAboveRight,
        BelowLeft => BelowLeft,
        Below => Below,
        BelowRight => BelowRight,
        Left => Left,
        Right => Right,
        AboveLeft => AboveLeft,
        Above => Above,
        AboveRight => AboveRight,
        DoubleBelow => DoubleBelow,
        DoubleAbove => DoubleAbove,
        IotaSubscript => IotaSubscript,
    } => icup::CanonicalCombiningClass,
    default = NotReordered
}

def_enum_prop! {
    enum EastAsianWidth {
        Neutral => Neutral,
        Ambiguous => Ambiguous,
        Halfwidth => Halfwidth,
        Fullwidth => Fullwidth,
        Narrow => Narrow,
        Wide => Wide,
    } => icup::EastAsianWidth,
    default = Neutral
}

def_enum_prop! {
    enum GeneralCategory {
        Unassigned => Unassigned,
        UppercaseLetter => UppercaseLetter,
        LowercaseLetter => LowercaseLetter,
        TitlecaseLetter => TitlecaseLetter,
        ModifierLetter => ModifierLetter,
        OtherLetter => OtherLetter,
        NonspacingMark => NonspacingMark,
        SpacingMark => SpacingMark,
        EnclosingMark => EnclosingMark,
        DecimalNumber => DecimalNumber,
        LetterNumber => LetterNumber,
        OtherNumber => OtherNumber,
        SpaceSeparator => SpaceSeparator,
        LineSeparator => LineSeparator,
        ParagraphSeparator => ParagraphSeparator,
        Control => Control,
        Format => Format,
        PrivateUse => PrivateUse,
        Surrogate => Surrogate,
        DashPunctuation => DashPunctuation,
        OpenPunctuation => OpenPunctuation,
        ClosePunctuation => ClosePunctuation,
        ConnectorPunctuation => ConnectorPunctuation,
        InitialPunctuation => InitialPunctuation,
        FinalPunctuation => FinalPunctuation,
        OtherPunctuation => OtherPunctuation,
        MathSymbol => MathSymbol,
        CurrencySymbol => CurrencySymbol,
        ModifierSymbol => ModifierSymbol,
        OtherSymbol => OtherSymbol,
    } => icup::GeneralCategory,
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
        Other => Other,
        Control => Control,
        CR => CR,
        Extend => Extend,
        L => L,
        LF => LF,
        LV => LV,
        LVT => LVT,
        T => T,
        V => V,
        SpacingMark => SpacingMark,
        Prepend => Prepend,
        RegionalIndicator => RegionalIndicator,
        EBase => EBase,
        EBaseGAZ => EBaseGAZ,
        EModifier => EModifier,
        GlueAfterZwj => GlueAfterZwj,
        ZWJ => ZWJ,
    } => icup::GraphemeClusterBreak,
    default = Other
}

def_enum_prop! {
    enum HangulSyllableType {
        NotApplicable => NotApplicable,
        VowelJamo => VowelJamo,
        TrailingJamo => TrailingJamo,
        LeadingVowelSyllable => LeadingVowelSyllable,
        LeadingVowelTrailingSyllable => LeadingVowelTrailingSyllable,
    } => icup::HangulSyllableType,
    default = NotApplicable
}

def_enum_prop! {
    enum IndicSyllabicCategory {
        Other => Other,
        Avagraha => Avagraha,
        Bindu => Bindu,
        BrahmiJoiningNumber => BrahmiJoiningNumber,
        CantillationMark => CantillationMark,
        Consonant => Consonant,
        ConsonantDead => ConsonantDead,
        ConsonantFinal => ConsonantFinal,
        ConsonantHeadLetter => ConsonantHeadLetter,
        ConsonantInitialPostfixed => ConsonantInitialPostfixed,
        ConsonantKiller => ConsonantKiller,
        ConsonantMedial => ConsonantMedial,
        ConsonantPlaceholder => ConsonantPlaceholder,
        ConsonantPrecedingRepha => ConsonantPrecedingRepha,
        ConsonantPrefixed => ConsonantPrefixed,
        ConsonantSucceedingRepha => ConsonantSucceedingRepha,
        ConsonantSubjoined => ConsonantSubjoined,
        ConsonantWithStacker => ConsonantWithStacker,
        GeminationMark => GeminationMark,
        InvisibleStacker => InvisibleStacker,
        Joiner => Joiner,
        ModifyingLetter => ModifyingLetter,
        NonJoiner => NonJoiner,
        Nukta => Nukta,
        Number => Number,
        NumberJoiner => NumberJoiner,
        PureKiller => PureKiller,
        RegisterShifter => RegisterShifter,
        SyllableModifier => SyllableModifier,
        ToneLetter => ToneLetter,
        ToneMark => ToneMark,
        Virama => Virama,
        Visarga => Visarga,
        Vowel => Vowel,
        VowelDependent => VowelDependent,
        VowelIndependent => VowelIndependent,
    } => icup::IndicSyllabicCategory,
    default = Other
}

def_enum_prop! {
    enum JoiningType {
        NonJoining => NonJoining,
        JoinCausing => JoinCausing,
        DualJoining => DualJoining,
        LeftJoining => LeftJoining,
        RightJoining => RightJoining,
        Transparent => Transparent,
    } => icup::JoiningType,
    default = NonJoining
}

def_enum_prop! {
    enum LineBreak {
        Unknown => Unknown,
        Ambiguous => Ambiguous,
        Alphabetic => Alphabetic,
        BreakBoth => BreakBoth,
        BreakAfter => BreakAfter,
        BreakBefore => BreakBefore,
        MandatoryBreak => MandatoryBreak,
        ContingentBreak => ContingentBreak,
        ClosePunctuation => ClosePunctuation,
        CombiningMark => CombiningMark,
        CarriageReturn => CarriageReturn,
        Exclamation => Exclamation,
        Glue => Glue,
        Hyphen => Hyphen,
        Ideographic => Ideographic,
        InfixNumeric => InfixNumeric,
        LineFeed => LineFeed,
        Nonstarter => Nonstarter,
        Numeric => Numeric,
        OpenPunctuation => OpenPunctuation,
        PostfixNumeric => PostfixNumeric,
        PrefixNumeric => PrefixNumeric,
        Quotation => Quotation,
        ComplexContext => ComplexContext,
        Surrogate => Surrogate,
        Space => Space,
        BreakSymbols => BreakSymbols,
        ZWSpace => ZWSpace,
        NextLine => NextLine,
        WordJoiner => WordJoiner,
        H2 => H2,
        H3 => H3,
        JL => JL,
        JT => JT,
        JV => JV,
        CloseParenthesis => CloseParenthesis,
        ConditionalJapaneseStarter => ConditionalJapaneseStarter,
        HebrewLetter => HebrewLetter,
        RegionalIndicator => RegionalIndicator,
        EBase => EBase,
        EModifier => EModifier,
        ZWJ => ZWJ,
        Aksara => Aksara,
        AksaraPrebase => AksaraPrebase,
        AksaraStart => AksaraStart,
        ViramaFinal => ViramaFinal,
        Virama => Virama,
    } => icup::LineBreak,
    default = Unknown
}

def_enum_prop! {
    enum Script {
        Adlam => Adlam,
        Ahom => Ahom,
        AnatolianHieroglyphs => AnatolianHieroglyphs,
        Arabic => Arabic,
        Armenian => Armenian,
        Avestan => Avestan,
        Balinese => Balinese,
        Bamum => Bamum,
        BassaVah => BassaVah,
        Batak => Batak,
        Bengali => Bengali,
        Bhaiksuki => Bhaiksuki,
        Bopomofo => Bopomofo,
        Brahmi => Brahmi,
        Braille => Braille,
        Buginese => Buginese,
        Buhid => Buhid,
        CanadianAboriginal => CanadianAboriginal,
        Carian => Carian,
        CaucasianAlbanian => CaucasianAlbanian,
        Chakma => Chakma,
        Cham => Cham,
        Cherokee => Cherokee,
        Chorasmian => Chorasmian,
        Common => Common,
        Coptic => Coptic,
        Cuneiform => Cuneiform,
        Cypriot => Cypriot,
        CyproMinoan => CyproMinoan,
        Cyrillic => Cyrillic,
        Deseret => Deseret,
        Devanagari => Devanagari,
        DivesAkuru => DivesAkuru,
        Dogra => Dogra,
        Duployan => Duployan,
        EgyptianHieroglyphs => EgyptianHieroglyphs,
        Elbasan => Elbasan,
        Elymaic => Elymaic,
        Ethiopian => Ethiopian,
        Georgian => Georgian,
        Glagolitic => Glagolitic,
        Gothic => Gothic,
        Grantha => Grantha,
        Greek => Greek,
        Gujarati => Gujarati,
        GunjalaGondi => GunjalaGondi,
        Gurmukhi => Gurmukhi,
        Han => Han,
        Hangul => Hangul,
        HanifiRohingya => HanifiRohingya,
        Hanunoo => Hanunoo,
        Hatran => Hatran,
        Hebrew => Hebrew,
        Hiragana => Hiragana,
        ImperialAramaic => ImperialAramaic,
        Inherited => Inherited,
        InscriptionalPahlavi => InscriptionalPahlavi,
        InscriptionalParthian => InscriptionalParthian,
        Javanese => Javanese,
        Kaithi => Kaithi,
        Kannada => Kannada,
        Katakana => Katakana,
        Kawi => Kawi,
        KayahLi => KayahLi,
        Kharoshthi => Kharoshthi,
        KhitanSmallScript => KhitanSmallScript,
        Khmer => Khmer,
        Khojki => Khojki,
        Khudawadi => Khudawadi,
        Lao => Lao,
        Latin => Latin,
        Lepcha => Lepcha,
        Limbu => Limbu,
        LinearA => LinearA,
        LinearB => LinearB,
        Lisu => Lisu,
        Lycian => Lycian,
        Lydian => Lydian,
        Mahajani => Mahajani,
        Makasar => Makasar,
        Malayalam => Malayalam,
        Mandaic => Mandaic,
        Manichaean => Manichaean,
        Marchen => Marchen,
        MasaramGondi => MasaramGondi,
        Medefaidrin => Medefaidrin,
        MeeteiMayek => MeeteiMayek,
        MendeKikakui => MendeKikakui,
        MeroiticCursive => MeroiticCursive,
        MeroiticHieroglyphs => MeroiticHieroglyphs,
        Miao => Miao,
        Modi => Modi,
        Mongolian => Mongolian,
        Mro => Mro,
        Multani => Multani,
        Myanmar => Myanmar,
        Nabataean => Nabataean,
        NagMundari => NagMundari,
        Nandinagari => Nandinagari,
        Nastaliq => Nastaliq,
        NewTaiLue => NewTaiLue,
        Newa => Newa,
        Nko => Nko,
        Nushu => Nushu,
        NyiakengPuachueHmong => NyiakengPuachueHmong,
        Ogham => Ogham,
        OlChiki => OlChiki,
        OldHungarian => OldHungarian,
        OldItalic => OldItalic,
        OldNorthArabian => OldNorthArabian,
        OldPermic => OldPermic,
        OldPersian => OldPersian,
        OldSouthArabian => OldSouthArabian,
        OldTurkic => OldTurkic,
        OldUyghur => OldUyghur,
        Oriya => Oriya,
        Osage => Osage,
        Osmanya => Osmanya,
        PahawhHmong => PahawhHmong,
        Palmyrene => Palmyrene,
        PauCinHau => PauCinHau,
        PhagsPa => PhagsPa,
        Phoenician => Phoenician,
        PsalterPahlavi => PsalterPahlavi,
        Rejang => Rejang,
        Runic => Runic,
        Samaritan => Samaritan,
        Saurashtra => Saurashtra,
        Sharada => Sharada,
        Shavian => Shavian,
        Siddham => Siddham,
        SignWriting => SignWriting,
        Sinhala => Sinhala,
        Sogdian => Sogdian,
        SoraSompeng => SoraSompeng,
        Soyombo => Soyombo,
        Sundanese => Sundanese,
        SylotiNagri => SylotiNagri,
        Syriac => Syriac,
        Tagalog => Tagalog,
        Tagbanwa => Tagbanwa,
        TaiLe => TaiLe,
        TaiTham => TaiTham,
        TaiViet => TaiViet,
        Takri => Takri,
        Tamil => Tamil,
        Tangsa => Tangsa,
        Tangut => Tangut,
        Telugu => Telugu,
        Thaana => Thaana,
        Thai => Thai,
        Tibetan => Tibetan,
        Tifinagh => Tifinagh,
        Tirhuta => Tirhuta,
        Toto => Toto,
        Ugaritic => Ugaritic,
        Unknown => Unknown,
        Vai => Vai,
        Vithkuqi => Vithkuqi,
        Wancho => Wancho,
        WarangCiti => WarangCiti,
        Yezidi => Yezidi,
        Yi => Yi,
        ZanabazarSquare => ZanabazarSquare,
    } => icup::Script,
    default = Unknown
}

def_enum_prop! {
    enum SentenceBreak {
        Other => Other,
        ATerm => ATerm,
        Close => Close,
        Format => Format,
        Lower => Lower,
        Numeric => Numeric,
        OLetter => OLetter,
        Sep => Sep,
        Sp => Sp,
        STerm => STerm,
        Upper => Upper,
        CR => CR,
        Extend => Extend,
        LF => LF,
        SContinue => SContinue,
    } => icup::SentenceBreak,
    default = Other
}

def_enum_prop! {
    enum WordBreak {
        Other => Other,
        ALetter => ALetter,
        Format => Format,
        Katakana => Katakana,
        MidLetter => MidLetter,
        MidNum => MidNum,
        Numeric => Numeric,
        ExtendNumLet => ExtendNumLet,
        CR => CR,
        Extend => Extend,
        LF => LF,
        MidNumLet => MidNumLet,
        Newline => Newline,
        RegionalIndicator => RegionalIndicator,
        HebrewLetter => HebrewLetter,
        SingleQuote => SingleQuote,
        DoubleQuote => DoubleQuote,
        EBase => EBase,
        EBaseGAZ => EBaseGAZ,
        EModifier => EModifier,
        GlueAfterZwj => GlueAfterZwj,
        ZWJ => ZWJ,
        WSegSpace => WSegSpace,
    } => icup::WordBreak,
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
