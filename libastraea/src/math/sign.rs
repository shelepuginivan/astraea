use std::{cmp::Ordering, fmt::Display};

/// Sign represents sign of the number.
#[derive(Debug, Eq, PartialEq)]
pub enum Sign {
    Negative,
    Zero,
    Positive,
}

impl Sign {
    /// Returns integer representation of Sign (-1 for Negative, 1 for Positive, 0 otherwise).
    pub fn value(&self) -> i32 {
        match self {
            Self::Negative => -1,
            Self::Zero => 0,
            Self::Positive => 1,
        }
    }

    /// Converts std::cmp::Ordering to Sign.
    pub fn from_ordering(o: &Ordering) -> Self {
        match o {
            Ordering::Less => Self::Negative,
            Ordering::Equal => Self::Zero,
            Ordering::Greater => Self::Positive,
        }
    }
}

impl Display for Sign {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value())
    }
}

pub trait ToSign {
    fn to_sign(&self) -> Sign;
}

impl ToSign for Ordering {
    fn to_sign(&self) -> Sign {
        Sign::from_ordering(self)
    }
}
