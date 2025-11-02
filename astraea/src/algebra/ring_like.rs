use crate::algebra::{
    AddAssociative, AddClosed, AddCommutative, AddIdentity, AddInversion, Distributive,
    MulAssociative, MulClosed, MulCommutative, MulIdentity, MulInversion,
};

/// A Semiring is an algebraic structure consisting of a set equipped with two binary operations:
/// addition and multiplication, where addition is associative and commutative with an identity element,
/// multiplication is associative with an identity element, and multiplication distributes over addition.
///
/// Unlike rings, semirings do not require additive inverses.
pub trait Semiring:
    AddClosed
    + AddAssociative<Self>
    + AddIdentity<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + Distributive
{
}

pub trait Rng:
    AddClosed
    + AddAssociative<Self>
    + AddIdentity<Self>
    + AddInversion<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + Distributive
{
}

/// A Ring is an algebraic structure in which addition (subtraction) and multiplication are defined
/// and satisfy the ring axioms.
pub trait Ring:
    AddClosed
    + AddAssociative<Self>
    + AddIdentity<Self>
    + AddInversion<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + MulIdentity<Self>
    + Distributive
{
}

/// A Field is an algebraic structure in which addition (subtraction), multiplication,
/// and division (except by zero) are defined and satisfy the field axioms.
pub trait Field:
    AddClosed
    + AddAssociative<Self>
    + AddIdentity<Self>
    + AddInversion<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + MulIdentity<Self>
    + MulInversion<Self>
    + MulCommutative<Self>
    + Distributive
{
}

