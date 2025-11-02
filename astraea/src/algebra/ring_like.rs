use crate::algebra::{
    AddAssociative, AddClosed, AddCommutative, AddWithIdentity, AddInvertible, Distributive,
    MulAssociative, MulClosed, MulCommutative, MulWithIdentity, MulInvertible,
};

/// Semiring is an algebraic structure, where
///
/// 1. Addition is a **commutative monoid**: closed, associative, with identity, commutative.
/// 2. Multiplication is a **monoid**: closed, associative, with identity.
/// 3. Multiplication distributes over addition
///
/// Semiring is a ring without additive inverses.
pub trait Semiring:
    AddClosed
    + AddAssociative<Self>
    + AddWithIdentity<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + MulWithIdentity<Self>
    + Distributive
{
}

/// Rng is an algebraic structure, where
///
/// 1. Addition is an **abelian group**: closed, associative, with identity, invertible,
///    commutative.
/// 2. Multiplication is a **semigroup**: closed, associative.
/// 3. Multiplication distributes over addition
///
/// Rng is a ring without multiplicative identity.
pub trait Rng:
    AddClosed
    + AddAssociative<Self>
    + AddWithIdentity<Self>
    + AddInvertible<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + Distributive
{
}

/// Rng is an algebraic structure, where
///
/// 1. Addition is an **abelian group**: closed, associative, with identity, invertible,
///    commutative.
/// 2. Multiplication is a **monoid**: closed, associative, with identity.
/// 3. Multiplication distributes over addition
pub trait Ring:
    AddClosed
    + AddAssociative<Self>
    + AddWithIdentity<Self>
    + AddInvertible<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + MulWithIdentity<Self>
    + Distributive
{
}

/// Field is an algebraic structure, where
///
/// 1. Addition is an **abelian group**: closed, associative, with identity, invertible,
///    commutative.
/// 2. Multiplication is an **abelian group**: closed, associative, with identity, invertible,
///    commutative.
/// 3. Multiplication distributes over addition
pub trait Field:
    AddClosed
    + AddAssociative<Self>
    + AddWithIdentity<Self>
    + AddInvertible<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + MulWithIdentity<Self>
    + MulInvertible<Self>
    + MulCommutative<Self>
    + Distributive
{
}
