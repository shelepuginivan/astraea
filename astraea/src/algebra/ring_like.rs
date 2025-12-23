use crate::algebra::{
    AddAssociative, AddClosed, AddCommutative, AddInvertible, AddWithIdentity, Distributive,
    MulAssociative, MulClosed, MulCommutative, MulInvertible, MulWithIdentity,
};

use super::class_inclusion::inclusion_chain;

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
/// 3. Multiplication distributes over addition.
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

/// Ring is an algebraic structure, where
///
/// 1. Addition is an **abelian group**: closed, associative, with identity, invertible,
///    commutative.
/// 2. Multiplication is a **monoid**: closed, associative, with identity.
/// 3. Multiplication distributes over addition.
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

/// CommutativeRing is an algebraic structure, where
///
/// 1. Addition is an **abelian group**: closed, associative, with identity, invertible,
///    commutative.
/// 2. Multiplication is a **commutative monoid**: closed, associative, with identity, commutative.
/// 3. Multiplication distributes over addition.
///
/// Commutative ring is a ring with commutative multiplication.
pub trait CommutativeRing:
    AddClosed
    + AddAssociative<Self>
    + AddWithIdentity<Self>
    + AddInvertible<Self>
    + AddCommutative<Self>
    + MulClosed
    + MulAssociative<Self>
    + MulWithIdentity<Self>
    + MulCommutative<Self>
    + Distributive
{
}

/// Field is an algebraic structure, where
///
/// 1. Addition is an **abelian group**: closed, associative, with identity, invertible,
///    commutative.
/// 2. Multiplication is an **abelian group**: closed, associative, with identity, invertible,
///    commutative.
/// 3. Multiplication distributes over addition.
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

// Semiring ⊃ Ring
inclusion_chain!(Semiring, Ring);

// Rng ⊃ Ring
inclusion_chain!(Rng, Ring);

// Ring ⊃ CommutativeRing ⊃ Field
inclusion_chain!(Ring, CommutativeRing, Field);
