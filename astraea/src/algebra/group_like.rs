use crate::algebra::{
    AddAssociative, AddClosed, AddCommutative, AddInvertible, AddWithIdentity, MulAssociative,
    MulClosed, MulCommutative, MulInvertible, MulWithIdentity,
};

/// Magma under addition.
pub trait AddMagma: AddClosed {}

/// Semigroup under addition.
pub trait AddSemigroup: AddClosed + AddAssociative<Self> {}

/// Monoid under addition.
pub trait AddMonoid: AddClosed + AddAssociative<Self> + AddWithIdentity<Self> {}

/// Quasigroup under addition.
pub trait AddQuasigroup: AddClosed + AddInvertible<Self> {}

/// Loop under addition.
pub trait AddLoop: AddClosed + AddInvertible<Self> + AddWithIdentity<Self> {}

/// Group under addition.
pub trait AddGroup:
    AddClosed + AddAssociative<Self> + AddWithIdentity<Self> + AddInvertible<Self>
{
}

/// Abelian group under addition.
pub trait AddAbelianGroup:
    AddClosed
    + AddAssociative<Self>
    + AddWithIdentity<Self>
    + AddInvertible<Self>
    + AddCommutative<Self>
{
}

/// Magma under multiplication.
pub trait MulMagma: MulClosed {}

/// Semigroup under multiplication.
pub trait MulSemigroup: MulClosed + MulAssociative<Self> {}

/// Monoid under multiplication.
pub trait MulMonoid: MulClosed + MulAssociative<Self> + MulWithIdentity<Self> {}

/// Quasigroup under multiplication.
pub trait MulQuasigroup: MulInvertible<Self> + MulClosed {}

/// Loop under multiplication.
pub trait MulLoop: MulClosed + MulInvertible<Self> + MulWithIdentity<Self> {}

/// Group under multiplication.
pub trait MulGroup:
    MulClosed + MulAssociative<Self> + MulWithIdentity<Self> + MulInvertible<Self>
{
}

/// Abelian group under multiplication.
pub trait MulAbelianGroup:
    MulClosed
    + MulAssociative<Self>
    + MulWithIdentity<Self>
    + MulInvertible<Self>
    + MulCommutative<Self>
{
}
