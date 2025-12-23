use proc_macro::TokenStream;
use quote::quote;
use syn::{DeriveInput, parse_macro_input};

extern crate proc_macro;

/// Derive macro generating an impl of the `MathObject` trait.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`Sized`]
/// - [`Clone`]
/// - [`std::str::FromStr<Err: Debug>`]
#[proc_macro_derive(MathObject)]
pub fn derive_math_object(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    quote! {
        impl astraea::algebra::MathObject for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `AddMagma` trait.
///
/// Marks this type as a magma under addition, generating implementations for the following traits:
///
/// - `AddClosed`
/// - `AddMagma`
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
#[proc_macro_derive(AddMagma)]
pub fn derive_add_magma(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}

        impl astraea::algebra::AddMagma for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `AddSemigroup` trait.
///
/// Marks this type as a semigroup under addition, generating implementations for the following
/// traits:
///
/// - `AddClosed`
/// - `AddAssociative<Self>`
/// - `AddMagma`
/// - `AddSemigroup`
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - Associative --- `a + (b + c) = (a + b) + c`.
#[proc_macro_derive(AddSemigroup)]
pub fn derive_add_semigroup(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddAssociative<Self> for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddSemigroup for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `AddQuasigroup` trait.
///
/// Marks this type as a quasigroup under addition, generating implementations for the following
/// traits:
///
/// - `AddClosed`
/// - `AddInvertible<Self>`
/// - `AddMagma`
/// - `AddQuasigroup`
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
/// - [`std::ops::Neg`]
/// - [`std::ops::Sub`]
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - Invertible --- for all `a` there exists `-a`, such that `a + (-a) = 0`.
#[proc_macro_derive(AddQuasigroup)]
pub fn derive_add_quasigroup(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddInvertible<Self> for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `AddUnitalMagma` trait.
///
/// Marks this type as a unital magma under addition, generating implementations for the following
/// traits:
///
/// - `AddClosed`
/// - `AddMagma`
/// - `AddUnitalMagma`
///
/// `AddWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
/// - `AddWithIdentity<Self>`
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - With identity --- there exists `e = 0`, such that `a + e = a`.
#[proc_macro_derive(AddUnitalMagma)]
pub fn derive_add_unital_magma(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddUnitalMagma for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `AddMonoid` trait.
///
/// Marks this type as a monoid under addition, generating implementations for the following
/// traits:
///
/// - `AddClosed`
/// - `AddAssociative<Self>`
/// - `AddMagma`
/// - `AddSemigroup`
/// - `AddUnitalMagma`
/// - `AddMonoid`
///
/// `AddWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
/// - `AddWithIdentity<Self>`
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - Associative --- `a + (b + c) = (a + b) + c`.
/// - With identity --- there exists `e = 0`, such that `a + e = a`.
#[proc_macro_derive(AddMonoid)]
pub fn derive_add_monoid(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddAssociative<Self> for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddSemigroup for #name {}
        impl astraea::algebra::AddUnitalMagma for #name {}
        impl astraea::algebra::AddMonoid for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `AddLoop` trait.
///
/// Marks this type as a loop under addition, generating implementations for the following traits:
///
/// - `AddClosed`
/// - `AddInvertible<Self>`
/// - `AddMagma`
/// - `AddUnitalMagma`
/// - `AddQuasigroup`
/// - `AddLoop`
///
/// `AddWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
/// - [`std::ops::Neg`]
/// - [`std::ops::Sub`]
/// - `AddWithIdentity<Self>`
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - With identity --- there exists `e = 0`, such that `a + e = a`.
/// - Invertible --- for all `a` there exists `-a`, such that `a + (-a) = e`.
#[proc_macro_derive(AddLoop)]
pub fn derive_add_loop(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddInvertible<Self> for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddUnitalMagma for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddLoop for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `AddInvertibleSemigroup` trait.
///
/// Marks this type as a semigroup under addition, generating implementations for the following
/// traits:
///
/// - `AddClosed`
/// - `AddAssociative<Self>`
/// - `AddInvertible<Self>`
/// - `AddMagma`
/// - `AddSemigroup`
/// - `AddQuasigroup`
/// - `AddInvertibleSemigroup`
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
/// - [`std::ops::Neg`]
/// - [`std::ops::Sub`]
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - Associative --- `a + (b + c) = (a + b) + c`.
/// - Invertible --- for all `a` there exists `-a`, such that `a + (-a) = e`.
#[proc_macro_derive(AddInvertibleSemigroup)]
pub fn derive_add_invertible_semigroup(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddAssociative<Self> for #name {}
        impl astraea::algebra::AddInvertible<Self> for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddSemigroup for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddInvertibleSemigroup for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `AddGroup` trait.
///
/// Marks this type as a group under addition, generating implementations for the following traits:
///
/// - `AddClosed`
/// - `AddInvertible<Self>`
/// - `AddAssociative<Self>`
/// - `AddMagma`
/// - `AddSemigroup`
/// - `AddQuasigroup`
/// - `AddUnitalMagma`
/// - `AddMonoid`
/// - `AddLoop`
/// - `AddInvertibleSemigroup`
/// - `AddGroup`
///
/// `AddWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
/// - [`std::ops::Neg`]
/// - [`std::ops::Sub`]
/// - `AddWithIdentity<Self>`
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - Associative --- `a + (b + c) = (a + b) + c`.
/// - With identity --- there exists `e = 0`, such that `a + e = a`.
/// - Invertible --- for all `a` there exists `-a`, such that `a + (-a) = e`.
#[proc_macro_derive(AddGroup)]
pub fn derive_add_group(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddInvertible<Self> for #name {}
        impl astraea::algebra::AddAssociative<Self> for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddSemigroup for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddUnitalMagma for #name {}
        impl astraea::algebra::AddMonoid for #name {}
        impl astraea::algebra::AddLoop for #name {}
        impl astraea::algebra::AddInvertibleSemigroup for #name {}
        impl astraea::algebra::AddGroup for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `AddAbelianGroup` trait.
///
/// Marks this type as an abelian group under addition, generating implementations for the
/// following traits:
///
/// - `AddClosed`
/// - `AddInvertible<Self>`
/// - `AddAssociative<Self>`
/// - `AddCommutative<Self>`
/// - `AddMagma`
/// - `AddSemigroup`
/// - `AddQuasigroup`
/// - `AddUnitalMagma`
/// - `AddMonoid`
/// - `AddLoop`
/// - `AddInvertibleSemigroup`
/// - `AddGroup`
/// - `AddAbelianGroup`
///
/// `AddWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
/// - [`std::ops::Neg`]
/// - [`std::ops::Sub`]
/// - `AddWithIdentity<Self>`
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - Associative --- `a + (b + c) = (a + b) + c`.
/// - With identity --- there exists `e = 0`, such that `a + e = a`.
/// - Invertible --- for all `a` there exists `-a`, such that `a + (-a) = e`.
/// - Commutative --- `a + b = b + a`.
#[proc_macro_derive(AddAbelianGroup)]
pub fn derive_add_abelian_group(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddInvertible<Self> for #name {}
        impl astraea::algebra::AddAssociative<Self> for #name {}
        impl astraea::algebra::AddCommutative<Self> for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddSemigroup for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddUnitalMagma for #name {}
        impl astraea::algebra::AddMonoid for #name {}
        impl astraea::algebra::AddLoop for #name {}
        impl astraea::algebra::AddInvertibleSemigroup for #name {}
        impl astraea::algebra::AddGroup for #name {}
        impl astraea::algebra::AddAbelianGroup for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `MulMagma` trait.
///
/// Marks this type as a magma under multiplication, generating implementations for the following
/// traits:
///
/// - `MulClosed`
/// - `MulMagma`
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Mul`]
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
#[proc_macro_derive(MulMagma)]
pub fn derive_mul_magma(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}

        impl astraea::algebra::MulMagma for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `MulSemigroup` trait.
///
/// Marks this type as a semigroup under multiplication, generating implementations for the
/// following traits:
///
/// - `MulClosed`
/// - `MulAssociative<Self>`
/// - `MulMagma`
/// - `MulSemigroup`
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Mul`]
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - Associative --- `a * (b * c) = (a * b) * c`.
#[proc_macro_derive(MulSemigroup)]
pub fn derive_mul_semigroup(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `MulQuasigroup` trait.
///
/// Marks this type as a quasigroup under multiplication, generating implementations for the
/// following traits:
///
/// - `MulClosed`
/// - `MulMagma`
/// - `MulQuasigroup`
///
/// `MulInvertible<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Mul`]
/// - [`std::ops::Div`]
/// - `MulInvertible<Self>`
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - Invertible --- for all `a` there exists `a⁻¹`, such that `a * a⁻¹ = 1`.
#[proc_macro_derive(MulQuasigroup)]
pub fn derive_mul_quasigroup(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulQuasigroup for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `MulUnitalMagma` trait.
///
/// Marks this type as a unital magma under multiplication, generating implementations for the
/// following traits:
///
/// - `MulClosed`
/// - `MulMagma`
/// - `MulUnitalMagma`
///
/// `MulWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Mul`]
/// - `MulWithIdentity<Self>`
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - With identity --- there exists `e = 1`, such that `a * e = a`.
#[proc_macro_derive(MulUnitalMagma)]
pub fn derive_mul_unital_magma(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulUnitalMagma for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `MulMonoid` trait.
///
/// Marks this type as a monoid under multiplication, generating implementations for the following
/// traits:
///
/// - `MulClosed`
/// - `MulAssociative<Self>`
/// - `MulMagma`
/// - `MulSemigroup`
/// - `MulUnitalMagma`
/// - `MulMonoid`
///
/// `MulWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Mul`]
/// - `MulWithIdentity<Self>`
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - Associative --- `a * (b * c) = (a * b) * c`.
/// - With identity --- there exists `e = 1`, such that `a * e = a`.
#[proc_macro_derive(MulMonoid)]
pub fn derive_mul_monoid(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::algebra::MulUnitalMagma for #name {}
        impl astraea::algebra::MulMonoid for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `MulLoop` trait.
///
/// Marks this type as a loop under multiplication, generating implementations for the following
/// traits:
///
/// - `MulClosed`
/// - `MulMagma`
/// - `MulUnitalMagma`
/// - `MulQuasigroup`
/// - `MulLoop`
///
/// `MulInvertible<Self>` and `MulWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Mul`]
/// - [`std::ops::Div`]
/// - `MulInvertible<Self>`
/// - `MulWithIdentity<Self>`
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - With identity --- there exists `e = 1`, such that `a * e = a`.
/// - Invertible --- for all `a` there exists `a⁻¹`, such that `a * a⁻¹ = 1`.
#[proc_macro_derive(MulLoop)]
pub fn derive_mul_loop(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulUnitalMagma for #name {}
        impl astraea::algebra::MulQuasigroup for #name {}
        impl astraea::algebra::MulLoop for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `MulInvertibleSemigroup` trait.
///
/// Marks this type as a semigroup under multiplication, generating implementations for the
/// following traits:
///
/// - `MulClosed`
/// - `MulAssociative<Self>`
/// - `MulMagma`
/// - `MulSemigroup`
/// - `MulQuasigroup`
/// - `MulInvertibleSemigroup`
///
/// `MulInvertible<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Mul`]
/// - [`std::ops::Div`]
/// - `MulInvertible<Self>`
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - Associative --- `a * (b * c) = (a * b) + c`.
/// - Invertible --- for all `a` there exists `a⁻¹`, such that `a * a⁻¹ = 1`.
#[proc_macro_derive(MulInvertibleSemigroup)]
pub fn derive_mul_invertible_semigroup(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::algebra::MulQuasigroup for #name {}
        impl astraea::algebra::MulInvertibleSemigroup for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `MulGroup` trait.
///
/// Marks this type as a group under multiplication, generating implementations for the following
/// traits:
///
/// - `MulClosed`
/// - `MulAssociative<Self>`
/// - `MulMagma`
/// - `MulSemigroup`
/// - `MulQuasigroup`
/// - `MulUnitalMagma`
/// - `MulMonoid`
/// - `MulLoop`
/// - `MulInvertibleSemigroup`
/// - `MulGroup`
///
/// `MulInvertible<Self>` and `MulWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Mul`]
/// - [`std::ops::Div`]
/// - `MulInvertible<Self>`
/// - `MulWithIdentity<Self>`
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - Associative --- `a * (b * c) = (a * b) * c`.
/// - With identity --- there exists `e = 1`, such that `a * e = a`.
/// - Invertible --- for all `a` there exists `a⁻¹`, such that `a * a⁻¹ = 1`.
#[proc_macro_derive(MulGroup)]
pub fn derive_mul_group(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::algebra::MulQuasigroup for #name {}
        impl astraea::algebra::MulUnitalMagma for #name {}
        impl astraea::algebra::MulMonoid for #name {}
        impl astraea::algebra::MulLoop for #name {}
        impl astraea::algebra::MulInvertibleSemigroup for #name {}
        impl astraea::algebra::MulGroup for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `MulAbelianGroup` trait.
///
/// Marks this type as an abelian group under multiplication, generating implementations for the
/// following traits:
///
/// - `MulClosed`
/// - `MulAssociative<Self>`
/// - `MulCommutative<Self>`
/// - `MulMagma`
/// - `MulSemigroup`
/// - `MulQuasigroup`
/// - `MulUnitalMagma`
/// - `MulMonoid`
/// - `MulLoop`
/// - `MulInvertibleSemigroup`
/// - `MulGroup`
/// - `MulAbelianGroup`
///
/// `MulInvertible<Self>` and `MulWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Mul`]
/// - [`std::ops::Div`]
/// - `MulInvertible<Self>`
/// - `MulWithIdentity<Self>`
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - Associative --- `a * (b * c) = (a * b) * c`.
/// - With identity --- there exists `e = 1`, such that `a * e = a`.
/// - Invertible --- for all `a` there exists `a⁻¹`, such that `a * a⁻¹ = 1`.
/// - Commutative --- `a * b = b * a`.
#[proc_macro_derive(MulAbelianGroup)]
pub fn derive_mul_abelian_group(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}
        impl astraea::algebra::MulCommutative<Self> for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::algebra::MulQuasigroup for #name {}
        impl astraea::algebra::MulUnitalMagma for #name {}
        impl astraea::algebra::MulMonoid for #name {}
        impl astraea::algebra::MulLoop for #name {}
        impl astraea::algebra::MulInvertibleSemigroup for #name {}
        impl astraea::algebra::MulGroup for #name {}
        impl astraea::algebra::MulAbelianGroup for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `Semiring` trait.
///
/// Marks this type as a semiring, generating implementations for the following traits:
///
/// - `AddClosed`
/// - `AddAssociative<Self>`
/// - `AddCommutative<Self>`
/// - `AddMagma`
/// - `AddSemigroup`
/// - `AddUnitalMagma`
/// - `AddMonoid`
///
/// - `MulClosed`
/// - `MulAssociative<Self>`
/// - `MulMagma`
/// - `MulSemigroup`
/// - `MulUnitalMagma`
/// - `MulMonoid`
///
/// - `Distributive`
///
/// `AddWithIdentity<Self>`, `MulWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
/// - [`std::ops::Mul`]
/// - `AddWithIdentity<Self>`
/// - `MulWithIdentity<Self>`
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - Associative --- `a + (b + c) = (a + b) + c`.
/// - With identity --- there exists `e = 0`, such that `a + e = a`.
/// - Commutative --- `a + b = b + a`.
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - Associative --- `a * (b * c) = (a * b) * c`.
/// - With identity --- there exists `e = 1`, such that `a * e = a`.
#[proc_macro_derive(Semiring)]
pub fn derive_semiring(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddAssociative<Self> for #name {}
        impl astraea::algebra::AddCommutative<Self> for #name {}
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}
        impl astraea::algebra::Distributive for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddSemigroup for #name {}
        impl astraea::algebra::AddUnitalMagma for #name {}
        impl astraea::algebra::AddMonoid for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::algebra::MulUnitalMagma for #name {}
        impl astraea::algebra::MulMonoid for #name {}

        impl astraea::algebra::Semiring for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `Rng` trait.
///
/// Marks this type as a rng, generating implementations for the following traits:
///
/// - `AddClosed`
/// - `AddAssociative<Self>`
/// - `AddInvertible<Self>`
/// - `AddCommutative<Self>`
/// - `AddMagma`
/// - `AddSemigroup`
/// - `AddQuasigroup`
/// - `AddUnitalMagma`
/// - `AddMonoid`
/// - `AddLoop`
/// - `AddInvertibleSemigroup`
/// - `AddGroup`
/// - `AddAbelianGroup`
///
/// - `MulClosed`
/// - `MulAssociative<Self>`
/// - `MulMagma`
/// - `MulSemigroup`
///
/// - `Distributive`
///
/// `AddWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
/// - [`std::ops::Neg`]
/// - [`std::ops::Sub`]
/// - [`std::ops::Mul`]
/// - `AddWithIdentity<Self>`
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - Associative --- `a + (b + c) = (a + b) + c`.
/// - With identity --- there exists `e = 0`, such that `a + e = a`.
/// - Invertible --- for all `a` there exists `-a`, such that `a + (-a) = 0`.
/// - Commutative --- `a + b = b + a`.
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - Associative --- `a * (b * c) = (a * b) * c`.
#[proc_macro_derive(Rng)]
pub fn derive_rng(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddAssociative<Self> for #name {}
        impl astraea::algebra::AddInvertible<Self> for #name {}
        impl astraea::algebra::AddCommutative<Self> for #name {}
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}
        impl astraea::algebra::Distributive for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddSemigroup for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddUnitalMagma for #name {}
        impl astraea::algebra::AddMonoid for #name {}
        impl astraea::algebra::AddLoop for #name {}
        impl astraea::algebra::AddInvertibleSemigroup for #name {}
        impl astraea::algebra::AddGroup for #name {}
        impl astraea::algebra::AddAbelianGroup for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}

        impl astraea::algebra::Rng for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `Ring` trait.
///
/// Marks this type as a ring, generating implementations for the following traits:
///
/// - `AddClosed`
/// - `AddAssociative<Self>`
/// - `AddInvertible<Self>`
/// - `AddCommutative<Self>`
/// - `AddMagma`
/// - `AddSemigroup`
/// - `AddQuasigroup`
/// - `AddUnitalMagma`
/// - `AddMonoid`
/// - `AddLoop`
/// - `AddInvertibleSemigroup`
/// - `AddGroup`
/// - `AddAbelianGroup`
///
/// - `MulClosed`
/// - `MulAssociative<Self>`
/// - `MulMagma`
/// - `MulSemigroup`
/// - `MulUnitalMagma`
/// - `MulMonoid`
///
/// - `Distributive`
///
/// `AddWithIdentity<Self>`, `MulWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
/// - [`std::ops::Neg`]
/// - [`std::ops::Sub`]
/// - [`std::ops::Mul`]
/// - `AddWithIdentity<Self>`
/// - `MulWithIdentity<Self>`
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - Associative --- `a + (b + c) = (a + b) + c`.
/// - With identity --- there exists `e = 0`, such that `a + e = a`.
/// - Invertible --- for all `a` there exists `-a`, such that `a + (-a) = 0`.
/// - Commutative --- `a + b = b + a`.
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - Associative --- `a * (b * c) = (a * b) * c`.
/// - With identity --- there exists `e = 1`, such that `a * e = a`.
#[proc_macro_derive(Ring)]
pub fn derive_ring(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddAssociative<Self> for #name {}
        impl astraea::algebra::AddInvertible<Self> for #name {}
        impl astraea::algebra::AddCommutative<Self> for #name {}
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}
        impl astraea::algebra::Distributive for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddSemigroup for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddUnitalMagma for #name {}
        impl astraea::algebra::AddMonoid for #name {}
        impl astraea::algebra::AddLoop for #name {}
        impl astraea::algebra::AddInvertibleSemigroup for #name {}
        impl astraea::algebra::AddGroup for #name {}
        impl astraea::algebra::AddAbelianGroup for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::algebra::MulUnitalMagma for #name {}
        impl astraea::algebra::MulMonoid for #name {}

        impl astraea::algebra::Ring for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `CommutativeRing` trait.
///
/// Marks this type as a commutative ring, generating implementations for the following traits:
///
/// - `AddClosed`
/// - `AddAssociative<Self>`
/// - `AddInvertible<Self>`
/// - `AddCommutative<Self>`
/// - `AddMagma`
/// - `AddSemigroup`
/// - `AddQuasigroup`
/// - `AddUnitalMagma`
/// - `AddMonoid`
/// - `AddLoop`
/// - `AddInvertibleSemigroup`
/// - `AddGroup`
/// - `AddAbelianGroup`
///
/// - `MulClosed`
/// - `MulAssociative<Self>`
/// - `MulCommutative<Self>`
/// - `MulMagma`
/// - `MulSemigroup`
/// - `MulUnitalMagma`
/// - `MulMonoid`
///
/// - `Distributive`
///
/// `AddWithIdentity<Self>`, `MulWithIdentity<Self>` must be implemented manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
/// - [`std::ops::Neg`]
/// - [`std::ops::Sub`]
/// - [`std::ops::Mul`]
/// - `AddWithIdentity<Self>`
/// - `MulWithIdentity<Self>`
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - Associative --- `a + (b + c) = (a + b) + c`.
/// - With identity --- there exists `e = 0`, such that `a + e = a`.
/// - Invertible --- for all `a` there exists `-a`, such that `a + (-a) = 0`.
/// - Commutative --- `a + b = b + a`.
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - Associative --- `a * (b * c) = (a * b) * c`.
/// - With identity --- there exists `e = 1`, such that `a * e = a`.
/// - Commutative --- `a * b = b * a`.
#[proc_macro_derive(CommutativeRing)]
pub fn derive_commutative_ring(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddAssociative<Self> for #name {}
        impl astraea::algebra::AddInvertible<Self> for #name {}
        impl astraea::algebra::AddCommutative<Self> for #name {}
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}
        impl astraea::algebra::MulCommutative<Self> for #name {}
        impl astraea::algebra::Distributive for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddSemigroup for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddUnitalMagma for #name {}
        impl astraea::algebra::AddMonoid for #name {}
        impl astraea::algebra::AddLoop for #name {}
        impl astraea::algebra::AddInvertibleSemigroup for #name {}
        impl astraea::algebra::AddGroup for #name {}
        impl astraea::algebra::AddAbelianGroup for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::algebra::MulUnitalMagma for #name {}
        impl astraea::algebra::MulMonoid for #name {}

        impl astraea::algebra::Ring for #name {}
    }
    .into()
}

/// Derive macro generating an impl of the `Field` trait.
///
/// Marks this type as a field, generating implementations for the following traits:
///
/// - `AddClosed`
/// - `AddAssociative<Self>`
/// - `AddInvertible<Self>`
/// - `AddCommutative<Self>`
/// - `AddMagma`
/// - `AddSemigroup`
/// - `AddQuasigroup`
/// - `AddUnitalMagma`
/// - `AddMonoid`
/// - `AddLoop`
/// - `AddInvertibleSemigroup`
/// - `AddGroup`
/// - `AddAbelianGroup`
///
/// - `MulClosed`
/// - `MulAssociative<Self>`
/// - `MulCommutative<Self>`
/// - `MulMagma`
/// - `MulSemigroup`
/// - `MulQuasigroup`
/// - `MulUnitalMagma`
/// - `MulMonoid`
/// - `MulLoop`
/// - `MulInvertibleSemigroup`
/// - `MulGroup`
/// - `MulAbelianGroup`
///
/// - `Distributive`
///
/// `AddWithIdentity<Self>`, `MulWithIdentity<Self>`, `MulInvertible<Self>` must be implemented
/// manually.
///
/// # Requirements
///
/// The following traits must be implemented (or derived):
///
/// - [`MathObject`]
/// - [`std::ops::Add`]
/// - [`std::ops::Neg`]
/// - [`std::ops::Sub`]
/// - [`std::ops::Mul`]
/// - `AddWithIdentity<Self>`
/// - `MulWithIdentity<Self>`
///
/// Addition (`+`) must be:
///
/// - Closed --- sum of elements returns the same type.
/// - Associative --- `a + (b + c) = (a + b) + c`.
/// - With identity --- there exists `e = 0`, such that `a + e = a`.
/// - Invertible --- for all `a` there exists `-a`, such that `a + (-a) = 0`.
/// - Commutative --- `a + b = b + a`.
///
/// Multiplication (`*`) must be:
///
/// - Closed --- product of elements returns the same type.
/// - Associative --- `a * (b * c) = (a * b) * c`.
/// - With identity --- there exists `e = 1`, such that `a * e = a`.
/// - Invertible --- for all `a` there exists `a⁻¹`, such that `a * a⁻¹ = 1`.
/// - Commutative --- `a * b = b * a`.
#[proc_macro_derive(Field)]
pub fn derive_field(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddAssociative<Self> for #name {}
        impl astraea::algebra::AddInvertible<Self> for #name {}
        impl astraea::algebra::AddCommutative<Self> for #name {}
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}
        impl astraea::algebra::MulCommutative<Self> for #name {}
        impl astraea::algebra::Distributive for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddSemigroup for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddUnitalMagma for #name {}
        impl astraea::algebra::AddMonoid for #name {}
        impl astraea::algebra::AddLoop for #name {}
        impl astraea::algebra::AddInvertibleSemigroup for #name {}
        impl astraea::algebra::AddGroup for #name {}
        impl astraea::algebra::AddAbelianGroup for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::algebra::MulQuasigroup for #name {}
        impl astraea::algebra::MulUnitalMagma for #name {}
        impl astraea::algebra::MulMonoid for #name {}
        impl astraea::algebra::MulLoop for #name {}
        impl astraea::algebra::MulInvertibleSemigroup for #name {}
        impl astraea::algebra::MulGroup for #name {}
        impl astraea::algebra::MulAbelianGroup for #name {}

        impl astraea::algebra::Field for #name {}
    }
    .into()
}
