use proc_macro::TokenStream;
use quote::quote;
use syn::{DeriveInput, parse_macro_input};

extern crate proc_macro;

#[proc_macro_derive(MathObject)]
pub fn derive_math_object(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    quote! {
        impl astraea::algebra::MathObject for #name {}
    }
    .into()
}

#[proc_macro_derive(AddMagma)]
pub fn derive_add_magma(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}

        impl astraea::algebra::AddMagma for #name {}
    }
    .into()
}

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

#[proc_macro_derive(AddMonoid)]
pub fn derive_add_monoid(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddAssociative<Self> for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddSemigroup for #name {}
        impl astraea::algebra::AddMonoid for #name {}
    }
    .into()
}

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

#[proc_macro_derive(AddLoop)]
pub fn derive_add_loop(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddInvertible<Self> for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddLoop for #name {}
    }
    .into()
}

#[proc_macro_derive(AddGroup)]
pub fn derive_add_group(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::AddClosed for #name {}
        impl astraea::algebra::AddInvertible<Self> for #name {}
        impl astraea::algebra::AddAssociative<Self> for #name {}

        impl astraea::algebra::AddMagma for #name {}
        impl astraea::algebra::AddSemigroup for #name {}
        impl astraea::algebra::AddMonoid for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddLoop for #name {}
        impl astraea::algebra::AddGroup for #name {}
    }
    .into()
}

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
        impl astraea::algebra::AddMonoid for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddLoop for #name {}
        impl astraea::algebra::AddGroup for #name {}
        impl astraea::algebra::AddAbelianGroup for #name {}
    }
    .into()
}

#[proc_macro_derive(MulMagma)]
pub fn derive_mul_magma(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}

        impl astraea::algebra::MulMagma for #name {}
    }
    .into()
}

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

#[proc_macro_derive(MulMonoid)]
pub fn derive_mul_monoid(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::algebra::MulMonoid for #name {}
    }
    .into()
}

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

#[proc_macro_derive(MulLoop)]
pub fn derive_mul_loop(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulQuasigroup for #name {}
        impl astraea::algebra::MulLoop for #name {}
    }
    .into()
}

#[proc_macro_derive(MulGroup)]
pub fn derive_mul_group(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::algebra::MulMonoid for #name {}
        impl astraea::algebra::MulQuasigroup for #name {}
        impl astraea::algebra::MulLoop for #name {}
        impl astraea::algebra::MulGroup for #name {}
    }
    .into()
}

#[proc_macro_derive(MulAbelianGroup)]
pub fn derive_mul_abelian_group(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as DeriveInput).ident;

    quote! {
        impl astraea::algebra::MulClosed for #name {}
        impl astraea::algebra::MulAssociative<Self> for #name {}
        impl astraea::algebra::MulCommutative<Self> for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::algebra::MulMonoid for #name {}
        impl astraea::algebra::MulQuasigroup for #name {}
        impl astraea::algebra::MulLoop for #name {}
        impl astraea::algebra::MulGroup for #name {}
        impl astraea::algebra::MulAbelianGroup for #name {}
    }
    .into()
}

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
        impl astraea::algebra::AddMonoid for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::astraea::MulMonoid for #name {}

        impl astraea::algebra::Semiring for #name {}
    }
    .into()
}

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
        impl astraea::algebra::AddMonoid for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddLoop for #name {}
        impl astraea::algebra::AddGroup for #name {}
        impl astraea::algebra::AddAbelianGroup for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}

        impl astraea::algebra::Rng for #name {}
    }
    .into()
}

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
        impl astraea::algebra::AddMonoid for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddLoop for #name {}
        impl astraea::algebra::AddGroup for #name {}
        impl astraea::algebra::AddAbelianGroup for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::astraea::MulMonoid for #name {}

        impl astraea::algebra::Semiring for #name {}
        impl astraea::algebra::Rng for #name {}
        impl astraea::algebra::Ring for #name {}
    }
    .into()
}

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
        impl astraea::algebra::AddMonoid for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddLoop for #name {}
        impl astraea::algebra::AddGroup for #name {}
        impl astraea::algebra::AddAbelianGroup for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::astraea::MulMonoid for #name {}

        impl astraea::algebra::Semiring for #name {}
        impl astraea::algebra::Rng for #name {}
        impl astraea::algebra::Ring for #name {}
    }
    .into()
}

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
        impl astraea::algebra::AddMonoid for #name {}
        impl astraea::algebra::AddQuasigroup for #name {}
        impl astraea::algebra::AddLoop for #name {}
        impl astraea::algebra::AddGroup for #name {}
        impl astraea::algebra::AddAbelianGroup for #name {}

        impl astraea::algebra::MulMagma for #name {}
        impl astraea::algebra::MulSemigroup for #name {}
        impl astraea::algebra::MulMonoid for #name {}
        impl astraea::algebra::MulQuasigroup for #name {}
        impl astraea::algebra::MulLoop for #name {}
        impl astraea::algebra::MulGroup for #name {}
        impl astraea::algebra::MulAbelianGroup for #name {}

        impl astraea::algebra::Semiring for #name {}
        impl astraea::algebra::Rng for #name {}
        impl astraea::algebra::Ring for #name {}
        impl astraea::algebra::Field for #name {}
    }
    .into()
}
