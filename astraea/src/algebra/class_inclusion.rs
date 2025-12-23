/// Marks type as a chain of class inclusion, where traits to the left generalize traits to the
/// right.
///
/// ```ignore
/// // A ⊃ B ⊃ C ⊃ D ⊃ E
/// inclusion_chain!(A, B, C, D, E);
/// ```
macro_rules! inclusion_chain {
    ($generalization:ident, $set: ident) => {
        impl<T: $set> $generalization for T {}
    };

    ($generalization:ident, $set:ident, $($rest:ident),+ $(,)?) => {
        inclusion_chain!($generalization, $set);
        inclusion_chain!($set, $($rest),+);
    };
}

pub(super) use inclusion_chain;
