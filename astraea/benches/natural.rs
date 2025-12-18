use criterion::BenchmarkId;
use criterion::Criterion;
use criterion::Throughput;
use criterion::{criterion_group, criterion_main};

use astraea::prelude::*;

pub fn natural_add(c: &mut Criterion) {
    let mut group = c.benchmark_group("Natural Add");

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = Natural::new(vec![Digit::Nine; size]);
                let rhs = Natural::new(vec![Digit::One; size]);

                lhs + rhs
            });
        });
    }
    group.finish();
}

pub fn natural_subtract(c: &mut Criterion) {
    let mut group = c.benchmark_group("Natural Sub");

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = Natural::new(vec![Digit::Nine; size]);
                let rhs = Natural::new(vec![Digit::One; size]);

                lhs - rhs
            });
        });
    }
    group.finish();
}

pub fn natural_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("Natural Mul");

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = Natural::new(vec![Digit::Nine; size]);
                let rhs = Natural::new(vec![Digit::One; size]);

                lhs * rhs
            });
        });
    }
    group.finish();
}

pub fn natural_div(c: &mut Criterion) {
    let mut group = c.benchmark_group("Natural Div");

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = Natural::new(vec![Digit::Nine; size]);
                let rhs = Natural::new(vec![Digit::One; size]);

                lhs / rhs
            });
        });
    }
    group.finish();
}

pub fn natural_rem(c: &mut Criterion) {
    let mut group = c.benchmark_group("Natural Rem");

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = Natural::new(vec![Digit::Nine; size]);
                let rhs = Natural::new(vec![Digit::One; size]);

                lhs / rhs
            });
        });
    }
    group.finish();
}

pub fn natural_gcd(c: &mut Criterion) {
    let mut group = c.benchmark_group("Natural GCD");

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = Natural::new(vec![Digit::Nine; size]);
                let rhs = Natural::new(vec![Digit::One; size]);

                lhs.gcd(rhs)
            });
        });
    }
    group.finish();
}

pub fn natural_lcm(c: &mut Criterion) {
    let mut group = c.benchmark_group("Natural LCM");

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = Natural::new(vec![Digit::Nine; size]);
                let rhs = Natural::new(vec![Digit::One; size]);

                lhs.lcm(rhs)
            });
        });
    }
    group.finish();
}

criterion_group!(
    natural,
    natural_add,
    natural_subtract,
    natural_mul,
    natural_div,
    natural_rem,
    natural_gcd,
    natural_lcm,
);
criterion_main!(natural);
