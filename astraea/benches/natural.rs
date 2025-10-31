use criterion::BenchmarkId;
use criterion::Criterion;
use criterion::Throughput;
use criterion::{criterion_group, criterion_main};

use astraea::core::Instruction;
use astraea::digit;
use astraea::math::Digit;
use astraea::natural::NaturalNumber;

pub fn natural_add(c: &mut Criterion) {
    let mut group = c.benchmark_group(Instruction::NaturalAdd.opcode());

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = NaturalNumber::new(vec![digit!(9); size]);
                let rhs = NaturalNumber::new(vec![digit!(1); size]);

                lhs + rhs
            });
        });
    }
    group.finish();
}

pub fn natural_subtract(c: &mut Criterion) {
    let mut group = c.benchmark_group(Instruction::NaturalSubtract.opcode());

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = NaturalNumber::new(vec![digit!(9); size]);
                let rhs = NaturalNumber::new(vec![digit!(1); size]);

                lhs - rhs
            });
        });
    }
    group.finish();
}

pub fn natural_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group(Instruction::NaturalMultiply.opcode());

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = NaturalNumber::new(vec![digit!(9); size]);
                let rhs = NaturalNumber::new(vec![digit!(1); size]);

                lhs * rhs
            });
        });
    }
    group.finish();
}

pub fn natural_div(c: &mut Criterion) {
    let mut group = c.benchmark_group(Instruction::NaturalQuotient.opcode());

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = NaturalNumber::new(vec![digit!(9); size]);
                let rhs = NaturalNumber::new(vec![digit!(1); size]);

                lhs / rhs
            });
        });
    }
    group.finish();
}

pub fn natural_rem(c: &mut Criterion) {
    let mut group = c.benchmark_group(Instruction::NaturalRemainder.opcode());

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = NaturalNumber::new(vec![digit!(9); size]);
                let rhs = NaturalNumber::new(vec![digit!(1); size]);

                lhs / rhs
            });
        });
    }
    group.finish();
}

pub fn natural_gcd(c: &mut Criterion) {
    let mut group = c.benchmark_group(Instruction::NaturalGCD.opcode());

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = NaturalNumber::new(vec![digit!(9); size]);
                let rhs = NaturalNumber::new(vec![digit!(1); size]);

                lhs.gcd(rhs)
            });
        });
    }
    group.finish();
}

pub fn natural_lcm(c: &mut Criterion) {
    let mut group = c.benchmark_group(Instruction::NaturalLCM.opcode());

    for size in [2usize.pow(4), 2usize.pow(8), 2usize.pow(12), 2usize.pow(16)].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.sample_size(10);
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let lhs = NaturalNumber::new(vec![digit!(9); size]);
                let rhs = NaturalNumber::new(vec![digit!(1); size]);

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
