use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pausable_clock::*;

fn run_unpausable_benchmark(c: &mut Criterion) {
    let clock = PausableClock::default();

    let repeat = 1000;

    c.bench_function("Std Instant Now", |b| {
        b.iter(|| {
            for _ in 0..repeat {
                black_box(clock.run_unpausable(|| black_box(0)));
            }
        })
    });
}

criterion_group!(benches, run_unpausable_benchmark,);
criterion_main!(benches);
