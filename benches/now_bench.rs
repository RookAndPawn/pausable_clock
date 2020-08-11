use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pausable_clock::*;
use std::time::Instant;

fn now_benchmark(c: &mut Criterion) {
    let clock = PausableClock::default();

    let repeat = 1000;

    c.bench_function("Std Instant Now", |b| {
        b.iter(|| {
            for _ in 0..repeat {
                black_box(Instant::now());
            }
        })
    });
    c.bench_function("Pausable Clock Now", |b| {
        b.iter(|| {
            for _ in 0..repeat {
                black_box(clock.now());
            }
        })
    });

    // Lol, this is too slow to do every time. 10x slower than one-way
    // c.bench_function("hashmap reading 1m from 10k", |b| {
    //     b.iter(|| {
    //         read_many_hash_map(&hashmap, &one_way_keys, 100);
    //     })
    // });
}

criterion_group!(benches, now_benchmark,);
criterion_main!(benches);
