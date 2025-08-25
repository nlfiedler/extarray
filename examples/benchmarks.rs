//
// Copyright (c) 2025 Nathan Fiedler
//
use extarray::ExtensibleArray;
use rand::{Rng, SeedableRng, rngs::SmallRng};
use std::time::Instant;

//
// This example was intended to show that an extensible array will grow in less
// time than a vector, however in practice that is not the case.
//

fn benchmark_extarray(size: usize) {
    let start = Instant::now();
    let mut coll: ExtensibleArray<usize> = ExtensibleArray::new();
    for value in 0..size {
        coll.push(value);
    }
    let duration = start.elapsed();
    println!("extarray create: {:?}", duration);

    // test random access `size` times; use SmallRng to avoid dominating the
    // running time with random number generation
    let mut rng = SmallRng::seed_from_u64(0);
    let start = Instant::now();
    for _ in 0..size {
        let index = rng.random_range(0..size);
        assert_eq!(coll[index], index);
    }
    let duration = start.elapsed();
    println!("extarray random: {:?}", duration);

    // test sequenced access for entire collection
    let start = Instant::now();
    for (index, value) in coll.iter().enumerate() {
        assert_eq!(*value, index);
    }
    let duration = start.elapsed();
    println!("extarray ordered: {:?}", duration);
}

fn benchmark_vector(size: usize) {
    let start = Instant::now();
    let mut coll: Vec<usize> = Vec::new();
    for value in 0..size {
        coll.push(value);
    }
    let duration = start.elapsed();
    println!("vector create: {:?}", duration);

    // test random access `size` times; use SmallRng to avoid dominating the
    // running time with random number generation
    let mut rng = SmallRng::seed_from_u64(0);
    let start = Instant::now();
    for _ in 0..size {
        let index = rng.random_range(0..size);
        assert_eq!(coll[index], index);
    }
    let duration = start.elapsed();
    println!("vector random: {:?}", duration);

    // test sequenced access for entire collection
    let start = Instant::now();
    for (index, value) in coll.iter().enumerate() {
        assert_eq!(*value, index);
    }
    let duration = start.elapsed();
    println!("vector ordered: {:?}", duration);
}

fn main() {
    println!("creating ExtensibleArray...");
    benchmark_extarray(100_000_000);
    println!("creating Vec...");
    benchmark_vector(100_000_000);
}
