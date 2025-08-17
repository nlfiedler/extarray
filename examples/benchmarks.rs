//
// Copyright (c) 2025 Nathan Fiedler
//
use extarray::ExtensibleArray;
use std::time::Instant;

//
// This example was intended to show that an extensible array will grow in less
// time than a vector, however in practice that is not the case.
//

fn create_segarray(size: u64) {
    let start = Instant::now();
    let mut coll: ExtensibleArray<u64> = ExtensibleArray::new();
    for value in 0..size {
        coll.push(value);
    }
    let duration = start.elapsed();
    println!("extarray: {:?}", duration);
}

fn create_vector(size: u64) {
    let start = Instant::now();
    let mut coll: Vec<u64> = Vec::new();
    for value in 0..size {
        coll.push(value);
    }
    let duration = start.elapsed();
    println!("vector: {:?}", duration);
}

fn main() {
    println!("creating ExtensibleArray...");
    create_segarray(1_000_000_000);
    println!("creating Vec...");
    create_vector(1_000_000_000);
}
