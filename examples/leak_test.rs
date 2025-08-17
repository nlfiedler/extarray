//
// Copyright (c) 2025 Nathan Fiedler
//
use extarray::ExtensibleArray;

//
// Basically useless except that it can be tested with a memory analyzer to
// determine if the segment array is leaking memory. By storing `String` instead
// of numbers, this is more interesting in terms of memory management since the
// array must drop all of the values, either when the collection is dropped,
// when an IntoIterator is used and eventually dropped.
//
fn main() {
    let mut array: ExtensibleArray<String> = ExtensibleArray::new();
    // add enough values to allocate a bunch of segments
    for _ in 0..15_020 {
        let value = ulid::Ulid::new().to_string();
        array.push(value);
    }

    // use an into iterator the to visit elements from various segments
    for (index, value) in array.into_iter().skip(1).enumerate() {
        if index == 1 {
            println!("1: {value}");
        } else if index == 15 {
            println!("15: {value}");
        } else if index == 48 {
            println!("48: {value}");
        } else if index == 240 {
            println!("240: {value}");
        } else if index == 512 {
            println!("512: {value}");
        } else if index == 1024 {
            println!("1024: {value}");
        } else if index == 15_000 {
            println!("15_000: {value}");
            // exit the iterator early intentionally
            break;
        }
    }
    // now the Drop implementation for the IntoIter will be invoked and the
    // memory analyzer can catch even more issues
}
