//
// Copyright (c) 2025 Nathan Fiedler
//
use extarray::ExtensibleArray;

//
// Create and drop collections and iterators in order to test for memory leaks.
// Must allocate Strings in order to fully test the drop implementation.
//
fn main() {
    // add only enough values to allocate one segment
    let mut array: ExtensibleArray<String> = ExtensibleArray::new();
    for _ in 0..2 {
        let value = ulid::Ulid::new().to_string();
        array.push(value);
    }
    drop(array);

    // add enough values to allocate a bunch of segments
    let mut array: ExtensibleArray<String> = ExtensibleArray::new();
    for _ in 0..80 {
        let value = ulid::Ulid::new().to_string();
        array.push(value);
    }
    drop(array);

    // IntoIterator: add only enough values to allocate one segment
    let mut array: ExtensibleArray<String> = ExtensibleArray::new();
    for _ in 0..2 {
        let value = ulid::Ulid::new().to_string();
        array.push(value);
    }
    let itty = array.into_iter();
    drop(itty);

    // IntoIterator: add enough values to allocate a bunch of segments
    let mut array: ExtensibleArray<String> = ExtensibleArray::new();
    for _ in 0..250 {
        let value = ulid::Ulid::new().to_string();
        array.push(value);
    }
    // skip enough elements to pass over a few segments then drop
    for (index, value) in array.into_iter().skip(28).enumerate() {
        if index == 28 {
            println!("28: {value}");
            // exit the iterator early intentionally
            break;
        }
    }
}
