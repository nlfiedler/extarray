# Space-Efficient Extensible Arrays

## Overview

This Rust [crate](https://crates.io/crates/extarray) implements a growable array as described in section 3 of the paper **Immediate-Access Indexing Using Space-Efficient Extensible Arrays** by Alistair Moffat and Joel Mackenzie, published in 2022.

* ACM ISBN 979-8-4007-0021-7/22/12
* https://doi.org/10.1145/3572960.3572984

This data structure supports `push` and `pop` operations and does _not_ support inserts or removes at other locations within the array. One exception is the `swap/remove` operation which will retrieve a value from a specified index, overwrite that slot with the value at the end of the array, decrement the count, and return the retrieved value.

This is part of a collection of similar data structures:

* [Optimal Arrays](https://github.com/nlfiedler/optarray)
    - Similar O(√N) space overhead and similar O(1) running time for most operations
    - Markedly faster than Extensible Arrays for repeated pushes
* [Segment Array](https://github.com/nlfiedler/segarray)
    - Grows geometrically like `Vec`, hence O(N) space overhead
    - Much faster than Extensible Arrays for repeated pushes

### Background

The intent of this data structure is that it will work well with arena memory allocators, and is designed to efficiently utilize a significant portion of the available RAM of a system. From section 2 of the paper:

> More generally, the old and new segments must be assumed to be disjoint, and
> at the critical transition moment both must be assumed to be present
> simultaneously. That is, the momentary overhead space cost is 𝑘𝑛 elements,
> which is a substantial imposition, and might mean that memory utilization is
> restricted to less than 50% of available capacity. Note that this accounting in
> regard to the Geometric approach also relies on memory segments being reusable
> after they have been released back into the memory pool. That is not in any way
> guaranteed, and in the absence of a defragmentation operation it might be that
> a Geometric extensible array leaves behind a trail of empty-but-unusable space,
> further worsening the effective space overhead ratio.

The specification for the data structure is contained in section 3 of the paper.

### Memory Usage

Compared to the `Vec` type in the Rust standard library, this data structure will have substantially less unused space, on the order of O(√N). The dope vector contributes to the overhead of this data structure, and that is on the order of O(√N). Based on the current implementation of `Vec`, as much as 50% of the space may be unused since it has a growth factor of 2. The [Segment Array](https://github.com/nlfiedler/segarray) has the same growth factor as `Vec` and potentially the same proportion of unused space (its dope vector is a fixed size).

## Examples

A simple example copied from the unit tests.

```rust
let inputs = [
    "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
];
let mut arr: ExtensibleArray<String> = ExtensibleArray::new();
for item in inputs {
    arr.push(item.to_owned());
}
for (idx, elem) in arr.iter().enumerate() {
    assert_eq!(inputs[idx], elem);
}
```

## Supported Rust Versions

The Rust edition is set to `2024` and hence version `1.85.0` is the minimum supported version.

## Troubleshooting

### Memory Leaks

Finding memory leaks with [Address Sanitizer](https://clang.llvm.org/docs/AddressSanitizer.html) is fairly [easy](https://doc.rust-lang.org/beta/unstable-book/compiler-flags/sanitizer.html) and seems to work best on Linux. The shell script below gives a quick demonstration of running one of the examples with ASAN analysis enabled.

```shell
#!/bin/sh
env RUSTDOCFLAGS=-Zsanitizer=address RUSTFLAGS=-Zsanitizer=address \
    cargo run -Zbuild-std --target x86_64-unknown-linux-gnu --release --example leak_test
```

## References

* \[1\]: [Immediate-Access Indexing Using Space-Efficient Extensible Arrays (2022)](https://www.semanticscholar.org/paper/Immediate-Access-Indexing-Using-Space-Efficient-Moffat/31e7dd2ee63efa92009035f4f04d9569ed3024c6)
* \[2\]: [JMMackenzie/immediate-access](https://github.com/JMMackenzie/immediate-access)
