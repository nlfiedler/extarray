# Space-Efficient Extensible Arrays

## Overview

An append-only (no insert or remove) growable array as described in section 3 of the paper **Immediate-Access Indexing Using Space-Efficient Extensible Arrays** by Alistair Moffat and Joel Mackenzie, published in 2022.

* ACM ISBN 979-8-4007-0021-7/22/12
* https://doi.org/10.1145/3572960.3572984

### Background

The design of this data structure is intended to work well with arena memory allocators.

From section 2 of the paper:

> More generally, the old and new segments must be assumed to be disjoint, and
> at the critical transition moment both must be assumed to be present
> simultaneously. That is, the momentary overhead space cost is 𝑘𝑛elements,
> which is a substantial imposition, and might mean that memory utilization is
> restricted to less than 50% of available capacity. Note that this accounting in
> regard to the Geometric approach also relies on memory segments being reusable
> after they have been released back into the memory pool. That is not in any way
> guaranteed, and in the absence of a defragmentation operation it might be that
> a Geometric extensible array leaves behind a trail of empty-but-unusable space,
> further worsening the effective space overhead ratio.

The specification for the data structure is contained in section 3 of the paper.

## Supported Rust Versions

The Rust edition is set to `2024` and hence version `1.85.0` is the minimum supported version.

## References

* \[1\]: [Immediate-Access Indexing Using Space-Efficient Extensible Arrays (2022)](https://www.semanticscholar.org/paper/Immediate-Access-Indexing-Using-Space-Efficient-Moffat/31e7dd2ee63efa92009035f4f04d9569ed3024c6)
* \[2\]: [JMMackenzie/immediate-access](https://github.com/JMMackenzie/immediate-access)
