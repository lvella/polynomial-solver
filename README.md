This repository contains a library for handling polynomial systems over
arbitrary fields, but with special focus on polynomials over large finite prime
fields, with the goal of being used in the formal verification of Zero Knowledge
circuits.

Currently it implements the Gröbner Basis algorithm *Signature Buchberger*, as
defined in this paper *"Practical Gröbner basis computation"*, by Bjarke
Hammersholt Roune and Michael Stillman:
http://www.broune.com/papers/issac2012.html.

Besides the library, the following tools are provided:
* `check-determinism`: a tool that attempts to decide whether a ZK circuit's
  output is unique for a given input (i.e. the circuit encodes a function),
  using Gröbner Basis;
* `grobner-basis`: a tool to compute the Gröbner Basis of a polynomial systems.

## How to build

First you need to [install rust](https://www.rust-lang.org/tools/install) if you
haven't already.

Then clone this repository, and inside its directory, run:

```
$ cargo build --release
```

The `--release` flag is highly recommended if you intent to actually execute it,
because Gröbner Basis is a slow algorithm, and the execution time difference
between an optimized and unoptimized build is as much as 20x.

## How to check determinism of R1CS circuits

Run:
```
$ cargo run --release --bin check-determinism PATH_TO_INPUT_FILE.r1cs
```
or if you already built, you can execute the binary directly:
```
$ ./target/release/check-determinism PATH_TO_INPUT_FILE.r1cs
```

After a possibly very long execution time, outputting a lot of debugging
information on the progress of Gröbner Basis execution, eventually it will
terminate with one of the following lines output:
* `DETERMINISTIC`
* `UNKNOWN`

A full execution of a small problem would look like:
```
$ ./target/release/check-determinism ../formalbenchmarks/generated/O2/Montgomery2Edwards@montgomery@circomlib.r1cs 
#(p: 0, s: 0), [] → idx 0, sign {0, 1}: x0 ...(1)
#(p: 1, s: 0), [] → idx 1, sign {1, 1}: x3*x2 ...(2)
#(p: 2, s: 1), [] → idx 2, sign {2, 1}: x6*x5 ...(2)
#(p: 3, s: 3), [] → idx 3, sign {3, 1}: x8*x1 ...(1)
#(p: 4, s: 6), [] → idx 4, sign {4, 1}: x8*x2 ...(1)
#(p: 5, s: 7), [(4, 3)] → idx 5, sign {4, x1}: x7*x2 ...(1)
#(p: 6, s: 8), [(4, 1)] → idx 6, sign {4, x3}: x8 ...(0)
#(p: 7, s: 9), [(5, 1), (6, 3)] → idx 7, sign {4, x3*x1}: x7 ...(0)
#(p: 8, s: 16), [] → idx 8, sign {5, 1}: x4 ...(1)
#(p: 9, s: 24), [] → idx 9, sign {6, 1}: x5 ...(1)
DETERMINISTIC
```
