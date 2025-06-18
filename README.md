# dafny-bignums

This repository uses bitstrings to represent arbitrary precision unsigned integers.
It has formal proofs that the bitstring arithmetic operations are correct
with respect to Dafny's built-in `nat` type.

To run verification:

```sh
dafny verify *.dfy
```

## Supported operations

- Addition, subtraction, and multiplication
  - In `bignums.dfy`
- Division
  - In `division.dfy`
- Modular exponentiation
  - In `mod-exp.dfy`

## Other files

- `add-aux.dfy`
  - Lemmas for proving addition is correct
- `sub-aux.dfy`
  - Lemmas for proving subtraction is correct
- `mul-aux.dfy`
  - A lemma for proving multiplication is correct
- `bignums-lemmas.dfy`
  - Other helpful lemmas for proving operations are correct
- `bitstring-lemmas.dfy`
  - Lemmas for working with bitstrings
- `bitstrings.dfy`
  - Defines the conversions between bitstrings and nats 
- `bound.dfy`
  - A useful lemma for modular arithmetic proofs
- `mod-exp-integers.dfy`
  - Simulation of `mod-exp.dfy` using `nat` to show the algorithm
- `modulo-integer-properties.dfy`
  - Useful properties of modular arithmetic
- `pow2.dfy`
  - Definition of $2^n$ and properties
