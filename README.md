# SPBiTopology

Author: Bilel Methnani

A personal project exploring bi-topological structures on Gaussian integers using Lean 4 and Mathlib.

## Overview

This project formalizes a bi-topological framework on the Gaussian integers (Z[i]) based on a canonical base-beta expansion where beta = -1 + i. The core idea is that every Gaussian integer has a unique representation as a finite sequence of binary digits (0 or 1) in this base, and this representation induces two natural topologies:

- **Suffix topology (tau_suffix)**: Based on agreement of least significant digits (LSD-first). Two elements are "close" if they agree on their first k digits from the least significant end.
- **Prefix topology (tau_prefix)**: Based on agreement of most significant digits (MSD-first) and digit length. Two elements are "close" if they have the same digit length and agree on their first m digits from the most significant end.

The project explores properties of these topologies, their interaction, and draws analogies to computational complexity theory.

## Technical Details

### The Base Beta

The base beta = -1 + i is a Gaussian integer with norm 2. Every Gaussian integer z can be uniquely written as:

```
z = d_0 + beta * d_1 + beta^2 * d_2 + ... + beta^(n-1) * d_(n-1)
```

where each d_i is either 0 or 1, and the leading digit d_(n-1) = 1 for nonzero z.

### Key Constructions

- `digit z`: Returns true if beta does not divide z (equivalently, if z.re mod 2 differs from z.im mod 2)
- `betaQuot z`: The quotient such that z = digit(z) + beta * betaQuot(z)
- `toDigits z`: The canonical digit representation as a list of booleans (LSD first)
- `evalDigits ds`: Reconstructs a Gaussian integer from its digit list
- `digitLength z`: The number of digits in the canonical representation
- `nthDigitLSD z n`: The n-th digit from the least significant end
- `nthDigitMSD z n`: The n-th digit from the most significant end

### Topological Structure

The suffix and prefix embeddings map Gaussian integers into the Cantor space (infinite binary sequences):

- `iotaSuffix z`: Maps z to the sequence of its LSD digits (extended with zeros)
- `iotaPrefixCanonical z`: Interleaves the binary encoding of digitLength with MSD digits

Both embeddings are proven injective, making the induced topologies T0.

### Cylinder Sets

- **SuffixCylinder k pattern**: Elements whose first k LSD digits match the pattern
- **PrefixCylinder len m pattern**: Elements with digit length = len and first m MSD digits matching the pattern
- **BiCylinder**: Intersection of suffix and prefix cylinders (always finite)
- **ResonantPrefixCylinder**: A variant where digit length is constrained modulo 2^m

### Dynamical Properties

Multiplication by beta acts as a shift operator on the digit representation:
- In the suffix topology, multiplication by beta is continuous (prepends a 0 digit)
- The orbit of any nonzero element eventually enters any suffix cylinder containing 0
- Digit length grows linearly under iteration: digitLength(beta^n * z) = digitLength(z) + n

## Project Structure

```
BiTopology/
  SPBiTopology/
    Basic.lean        - Core definitions: beta, digit, betaQuot, toDigits, evalDigits,
                        termination measure, norm properties, LSD/MSD agreement theorems
    Topology.lean     - Suffix and prefix topologies, cylinder sets, continuity of
                        multiplication and addition, T0 properties, dynamical systems
    Complexity.lean   - Complexity classes via cylinders, suffix/prefix decidability,
                        separation theorems, resource bounds, P vs NP analogies
    Parity.lean       - Integer embedding, beta-divisibility for integers, parity lemmas
    PrimeBasic.lean   - Prime digit structure, mod 4 properties, primes in BiCylinders
    SuffixCylinders.lean - Odd/even suffix cylinders, membership characterizations
```

## Main Results

### Foundation (Basic.lean)
- Canonical beta-adic representation exists and is unique
- `evalDigits_toDigits`: evalDigits (toDigits z) = z
- `lsd_agree_iff_pow_dvd`: LSD agreement is equivalent to divisibility by powers of beta
- Termination measure for the digit computation algorithm

### Topology (Topology.lean)
- `iotaSuffix_injective`: The suffix embedding is injective
- `iotaPrefixCanonical_injective`: The prefix embedding is injective
- `tau_suffix_t0`: The suffix topology is T0
- `suffixCylinder_isClopen`: Suffix cylinders are clopen
- `continuous_mul_beta_suffix`: Multiplication by beta is continuous in tau_suffix
- `continuous_add_suffix`: Addition is continuous in tau_suffix
- `biCylinder_finite`: BiCylinders are finite sets

### Complexity (Complexity.lean)
- `suffix_prefix_separation`: SuffixClass and PrefixClass are distinct
- `suffix_not_prefix_exists`: There exist suffix-decidable predicates that are not prefix-decidable
- `prefix_not_suffix_exists`: There exist prefix-decidable predicates that are not suffix-decidable
- `suffixClass_subset_witnessClass`: Analogy to P subset of NP

### Number Theory (Parity.lean, PrimeBasic.lean, SuffixCylinders.lean)
- `beta_dvd_int_iff`: For integers, beta divides n iff 2 divides n
- `odd_prime_first_digit`: Odd primes have first digit = true
- `primes_in_biCylinder_finite`: Primes in any BiCylinder form a finite set

## Requirements

- Lean 4 (v4.12.0)
- Mathlib4 (v4.12.0)

## Building

```bash
lake build
```

## Notes

This is a personal exploration project. The code formalizes mathematical structures and proves various properties, but the broader claims about connections to computational complexity are speculative analogies rather than rigorous results.

## License

This project is licensed under the Mozilla Public License 2.0. See the [LICENSE](LICENSE) file for details.
