# Erdős Problem #455: convex sequences of primes grow like at least `0.864289 n²`

[![CI](https://github.com/CoolRmal/erdos455-convex-primes/actions/workflows/ci.yml/badge.svg)](https://github.com/CoolRmal/erdos455-convex-primes/actions/workflows/ci.yml)

A Lean 4 / Mathlib formalisation (work in progress) of the lower bound

$$\liminf_{n\to\infty} \frac{q_n}{n^2} \;\ge\; \frac{M}{\Lambda + G} \;>\; 0.864289$$

for every strictly increasing sequence of primes `q₀ < q₁ < ⋯` with non-decreasing gaps
`q (n + 2) - q (n + 1) ≥ q (n + 1) - q n`, towards
[Erdős Problem #455](https://www.erdosproblems.com/455) (which asks whether `q n / n² → ∞`).
Here `M = 3 · 5 · 7 · 11 · 13 · 17 = 255255`, `Λ = 295318` and `G = 17.2244…`. This improves
Richter's bound `0.352` (1976), which is recovered as a corollary in the exact form of
`erdos_455.variants.liminf` of
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/455.lean).

## Layout

* `Challenge.lean` — the statements of record (imports Mathlib only).
* `Solution.lean` — the same statements, with proofs from the library `Erdos455/`.
* `comparator.json` — configuration for `lake comparator`, run in CI with the Lean kernel,
  nanoda and con-ron (the kernels Palomar uses).
* `Erdos455/Packed/` — arithmetic on packed vectors of small fields stored in one natural number.
* `Erdos455/DP/` — the max-plus dynamic program and its certificate.
* `scripts/` — reference implementations used to design and cross-check the certificate
  (not part of the proof).

## The proof

The argument has three ingredients:

1. A run of equal gaps `d` in the sequence is an arithmetic progression of primes, which has at
   most `P(d) - 2` terms after its first outside a sparse exceptional set, where `P(d)` is the
   least prime not dividing `d`.
2. Eventually every term is coprime to `M`, which turns the counting of gaps into a max-plus
   dynamic program on the units of `ℤ / Mℤ` that is periodic in the gap value.
3. An integer potential `φ` on the units certifies that this program gains at most
   `Λ = 295318` per period of gap values.

Item 3 is a finite computation of about `2 · 10¹⁰` elementary steps. Here it is **checked by
the Lean kernel**, without `native_decide`: the values of the dynamic program on the 92160
units are packed into two natural numbers of 85085 fields of 9 bits each, so that every step
of the value iteration is a few dozen GMP operations on 96 KB numbers
(`Erdos455/DP/Step.lean`). The soundness of this packed computation is proved once and for all
(`Erdos455/Packed/`), and the kernel evaluates the computation in chunks.

## Status

Under active development; see the CI badge and the remaining `sorry`s.
