# Erdős Problem #455: convex sequences of primes grow like at least `0.864289 n²`

[![CI](https://github.com/CoolRmal/erdos455-convex-primes/actions/workflows/ci.yml/badge.svg)](https://github.com/CoolRmal/erdos455-convex-primes/actions/workflows/ci.yml)

A Lean 4 / Mathlib formalisation of the lower bound

$$\liminf_{n\to\infty} \frac{q_n}{n^2} \;\ge\; \frac{M}{\Lambda + G} \;>\; 0.864289$$

for every strictly increasing sequence of primes `q₀ < q₁ < ⋯` with non-decreasing gaps
`q (n + 2) - q (n + 1) ≥ q (n + 1) - q n`, towards
[Erdős Problem #455](https://www.erdosproblems.com/455) (which asks whether `q n / n² → ∞`).
Here `M = 3 · 5 · 7 · 11 · 13 · 17 = 255255`, `Λ = 295318` and `G = 17.2244…`. This improves
Richter's bound `0.352` (1976), which is recovered as a corollary in the exact form of
`erdos_455.variants.liminf` of
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/455.lean).

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`: in particular
no `native_decide`. The finite computation at its heart (about `5 · 10¹⁰` elementary operations) is
evaluated by the Lean kernel.

## Statements

`Challenge.lean` (imports Mathlib only) states, for every `q : ℕ → ℕ` with `StrictMono q` and
`∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n`:

| declaration | statement |
| --- | --- |
| `Erdos455.ofReal_le_liminf` | `ENNReal.ofReal (255255 / (295318 + G)) ≤ liminf (q n / n²)` |
| `Erdos455.liminf_gt` | `liminf (q n / n²) > 0.864289` |
| `Erdos455.eventually_lt` | `∀ᶠ n in atTop, 0.864289 * n² < q n` |
| `Erdos455.G_lt` | `G < 17.2245` |
| `Erdos455.erdos_455.variants.liminf` | `liminf (q n / n²) > 0.352` (Richter; the Formal Conjectures statement) |

where `G = 17 + ∑_{i ≥ 1} (p'ᵢ₊₁ - p'ᵢ) / (p'₁ ⋯ p'ᵢ)` over the primes `19 = p'₁ < p'₂ < ⋯`
that are at least `19`. `Solution.lean` proves them, and `lake comparator` (configured by
`comparator.json`) checks that it proves exactly the statements of `Challenge.lean`.

## The proof

1. **Runs of equal gaps.** The indices with a given gap `d` are consecutive, and the
   corresponding terms form an arithmetic progression of primes with difference `d`. Such a
   progression has at most `P(d) - 2` terms after its first, where `P(d)` is the least prime not
   dividing `d`, unless it starts at `P(d)` itself (`Progression.lean`, `ConvexSeq.lean`).
2. **The dynamic program.** Eventually every term is coprime to `M`. Following the residue of
   the current term modulo `M` as the gap value runs through `2, 4, 6, …` gives a max-plus
   dynamic program on the `92160` units of `ℤ / Mℤ`, periodic in the gap with period `2M`
   (`Period.lean`).
3. **The certificate.** A potential `φ` on the units certifies that this program gains at most
   `Λ = 295318` per period (Proposition 11; `DP/`).
4. **The gaps divisible by `2M`**, on which the program gives no information, contribute at
   most `G` per period (`Constant.lean`, `FreeGaps.lean`). Counting gaps then gives
   `#{n : gap n ≤ D} ≤ (Λ + G) D / 2M + o(D)` (`Counting.lean`), and summing the gaps gives the
   bound on `q n` (`Main.lean`).

### How the certificate is checked by the kernel

Proposition 11 amounts to one period of max-plus value iteration: `255254` steps over the
`92160` units, starting from `φ`, ending at most at `φ + Λ`. This is checked by the kernel
(`Erdos455/DP/`):

* **Packed representation** (`Packed/Field.lean`, `Packed/Ops.lean`). A function on the units
  is stored as two natural numbers (the residues `≡ 1` and `≡ 2 mod 3`), each with
  `85085 = M / 3` fields of 9 bits. The kernel evaluates arithmetic and bitwise operations on
  `ℕ` literals with GMP, so one operation acts on 85085 residues. A step of the value iteration
  is a few dozen such operations (rotations, additions, masks and a fieldwise maximum that uses
  the top bit of every field as a guard bit) on 96 KB numbers (`DP/Step.lean`).
* **Soundness** is proved once and for all, for every input: a successful step dominates the
  max-plus operator on all runs of units (`DP/Sound.lean`, `DP/Invariant.lean`, `DP/Run.lean`).
  Every step checks at run time the bounds it needs (no field reaches its guard bit, no field
  borrows), so soundness needs no knowledge of the particular values.
* **Chunks.** The period is split into 499 chunks of 512 steps. A command run at elaboration
  time (`DP/Gen.lean`) computes the potential `φ` (one period of value iteration from zero), the
  intermediate states and a normalisation schedule, and emits one theorem
  `L.run K 512 lo sched st_k = some ([], st_(k+1))` per chunk, proved by
  `of_decide_eq_true rfl`. The generator is untrusted: the kernel re-evaluates every chunk.
  The final comparison with `φ + 295318` is a single kernel evaluation (`DP/Certificate.lean`).

Up to an additive constant, `φ` is the potential of the paper (whose values span `[-109, 0]`,
with SHA-256 `9ae840ca…dd07` in the format of the paper's checker); `scripts/gen_phi.c`
recomputes it and reproduces this hash.

## Layout

* `Challenge.lean`, `Solution.lean`, `comparator.json` — the statements of record, their proofs
  and the comparator configuration.
* `Erdos455/` — the development; `Erdos455/DP/` is the dynamic program and its certificate,
  `Erdos455/Packed/` the arithmetic on packed vectors.
* `scripts/` — reference implementations used to design and cross-check the certificate
  (`gen_phi.c`, `packed_ref.py`) and to time the external checkers; not part of the proof.

## Building and checking

```bash
lake exe cache get
lake build
```

Building `Erdos455/DP/Certificate.lean` takes about 20 minutes and 4 GB of memory: it runs the
value iteration twice at elaboration time and has the kernel check the 499 chunks. CI runs
`lake comparator` with the Lean kernel, nanoda and con-ron, the kernels Palomar uses.
