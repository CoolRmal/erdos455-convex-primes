/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib

/-!
# Erdős Problem 455: convex sequences of primes grow at least like `0.864289 n²`

This file is the statement of record: it contains the definitions and the theorem statements
proved in `Solution.lean` (checked against this file by `lake comparator`, see
`comparator.json`). It imports only Mathlib.

Let `q₀ < q₁ < q₂ < ⋯` be primes whose gaps are non-decreasing,
`q (n + 2) - q (n + 1) ≥ q (n + 1) - q n`. Erdős asked whether necessarily `q n / n² → ∞`
(Erdős Problem #455, <https://www.erdosproblems.com/455>). Richter [Ri76] proved
`liminf q n / n² ≥ 0.352`. The main result formalised here is the improvement

  `liminf_{n → ∞} q n / n² ≥ M / (Λ + G) > 0.864289`,

where `M = 3 · 5 · 7 · 11 · 13 · 17 = 255255`, `Λ = 295318` is the growth rate of a max-plus
dynamic program on the units of `ℤ / Mℤ` (certified by a finite computation that is checked by
the Lean kernel), and `G = 17.2244…` is the constant `Erdos455.G` below.

The hypotheses on `q` are stated exactly as in `erdos_455.variants.liminf` of the Formal
Conjectures project (`FormalConjectures/ErdosProblems/455.lean`), whose statement (Richter's
theorem) is recovered as a corollary. Since `q` is strictly increasing, the truncated
subtraction on `ℕ` in the gap condition is harmless. The quotient `q n / n ^ 2` is taken in
`ℝ≥0∞`, as in Formal Conjectures, so that `liminf` is always meaningful.

## References

* [Ri76] B. Richter, *Über die Monotonie von Differenzenfolgen*, Acta Arith. 30 (1976),
  225–227.
* [EG80] P. Erdős, R. L. Graham, *Old and new problems and results in combinatorial number
  theory*, Monogr. Enseign. Math. 28 (1980), p. 91.
* [EP455] T. F. Bloom, *Erdős Problem #455*, <https://www.erdosproblems.com/455>.
* Formal Conjectures, `FormalConjectures/ErdosProblems/455.lean`,
  <https://github.com/google-deepmind/formal-conjectures>.
-/

open Filter
open scoped ENNReal

namespace Erdos455

/-! ### The constant `G` -/

/-- The primes that are at least `19`, in increasing order: `largePrime 0 = 19`,
`largePrime 1 = 23`, `largePrime 2 = 29`, … -/
noncomputable def largePrime (i : ℕ) : ℕ :=
  Nat.nth (fun p => p.Prime ∧ 19 ≤ p) i

/-- The constant `G = (19 - 2) + ∑_{i ≥ 1} (p'ᵢ₊₁ - p'ᵢ) / (p'₁ ⋯ p'ᵢ) = 17.2244296…`, where
`19 = p'₁ < p'₂ < ⋯` are the primes that are at least `19` (so `p'ᵢ = largePrime (i - 1)`).
It bounds the average of `P(2Mj) - 2` over `j`, where `P(d)` is the least prime not dividing
`d`: these are the gaps divisible by `2M`, on which the dynamic program gives no information. -/
noncomputable def G : ℝ :=
  17 + ∑' i : ℕ, ((largePrime (i + 1) : ℝ) - largePrime i) /
    ∏ j ∈ Finset.range (i + 1), (largePrime j : ℝ)

/-! ### Main results -/

/-- **Main theorem** (sharp form). If `q` is a strictly increasing sequence of primes with
non-decreasing gaps, then `liminf q n / n² ≥ 255255 / (295318 + G)`. -/
theorem ofReal_le_liminf : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    ENNReal.ofReal (255255 / (295318 + G)) ≤
      liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop := by
  sorry

/-- **Main theorem**. If `q` is a strictly increasing sequence of primes with non-decreasing
gaps, then `liminf q n / n² > 0.864289`. -/
theorem liminf_gt : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop > 0.864289 := by
  sorry

/-- **Main theorem**, eventual form. If `q` is a strictly increasing sequence of primes with
non-decreasing gaps, then `q n > 0.864289 n²` for all sufficiently large `n`. -/
theorem eventually_lt : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    ∀ᶠ n : ℕ in atTop, (0.864289 : ℝ) * n ^ 2 < q n := by
  sorry

/-- Numerical value of the constant: `G < 17.2245`. -/
theorem G_lt : G < 17.2245 := by
  sorry

/-- **Richter's theorem** [Ri76], stated exactly as `erdos_455.variants.liminf` in Formal
Conjectures: `liminf q n / n² > 0.352`. It follows from the main theorem. -/
theorem erdos_455.variants.liminf : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop > 0.352 := by
  sorry

end Erdos455
