/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.Defs
import Erdos455.DP.Spec
import Erdos455.LeastNonDivisor

/-!
# The constant `G`

The primes `19 = p'₁ < p'₂ < ⋯` that are at least `19` are `largePrime 0, largePrime 1, …`,
and `G = 17 + ∑_{i ≥ 1} (p'ᵢ₊₁ - p'ᵢ) / (p'₁ ⋯ p'ᵢ)`. This file proves that the series
converges, that `G` bounds the average of `P(2 M j) - 2` (Lemma 14 of the paper), and the
numerical bounds `17.2244 < G < 17.2245` (Lemma 15).

## Main statements

* `Erdos455.sum_leastNonDivisor_two_mul_M_le`: `∑_{j = 1}^{K} (P(2 M j) - 2) ≤ G K`.
* `Erdos455.G_lt_bound`, `Erdos455.lt_G_bound`: `17.2244 < G < 17.2245`.
-/

namespace Erdos455

theorem largePrime_prime (i : ℕ) : (largePrime i).Prime := by
  sorry

theorem nineteen_le_largePrime (i : ℕ) : 19 ≤ largePrime i := by
  sorry

theorem largePrime_strictMono : StrictMono largePrime := by
  sorry

theorem largePrime_zero : largePrime 0 = 19 := by
  sorry

/-- The terms of the series defining `G` are summable. -/
theorem summable_G :
    Summable fun i : ℕ => ((largePrime (i + 1) : ℝ) - largePrime i) /
      ∏ j ∈ Finset.range (i + 1), (largePrime j : ℝ) := by
  sorry

/-- **Lemma 14**: `∑_{j = 1}^{K} (P(2 M j) - 2) ≤ G K`, where `P(d)` is the least prime not
dividing `d`. -/
theorem sum_leastNonDivisor_two_mul_M_le (K : ℕ) :
    ∑ j ∈ Finset.Icc 1 K, ((leastNonDivisor (2 * M * j) : ℝ) - 2) ≤ G * K := by
  sorry

/-- **Lemma 15** (upper bound). -/
theorem G_lt_bound : G < 17.2245 := by
  sorry

/-- **Lemma 15** (lower bound). -/
theorem lt_G_bound : 17.2244 < G := by
  sorry

end Erdos455
