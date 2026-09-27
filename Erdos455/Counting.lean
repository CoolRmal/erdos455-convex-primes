/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.FreeGaps
import Erdos455.Period

/-!
# Counting gaps

**Theorem 16** of the paper: the number `N(D) = #{n ≥ n₀ : gap q n ≤ D}` of gaps up to `D` is at
most `(Λ + G) / (2 M) · D + o(D)`. Here `N(D) = first q (D + 1) - start q`, and we bound
`first q (2 M K + 2)` by splitting the gaps below `2 M K + 2` into periods:

* the runs of the gaps `2 M k + 2 i` (`k < K`, `1 ≤ i < M`) have total length at most
  `Λ K + 255` by the certificate (Corollary 12, `Erdos455.IsConvexPrimeSeq.sum_period_le`);
* the runs of the gaps `2 M j` (`1 ≤ j ≤ K`) have total length at most `G K + #exceptional`
  (Lemmas 13 and 14, `Erdos455.IsConvexPrimeSeq.sum_runLength_two_mul_M_le`), and
  `2 ^ #exceptional ≤ 4 M K`;
* the odd gaps do not occur.

The logarithmic error term is only used in the weak form `e ≤ ε K + (4 M + 1) / ε`, valid for
every `ε > 0`, which follows from `e² ≤ 2 ^ e + 1`.

## Main statements

* `Erdos455.IsConvexPrimeSeq.first_two_mul_M_mul_add_two`: the decomposition of
  `first q (2 M K + 2)` into periods (Lemma 6(d)).
* `Erdos455.IsConvexPrimeSeq.exists_first_le`: Theorem 16, in the form
  `first q (2 M K + 2) ≤ (Λ + G + ε) K + C_ε` for every `ε > 0`.
-/

namespace Erdos455

/-- `n² ≤ 2 ^ n + 1` for every natural number `n`. -/
theorem sq_le_two_pow_add_one (n : ℕ) : n ^ 2 ≤ 2 ^ n + 1 := by
  have hlin : ∀ n, 3 ≤ n → 2 * n + 1 ≤ 2 ^ n := fun n hn => by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n _ ih => rw [pow_succ]; omega
  rcases lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have := hlin n hn
    rw [show (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) by ring, pow_succ 2 n]
    omega

/-- If `e² ≤ B K`, then `e ≤ ε K + B / ε` for every `ε > 0`. -/
theorem le_mul_add_div_of_sq_le {e B K ε : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hε : 0 < ε) (h : e ^ 2 ≤ B * K) : e ≤ ε * K + B / ε := by
  rcases le_or_gt e (ε * K) with hle | hlt
  · exact hle.trans (le_add_of_nonneg_right (div_nonneg hB hε.le))
  · have he' : 0 < e := (mul_nonneg hε.le hK).trans_lt hlt
    have hmul : ε * e * e ≤ B * e := by
      calc ε * e * e = ε * e ^ 2 := by ring
        _ ≤ ε * (B * K) := mul_le_mul_of_nonneg_left h hε.le
        _ = B * (ε * K) := by ring
        _ ≤ B * e := mul_le_mul_of_nonneg_left hlt.le hB
    have : e ≤ B / ε := by
      rw [le_div_iff₀ hε, mul_comm]
      exact le_of_mul_le_mul_right hmul he'
    linarith [mul_nonneg hε.le hK]

namespace IsConvexPrimeSeq

variable {q : ℕ → ℕ} (hq : IsConvexPrimeSeq q)
include hq

/-- One period of gap values: the gaps `2 M k + 2 i` (`1 ≤ i < M`) and then `2 M (k + 1)`. -/
theorem first_period (k : ℕ) :
    first q (2 * M * (k + 1) + 2) = first q (2 * M * k + 2) +
      ∑ i ∈ Finset.Ico 1 M, runLength q (2 * M * k + 2 * i) + runLength q (2 * M * (k + 1)) := by
  have hM : 1 ≤ M := by norm_num [M]
  have hperiod := hq.first_two_mul_add (M * k + 1) (M - 1)
  rw [show 2 * (M * k + 1 + (M - 1)) = 2 * (M * (k + 1)) by rw [mul_add_one]; omega,
    show 2 * (M * k + 1) = 2 * M * k + 2 by ring] at hperiod
  rw [show 2 * M * (k + 1) = 2 * (M * (k + 1)) by ring, hq.first_two_mul_add_two,
    ← hq.first_add_runLength, hperiod, Finset.sum_Ico_eq_sum_range]
  have hsum : ∑ i ∈ Finset.range (M - 1), runLength q (2 * M * k + 2 * (1 + i)) =
      ∑ i ∈ Finset.range (M - 1), runLength q (2 * (M * k + 1 + i)) :=
    Finset.sum_congr rfl fun i _ => congrArg _ (by ring)
  rw [hsum]

/-- **Lemma 6(d)**: `first q (2 M K + 2)` is `start q` plus the lengths of the runs of all the
gaps up to `2 M K + 1`, grouped into `K` periods. -/
theorem first_two_mul_M_mul_add_two (K : ℕ) :
    first q (2 * M * K + 2) = start q +
      ∑ k ∈ Finset.range K, ∑ i ∈ Finset.Ico 1 M, runLength q (2 * M * k + 2 * i) +
        ∑ j ∈ Finset.Icc 1 K, runLength q (2 * M * j) := by
  induction K with
  | zero => simpa using hq.first_eq_start le_rfl
  | succ K ih =>
    rw [hq.first_period, ih, Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega)]
    ring

/-- `first q (2 M K + 2) ≤ n₀ + (Λ + G) K + 255 + #(exceptional q K)`. -/
theorem first_le_add_card (K : ℕ) :
    (first q (2 * M * K + 2) : ℝ) ≤
      start q + (growth + G) * K + 255 + (exceptional q K).card := by
  have hperiod : (∑ k ∈ Finset.range K, ∑ i ∈ Finset.Ico 1 M, runLength q (2 * M * k + 2 * i) :
      ℝ) ≤ growth * K + 255 := by exact_mod_cast hq.sum_period_le K
  rw [hq.first_two_mul_M_mul_add_two]
  push_cast
  linarith [hq.sum_runLength_two_mul_M_le K]

/-- The number `e` of exceptional `j ∈ [1, K]` satisfies `e² ≤ (4 M + 1) K`. -/
theorem card_exceptional_sq_le (K : ℕ) :
    (exceptional q K).card ^ 2 ≤ (4 * M + 1) * K := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [exceptional]
  · have := hq.two_pow_card_exceptional_le hK
    have := sq_le_two_pow_add_one (exceptional q K).card
    nlinarith

/-- **Theorem 16**: for every `ε > 0` there is `C` such that
`N(2 M K + 1) ≤ first q (2 M K + 2) ≤ (Λ + G + ε) K + C` for all `K`. -/
theorem exists_first_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ K : ℕ, (first q (2 * M * K + 2) : ℝ) ≤ (growth + G + ε) * K + C := by
  refine ⟨start q + 255 + (4 * M + 1) / ε, fun K => ?_⟩
  have hcard : ((exceptional q K).card : ℝ) ≤ ε * K + (4 * M + 1) / ε :=
    le_mul_add_div_of_sq_le (by positivity) (Nat.cast_nonneg _) hε
      (by exact_mod_cast hq.card_exceptional_sq_le K)
  linarith [hq.first_le_add_card K]

end IsConvexPrimeSeq

end Erdos455
