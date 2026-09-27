/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.Counting

/-!
# From gap counts to growth

Section 7 of the paper. By Theorem 16, for every `ε > 0` the index `n` is at most
`β · gap q n + C` with `β = (Λ + G + ε) / (2 M)`, since `n < first q (gap q n + 1)`. Summing
the gaps, `q n ≥ (n² / 2 - (C + 1/2) n) / β`, which gives **Theorem 1**: `c n² < q n`
eventually, for every `c < M / (Λ + G) = 255255 / (295318 + G)`. Hence
`liminf q n / n² ≥ M / (Λ + G) > 0.864289`.

Unlike the paper, we do not need `gap q n → ∞` here: the bound `n ≤ β · gap q n + C` holds for
every `n`.

## Main statements

* `Erdos455.IsConvexPrimeSeq.eventually_mul_sq_lt`: Theorem 1, eventual form.
* `Erdos455.IsConvexPrimeSeq.ofReal_le_liminf`: Theorem 1, `liminf` form in `ℝ≥0∞`.
* `Erdos455.Main.ofReal_le_liminf`, `Erdos455.Main.liminf_gt`, `Erdos455.Main.eventually_lt`,
  `Erdos455.Main.liminf_gt_richter`: the statements of `Challenge.lean`.
-/

open Filter
open scoped ENNReal NNReal

namespace Erdos455

/-- `∑_{k < n} k = n (n - 1) / 2`, in `ℝ`. -/
theorem sum_range_natCast (n : ℕ) : ∑ k ∈ Finset.range n, (k : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- If `c n² < u n` eventually for every `c < r`, then `liminf u n / n² ≥ r` in `ℝ≥0∞`. -/
theorem ofReal_le_liminf_div_sq {u : ℕ → ℕ} {r : ℝ}
    (h : ∀ c < r, ∀ᶠ n : ℕ in atTop, c * n ^ 2 < u n) :
    ENNReal.ofReal r ≤ liminf (fun n : ℕ => (u n : ℝ≥0∞) / n ^ 2) atTop := by
  rw [le_liminf_iff]
  intro y hy
  have hy_top : y ≠ ∞ := ne_top_of_lt hy
  filter_upwards [h _ ((ENNReal.lt_ofReal_iff_toReal_lt hy_top).mp hy), eventually_gt_atTop 0]
    with n hn hn0
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by positivity)) (Or.inl (by simp))]
  have hmul : y * (n : ℝ≥0∞) ^ 2 = ENNReal.ofReal (y.toReal * n ^ 2) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hy_top,
      ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hmul, ← ENNReal.ofReal_natCast (u n),
    ENNReal.ofReal_lt_ofReal_iff (hn.trans_le' (by positivity))]
  exact hn

/-- The numerical value: `0.864289 < M / (Λ + G)`, from `G < 17.2245` (Lemma 15). -/
theorem lt_ratio : (0.864289 : ℝ) < 255255 / (295318 + G) := by
  have := G_lt_bound
  have := lt_G_bound
  rw [lt_div_iff₀ (by linarith)]
  linarith

namespace IsConvexPrimeSeq

variable {q : ℕ → ℕ} (hq : IsConvexPrimeSeq q)
include hq

/-- By Theorem 16, the index `n` is at most `(Λ + G + ε) / (2 M)` times its gap, up to an
additive constant: all the indices `n' ∈ [n₀, n]` have `gap q n' ≤ gap q n`. -/
theorem exists_le_mul_gap {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, (n : ℝ) ≤ (growth + G + ε) / (2 * M) * gap q n + C := by
  obtain ⟨C, hC⟩ := hq.exists_first_succ_le hε
  refine ⟨C, fun n => ?_⟩
  have hpos : 0 < (growth : ℝ) + G + ε := by
    have := lt_G_bound
    positivity
  rcases lt_or_ge n (start q) with hn | hn
  · have h0 := hC 0
    rw [zero_add, hq.first_eq_start (by norm_num), Nat.cast_zero, mul_zero, zero_add] at h0
    have : (n : ℝ) ≤ start q := by exact_mod_cast hn.le
    have : 0 ≤ (growth + G + ε) / (2 * M) * gap q n := by positivity
    linarith
  · have hlt : n < first q (gap q n + 1) := (hq.lt_first_iff hn).mpr (Nat.lt_add_one _)
    exact (Nat.cast_le.mpr hlt.le).trans (hC _)

/-- Summing the gaps: if `n ≤ β · gap q n + C` for all `n`, then
`n² / 2 - (C + 1/2) n ≤ β q n`. -/
theorem sq_div_two_sub_le {β C : ℝ} (hβ : 0 ≤ β) (h : ∀ n : ℕ, (n : ℝ) ≤ β * gap q n + C)
    (n : ℕ) : (n : ℝ) ^ 2 / 2 - (C + 1 / 2) * n ≤ β * q n := by
  have hsum : (q 0 : ℝ) + ∑ k ∈ Finset.range n, (gap q k : ℝ) = q n := by
    exact_mod_cast (by simpa using hq.add_sum_gap 0 n)
  have hq0 : 0 ≤ β * q 0 := by positivity
  calc (n : ℝ) ^ 2 / 2 - (C + 1 / 2) * n = ∑ k ∈ Finset.range n, (k : ℝ) - C * n := by
        rw [sum_range_natCast]
        ring
    _ ≤ ∑ k ∈ Finset.range n, (β * gap q k + C) - C * n := by
        gcongr with k
        exact h k
    _ = β * (q n - q 0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hsum, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ β * q n := by linarith

/-- **Theorem 1** (eventual form). If `c < M / (Λ + G) = 255255 / (295318 + G)`, then
`c n² < q n` for all sufficiently large `n`. -/
theorem eventually_mul_sq_lt {c : ℝ} (hc : c < 255255 / (295318 + G)) :
    ∀ᶠ n : ℕ in atTop, c * n ^ 2 < q n := by
  have hG := lt_G_bound
  set L : ℝ := 295318 + G with hL_def
  have hL : 0 < L := by linarith
  have hcL : c * L < 255255 := by rwa [lt_div_iff₀ hL] at hc
  -- choose `ε > 0` with `c (L + ε) < M`
  set ε := (255255 - c * L) / (|c| + 1) with hε_def
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hcε : c * ε < 255255 - c * L := by
    calc c * ε ≤ |c| * ε := mul_le_mul_of_nonneg_right (le_abs_self c) hε.le
      _ < (|c| + 1) * ε := by linarith
      _ = 255255 - c * L := by rw [hε_def]; field_simp
  obtain ⟨C, hC⟩ := hq.exists_le_mul_gap hε
  set β := ((growth : ℝ) + G + ε) / (2 * M) with hβ_def
  have hβ_eq : β = (L + ε) / 510510 := by
    simp only [hβ_def, hL_def, growth, M, Nat.cast_ofNat]
    ring
  have hβ : 0 < β := by rw [hβ_eq]; positivity
  set δ := 1 / 2 - c * β with hδ_def
  have hδ : 0 < δ := by
    rw [hδ_def, hβ_eq]
    linarith
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop ((|C| + 1) / δ)]
    with n hn
  have hn0 : 0 < (n : ℝ) := lt_trans (by positivity) hn
  have hδn : |C| + 1 < δ * n := by rwa [div_lt_iff₀ hδ, mul_comm] at hn
  have hCn : (C + 1 / 2) * n < δ * n * n := by
    have := le_abs_self C
    nlinarith
  refine lt_of_mul_lt_mul_left ?_ hβ.le
  calc β * (c * n ^ 2) = n ^ 2 / 2 - δ * n * n := by rw [hδ_def]; ring
    _ < n ^ 2 / 2 - (C + 1 / 2) * n := by linarith
    _ ≤ β * q n := hq.sq_div_two_sub_le hβ.le hC n

/-- **Theorem 1**: `liminf q n / n² ≥ M / (Λ + G)`. -/
theorem ofReal_le_liminf :
    ENNReal.ofReal (255255 / (295318 + G)) ≤
      liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop :=
  ofReal_le_liminf_div_sq fun _ hc => hq.eventually_mul_sq_lt hc

end IsConvexPrimeSeq

/-! ### The statements of `Challenge.lean` -/

namespace Main

/-- **Main theorem** (sharp form): `liminf q n / n² ≥ 255255 / (295318 + G)`. -/
theorem ofReal_le_liminf (q : ℕ → ℕ) (hmono : StrictMono q)
    (h : ∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) :
    ENNReal.ofReal (255255 / (295318 + G)) ≤
      liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop :=
  (IsConvexPrimeSeq.of_forall hmono h).ofReal_le_liminf

/-- **Main theorem**: `liminf q n / n² > 0.864289`. -/
theorem liminf_gt (q : ℕ → ℕ) (hmono : StrictMono q)
    (h : ∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) :
    liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop > 0.864289 := by
  refine lt_of_lt_of_le ?_ (ofReal_le_liminf q hmono h)
  rw [show (0.864289 : ℝ≥0∞) = ((0.864289 : ℝ≥0) : ℝ≥0∞) from rfl, ENNReal.ofReal,
    ENNReal.coe_lt_coe, Real.lt_toNNReal_iff_coe_lt]
  simpa using lt_ratio

/-- **Main theorem** (eventual form): `q n > 0.864289 n²` for all sufficiently large `n`. -/
theorem eventually_lt (q : ℕ → ℕ) (hmono : StrictMono q)
    (h : ∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) :
    ∀ᶠ n : ℕ in atTop, (0.864289 : ℝ) * n ^ 2 < q n :=
  (IsConvexPrimeSeq.of_forall hmono h).eventually_mul_sq_lt lt_ratio

/-- **Richter's theorem**: `liminf q n / n² > 0.352`. -/
theorem liminf_gt_richter (q : ℕ → ℕ) (hmono : StrictMono q)
    (h : ∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) :
    liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop > 0.352 := by
  refine lt_trans ?_ (liminf_gt q hmono h)
  rw [show (0.352 : ℝ≥0∞) = ((0.352 : ℝ≥0) : ℝ≥0∞) from rfl,
    show (0.864289 : ℝ≥0∞) = ((0.864289 : ℝ≥0) : ℝ≥0∞) from rfl, ENNReal.coe_lt_coe]
  norm_num

end Main

end Erdos455
