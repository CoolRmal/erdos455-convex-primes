/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.ConvexSeq
import Erdos455.DP.Certificate

/-!
# One period of gap values

The even gap values between `2 M k` and `2 M (k + 1)` form one period of the dynamic program:
for `1 ≤ i < M`, the run of gaps `d = 2 M k + 2 i` (with `d ≡ 2 i [MOD M]`) leads from the
residue of `q (first q d)` to that of `q (first q (d + 2))`, through terms coprime to `M`. The
certificate `Erdos455.exists_potential` (Proposition 11) therefore bounds the total length of
these runs by `growth = Λ` up to a bounded potential (Corollary 12), and the bounds telescope
over the periods.

## Main statements

* `Erdos455.IsConvexPrimeSeq.periodPath`: the runs of the `k`-th period form a `PeriodPath`.
* `Erdos455.IsConvexPrimeSeq.exists_potential_bound`: Corollary 12.
* `Erdos455.IsConvexPrimeSeq.sum_period_le`: the telescoped bound
  `∑_{k < K} ∑_{i = 1}^{M - 1} m(2 M k + 2 i) ≤ Λ K + 255`.
-/

namespace Erdos455

namespace IsConvexPrimeSeq

variable {q : ℕ → ℕ} (hq : IsConvexPrimeSeq q)
include hq

/-- The run of the even gap `2 e` leads from `q (first q (2 e))` to `q (first q (2 e + 2))`. -/
theorem q_first_two_mul_add_two (e : ℕ) :
    q (first q (2 * e + 2)) = q (first q (2 * e)) + runLength q (2 * e) * (2 * e) := by
  rw [hq.first_two_mul_add_two, hq.q_first_succ]

/-- The runs of the gaps `2 M k + 2 i`, `1 ≤ i < M`, form a path of runs along one period of
gap values, from the residue of `q (first q (2 M k + 2))` to that of `q (first q (2 M (k + 1)))`.
-/
theorem periodPath (k : ℕ) :
    PeriodPath (fun i => 2 * M * k + 2 * i) (fun i => q (first q (2 * M * k + 2 * i + 2)))
      (fun i => runLength q (2 * M * k + 2 * i)) where
  coprime_zero := hq.coprime_M (hq.start_le_first _)
  gap_mod i _ _ := by
    rw [show 2 * M * k + 2 * i = 2 * i + M * (2 * k) by ring, Nat.add_mul_mod_self_left]
  isRun i hi _ j _ hj := by
    rw [show 2 * M * k + 2 * (i - 1) + 2 = 2 * M * k + 2 * i by omega]
    exact hq.coprime_add_mul hj
  step i hi _ := by
    rw [show 2 * M * k + 2 * (i - 1) + 2 = 2 * (M * k + i) by rw [mul_assoc]; omega,
      show 2 * M * k + 2 * i + 2 = 2 * (M * k + i) + 2 by ring,
      show 2 * M * k + 2 * i = 2 * (M * k + i) by ring]
    exact hq.q_first_two_mul_add_two _

/-- **Corollary 12** (one period). There is a potential `φ` with values in `[0, 255]` such that
for every `k`, with `σ k = q (first q (2 M k + 2))`,
`φ (σ k) + ∑_{i = 1}^{M - 1} m(2 M k + 2 i) ≤ φ (σ (k + 1)) + Λ`. -/
theorem exists_potential_bound :
    ∃ φ : ℕ → ℕ, (∀ r, φ r ≤ 255) ∧ ∀ k,
      φ (q (first q (2 * M * k + 2))) + ∑ i ∈ Finset.Ico 1 M, runLength q (2 * M * k + 2 * i) ≤
        φ (q (first q (2 * M * (k + 1) + 2))) + growth := by
  obtain ⟨φ, hφ, hmod, hpath⟩ := exists_potential
  refine ⟨φ, hφ, fun k => ?_⟩
  have h := hpath _ _ _ (hq.periodPath k)
  simp only [mul_zero, add_zero] at h
  -- The last run of the period, of the gap `2 M (k + 1) ≡ 0 [MOD M]`, preserves the residue.
  have hlast : φ (q (first q (2 * M * (k + 1) + 2))) =
      φ (q (first q (2 * M * k + 2 * (M - 1) + 2))) := by
    have hM : 2 * M * k + 2 * (M - 1) + 2 = 2 * (M * (k + 1)) := by
      have : 1 ≤ M := by norm_num [M]
      rw [mul_assoc, mul_add_one]
      omega
    rw [hM, ← hmod, show 2 * M * (k + 1) = 2 * (M * (k + 1)) by ring,
      hq.q_first_two_mul_add_two, show runLength q (2 * (M * (k + 1))) * (2 * (M * (k + 1))) =
        M * (runLength q (2 * (M * (k + 1))) * (2 * (k + 1))) by ring, Nat.add_mul_mod_self_left,
      hmod]
  rw [hlast]
  exact h

/-- Corollary 12, telescoped over the first `K` periods:
`∑_{k < K} ∑_{i = 1}^{M - 1} m(2 M k + 2 i) ≤ Λ K + 255`. -/
theorem sum_period_le (K : ℕ) :
    ∑ k ∈ Finset.range K, ∑ i ∈ Finset.Ico 1 M, runLength q (2 * M * k + 2 * i) ≤
      growth * K + 255 := by
  obtain ⟨φ, hφ, hstep⟩ := hq.exists_potential_bound
  have key : ∀ K, φ (q (first q (2 * M * 0 + 2))) +
      ∑ k ∈ Finset.range K, ∑ i ∈ Finset.Ico 1 M, runLength q (2 * M * k + 2 * i) ≤
        φ (q (first q (2 * M * K + 2))) + growth * K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ← add_assoc]
      have := hstep K
      rw [mul_add_one growth K]
      omega
  have := key K
  have := hφ (q (first q (2 * M * K + 2)))
  omega

end IsConvexPrimeSeq

end Erdos455
