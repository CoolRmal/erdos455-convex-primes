/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.ConvexSeq
import Erdos455.Constant
import Erdos455.Progression

/-!
# The gaps divisible by `2 M`

On the gaps `d = 2 M j`, the dynamic program gives no information. Instead, the run of gaps `d`
is an arithmetic progression of primes, so by Lemma 3 its length `m(d)` is at most `P(d) - 2`,
except when it starts at the prime `P(d)` itself, in which case `m(d) = P(d) - 1`
(**Lemma 13**). The exceptional `j ∈ [1, K]` give distinct values `P(2 M j)` (they are values of
the increasing sequence `q`), so there are at most `log₂ (4 M K)` of them.

Combined with Lemma 14 (`Erdos455.sum_leastNonDivisor_two_mul_M_le`), this bounds
`∑_{j = 1}^{K} m(2 M j)` by `G K` plus the number of exceptional `j`.

## Main definitions

* `Erdos455.exceptional q K`: the `j ∈ [1, K]` with `m(2 M j) ≥ P(2 M j) - 1`.

## Main statements

* `Erdos455.IsConvexPrimeSeq.runLength_le_sub_one`: `m(d) ≤ P(d) - 1` for `d ≥ 2`.
* `Erdos455.IsConvexPrimeSeq.q_first_eq_of_le_runLength`: equality forces `q (first q d) = P(d)`.
* `Erdos455.IsConvexPrimeSeq.sum_runLength_two_mul_M_le`:
  `∑_{j = 1}^{K} m(2 M j) ≤ G K + #(exceptional q K)`.
* `Erdos455.IsConvexPrimeSeq.two_pow_card_exceptional_le`: `2 ^ #(exceptional q K) ≤ 4 M K`.
-/

namespace Erdos455

/-- The exceptional multiples of `2 M`: the `j ∈ [1, K]` such that the run of gaps `2 M j` has
length at least `P(2 M j) - 1` (Lemma 13 shows that it then starts at the prime `P(2 M j)`). -/
noncomputable def exceptional (q : ℕ → ℕ) (K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter fun j => leastNonDivisor (2 * M * j) - 1 ≤ runLength q (2 * M * j)

theorem mem_exceptional {q : ℕ → ℕ} {K j : ℕ} :
    j ∈ exceptional q K ↔
      (1 ≤ j ∧ j ≤ K) ∧ leastNonDivisor (2 * M * j) - 1 ≤ runLength q (2 * M * j) := by
  rw [exceptional, Finset.mem_filter, Finset.mem_Icc]

theorem two_le_two_mul_M_mul {j : ℕ} (hj : 1 ≤ j) : 2 ≤ 2 * M * j :=
  le_mul_of_le_of_one_le (le_mul_of_one_le_right zero_le_two (by norm_num [M])) hj

namespace IsConvexPrimeSeq

variable {q : ℕ → ℕ} (hq : IsConvexPrimeSeq q)
include hq

/-- **Lemma 13** (the exceptional case): if the run of gaps `d ≥ 2` has length at least
`P(d) - 1`, then it starts at the prime `P(d)`. -/
theorem q_first_eq_of_le_runLength {d : ℕ} (hd : 2 ≤ d)
    (h : leastNonDivisor d - 1 ≤ runLength q d) : q (first q d) = leastNonDivisor d :=
  (eq_leastNonDivisor_of_prime_add_mul hd (fun _ hj => hq.prime_add_mul hj) h).1

/-- **Lemma 13**: the run of gaps `d ≥ 2` has length at most `P(d) - 1`. -/
theorem runLength_le_sub_one {d : ℕ} (hd : 2 ≤ d) : runLength q d ≤ leastNonDivisor d - 1 := by
  by_cases h : leastNonDivisor d - 1 ≤ runLength q d
  · exact (eq_leastNonDivisor_of_prime_add_mul hd (fun _ hj => hq.prime_add_mul hj) h).2
  · omega

/-- **Lemma 13**, summed with Lemma 14: `∑_{j = 1}^{K} m(2 M j) ≤ G K + #(exceptional q K)`. -/
theorem sum_runLength_two_mul_M_le (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, runLength q (2 * M * j) : ℝ) ≤ G * K + (exceptional q K).card := by
  have hterm : ∀ j ∈ Finset.Icc 1 K, (runLength q (2 * M * j) : ℝ) ≤
      ((leastNonDivisor (2 * M * j) : ℝ) - 2) +
        if leastNonDivisor (2 * M * j) - 1 ≤ runLength q (2 * M * j) then 1 else 0 := by
    intro j hj
    have hd := two_le_two_mul_M_mul (Finset.mem_Icc.mp hj).1
    have hle := hq.runLength_le_sub_one hd
    have hP := (leastNonDivisor_prime (2 * M * j)).two_le
    split_ifs with h
    · have : runLength q (2 * M * j) + 1 ≤ leastNonDivisor (2 * M * j) := by omega
      have : (runLength q (2 * M * j) : ℝ) + 1 ≤ leastNonDivisor (2 * M * j) := by exact_mod_cast this
      linarith
    · have : runLength q (2 * M * j) + 2 ≤ leastNonDivisor (2 * M * j) := by omega
      have : (runLength q (2 * M * j) : ℝ) + 2 ≤ leastNonDivisor (2 * M * j) := by exact_mod_cast this
      linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_boole]
  exact add_le_add (sum_leastNonDivisor_two_mul_M_le K) le_rfl

/-- The exceptional runs start at increasing primes: `j ↦ P(2 M j)` is strictly increasing on the
exceptional set. -/
theorem strictMonoOn_exceptional (K : ℕ) :
    StrictMonoOn (fun j => leastNonDivisor (2 * M * j)) (exceptional q K) := by
  intro j hj j' hj' hlt
  rw [Finset.mem_coe, mem_exceptional] at hj hj'
  have hd := two_le_two_mul_M_mul hj.1.1
  have hd' := two_le_two_mul_M_mul hj'.1.1
  dsimp only
  rw [← hq.q_first_eq_of_le_runLength hd hj.2, ← hq.q_first_eq_of_le_runLength hd' hj'.2]
  refine hq.strictMono ?_
  have hpos : 1 ≤ runLength q (2 * M * j) := by
    have := (leastNonDivisor_prime (2 * M * j)).two_le
    omega
  have hmono : first q (2 * M * j + 1) ≤ first q (2 * M * j') := by
    refine hq.first_mono ?_
    have : 2 * M * j < 2 * M * j' := Nat.mul_lt_mul_of_pos_left hlt (by norm_num [M])
    omega
  have := hq.first_add_runLength (2 * M * j)
  omega

/-- The number of exceptional `j ∈ [1, K]` is at most `log₂ (4 M K)`. -/
theorem two_pow_card_exceptional_le {K : ℕ} (hK : 1 ≤ K) :
    2 ^ (exceptional q K).card ≤ 4 * M * K := by
  rw [← Finset.card_image_of_injOn (hq.strictMonoOn_exceptional K).injOn,
    show 4 * M * K = 2 * (2 * M * K) by ring]
  refine two_pow_card_le_of_leastNonDivisor (by norm_num [M]; omega) fun p hp => ?_
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
  rw [mem_exceptional] at hj
  exact ⟨2 * M * j, by have := two_le_two_mul_M_mul hj.1.1; omega,
    Nat.mul_le_mul_left _ hj.1.2, rfl⟩

end IsConvexPrimeSeq

end Erdos455
