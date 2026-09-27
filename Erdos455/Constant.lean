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

## Main definitions

* `Erdos455.largePrimeProd n`: the product `p'₁ ⋯ p'ₙ` of the first `n` primes `≥ 19`.
* `Erdos455.summandG i`: the `i`-th term `(p'ᵢ₊₂ - p'ᵢ₊₁) / (p'₁ ⋯ p'ᵢ₊₁)` of the series `G`.

## Main statements

* `Erdos455.summable_G`: the series defining `G` converges.
* `Erdos455.sum_leastNonDivisor_two_mul_M_le`: `∑_{j = 1}^{K} (P(2 M j) - 2) ≤ G K`.
* `Erdos455.G_lt_bound`, `Erdos455.lt_G_bound`: `17.2244 < G < 17.2245`.

## Implementation notes

Lemma 14 is proved by a layer-cake decomposition: `P(2 M j)` is the first `p'ₖ` not dividing
`j`, so `P(2 M j) - 2 = 17 + ∑_{i : p'₁ ⋯ p'ᵢ ∣ j} (p'ᵢ₊₁ - p'ᵢ)`, and there are at most
`K / (p'₁ ⋯ p'ᵢ)` multiples of `p'₁ ⋯ p'ᵢ` in `[1, K]`. Both Lemma 15 and the convergence of
the series rest on Bertrand's postulate `p'ᵢ₊₁ ≤ 2 p'ᵢ`, which bounds the `i`-th term by
`1 / (p'₁ ⋯ p'ᵢ₋₁) ≤ 19⁻⁽ⁱ⁻¹⁾`.
-/

namespace Erdos455

open Finset

/-! ### The primes that are at least `19` -/

/-- There are infinitely many primes that are at least `19`. -/
theorem infinite_setOf_prime_and_nineteen_le : {p : ℕ | p.Prime ∧ 19 ≤ p}.Infinite :=
  Set.infinite_of_forall_exists_gt fun a => by
    obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (a + 19)
    exact ⟨p, ⟨hp, by omega⟩, by omega⟩

/-- `largePrime i` is prime. -/
theorem largePrime_prime (i : ℕ) : (largePrime i).Prime :=
  (Nat.nth_mem_of_infinite infinite_setOf_prime_and_nineteen_le i).1

/-- `largePrime i` is at least `19`. -/
theorem nineteen_le_largePrime (i : ℕ) : 19 ≤ largePrime i :=
  (Nat.nth_mem_of_infinite infinite_setOf_prime_and_nineteen_le i).2

/-- The sequence `largePrime` is strictly increasing. -/
theorem largePrime_strictMono : StrictMono largePrime :=
  Nat.nth_strictMono infinite_setOf_prime_and_nineteen_le

/-- Every prime `p ≥ 19` is a `largePrime`, namely `largePrime i` where `i` is the number of
primes in `[19, p)`. -/
theorem largePrime_count {p : ℕ} (hp : p.Prime) (h : 19 ≤ p) :
    largePrime (Nat.count (fun p => p.Prime ∧ 19 ≤ p) p) = p :=
  Nat.nth_count (p := fun p => p.Prime ∧ 19 ≤ p) ⟨hp, h⟩

/-- A criterion to compute `largePrime i`: if `p ≥ 19` is prime and there are exactly `i`
primes in `[19, p)`, then `largePrime i = p`. -/
theorem largePrime_eq_of_count {i p : ℕ} (hp : p.Prime) (h19 : 19 ≤ p)
    (h : Nat.count (fun p => p.Prime ∧ 19 ≤ p) p = i) : largePrime i = p :=
  h ▸ largePrime_count hp h19

theorem largePrime_zero : largePrime 0 = 19 :=
  largePrime_eq_of_count (by norm_num) le_rfl (by decide)

/-- `largePrime 1 = 23`. -/
theorem largePrime_one : largePrime 1 = 23 :=
  largePrime_eq_of_count (by norm_num) (by norm_num) (by decide)

/-- `largePrime 2 = 29`. -/
theorem largePrime_two : largePrime 2 = 29 :=
  largePrime_eq_of_count (by norm_num) (by norm_num) (by decide)

/-- `largePrime 3 = 31`. -/
theorem largePrime_three : largePrime 3 = 31 :=
  largePrime_eq_of_count (by norm_num) (by norm_num) (by decide)

/-- `largePrime 4 = 37`. -/
theorem largePrime_four : largePrime 4 = 37 :=
  largePrime_eq_of_count (by norm_num) (by norm_num) (by decide)

/-- `largePrime (i + 1)` is the least prime above `largePrime i`. -/
theorem largePrime_succ_le_of_lt {i q : ℕ} (hq : q.Prime) (h : largePrime i < q) :
    largePrime (i + 1) ≤ q := by
  have h19 := (nineteen_le_largePrime i).trans h.le
  rw [← largePrime_count hq h19] at h ⊢
  exact largePrime_strictMono.monotone (largePrime_strictMono.lt_iff_lt.mp h)

/-- **Bertrand's postulate** for the primes `≥ 19`: `p'ᵢ₊₁ ≤ 2 p'ᵢ`. -/
theorem largePrime_succ_le_two_mul (i : ℕ) : largePrime (i + 1) ≤ 2 * largePrime i := by
  obtain ⟨q, hq, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (largePrime i) (largePrime_prime i).ne_zero
  exact (largePrime_succ_le_of_lt hq hlt).trans hle

/-! ### Products of the primes that are at least `19` -/

/-- The product `p'₁ ⋯ p'ₙ = ∏_{i < n} largePrime i` of the first `n` primes that are at least
`19`. -/
noncomputable def largePrimeProd (n : ℕ) : ℕ :=
  ∏ i ∈ range n, largePrime i

theorem largePrimeProd_zero : largePrimeProd 0 = 1 :=
  prod_range_zero _

theorem largePrimeProd_succ (n : ℕ) :
    largePrimeProd (n + 1) = largePrimeProd n * largePrime n :=
  prod_range_succ _ _

theorem largePrimeProd_pos (n : ℕ) : 0 < largePrimeProd n :=
  prod_pos fun i _ => (largePrime_prime i).pos

/-- `p'₁ ⋯ p'ₙ ⋅ 19 ^ m ≤ p'₁ ⋯ p'ₙ₊ₘ`. -/
theorem largePrimeProd_mul_pow_le (n m : ℕ) :
    largePrimeProd n * 19 ^ m ≤ largePrimeProd (n + m) := by
  rw [largePrimeProd, largePrimeProd, prod_range_add]
  gcongr
  simpa using pow_card_le_prod (range m) _ 19 fun i _ => nineteen_le_largePrime (n + i)

/-- `n < p'₁ ⋯ p'ₙ`. -/
theorem lt_largePrimeProd (n : ℕ) : n < largePrimeProd n := by
  have := largePrimeProd_mul_pow_le 0 n
  rw [largePrimeProd_zero, one_mul, zero_add] at this
  exact (Nat.lt_pow_self (by norm_num)).trans_le this

/-- If each of `p'₁, …, p'ₙ` divides `j`, then so does their product. -/
theorem largePrimeProd_dvd {n j : ℕ} (h : ∀ i < n, largePrime i ∣ j) :
    largePrimeProd n ∣ j := by
  induction n with
  | zero => simp [largePrimeProd_zero]
  | succ n ih =>
    rw [largePrimeProd_succ]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (ih fun i hi => h i (by omega)) (h n (by omega))
    refine Nat.Coprime.prod_left fun i hi => ?_
    rw [Nat.coprime_primes (largePrime_prime i) (largePrime_prime n)]
    exact largePrime_strictMono.injective.ne (mem_range.1 hi).ne

/-! ### The least prime not dividing `2 M j` -/

/-- Every prime `p < 19` divides `2 M`. -/
theorem dvd_two_mul_M {p : ℕ} (hp : p.Prime) (h : p < 19) : p ∣ 2 * M := by
  revert hp
  interval_cases p <;> norm_num [M]

/-- The primes `p'ᵢ ≥ 19` are coprime to `2 M = 2 ⋅ 3 ⋅ 5 ⋅ 7 ⋅ 11 ⋅ 13 ⋅ 17`. -/
theorem largePrime_coprime_two_mul_M (i : ℕ) : (largePrime i).Coprime (2 * M) := by
  have h19 := nineteen_le_largePrime i
  rw [M_eq]
  repeat' apply Nat.Coprime.mul_right
  all_goals exact Nat.coprime_of_lt_prime (by norm_num) (by omega) (largePrime_prime i)

/-- For `j ≠ 0`, `P(2 M j) ≥ 19`, since every prime below `19` divides `2 M`. -/
theorem nineteen_le_leastNonDivisor {j : ℕ} (hj : j ≠ 0) : 19 ≤ leastNonDivisor (2 * M * j) := by
  by_contra h
  exact not_dvd_leastNonDivisor (by simp [M, hj])
    ((dvd_two_mul_M (leastNonDivisor_prime (2 * M * j)) (by omega)).mul_right j)

/-- For `j ≠ 0`, if `P(2 M j) = p'ₖ`, then `p'₁ ⋯ p'ₙ` divides `j` if and only if `n ≤ k`. -/
theorem largePrimeProd_dvd_iff {j k : ℕ} (hj : j ≠ 0)
    (hk : largePrime k = leastNonDivisor (2 * M * j)) (n : ℕ) :
    largePrimeProd n ∣ j ↔ n ≤ k := by
  have hd : 2 * M * j ≠ 0 := by simp [M, hj]
  refine ⟨fun h => ?_, fun h => largePrimeProd_dvd fun i hi => ?_⟩
  · by_contra hnk
    refine not_dvd_leastNonDivisor hd (hk ▸ Dvd.dvd.mul_left ?_ _)
    exact (dvd_prod_of_mem _ (mem_range.2 (by omega))).trans h
  · refine (largePrime_coprime_two_mul_M i).dvd_of_dvd_mul_left ?_
    exact dvd_of_lt_leastNonDivisor hd (largePrime_prime i) (hk ▸ largePrime_strictMono (by omega))

/-- **Layer-cake formula**: for `j ≠ 0` and `N` such that `p'₁ ⋯ p'_N ∤ j`,
`P(2 M j) - 2 = 17 + ∑_{i < N, p'₁ ⋯ p'ᵢ₊₁ ∣ j} (p'ᵢ₊₂ - p'ᵢ₊₁)`. -/
theorem leastNonDivisor_two_mul_M_sub_two {j N : ℕ} (hj : j ≠ 0) (hN : ¬largePrimeProd N ∣ j) :
    (leastNonDivisor (2 * M * j) : ℝ) - 2 = 17 + ∑ i ∈ range N,
      if largePrimeProd (i + 1) ∣ j then (largePrime (i + 1) : ℝ) - largePrime i else 0 := by
  obtain ⟨k, hk⟩ : ∃ k, largePrime k = leastNonDivisor (2 * M * j) :=
    ⟨_, largePrime_count (leastNonDivisor_prime _) (nineteen_le_leastNonDivisor hj)⟩
  rw [largePrimeProd_dvd_iff hj hk, not_le] at hN
  simp_rw [largePrimeProd_dvd_iff hj hk, ← sum_filter]
  rw [show (range N).filter (· + 1 ≤ k) = range k by ext; simp; omega,
    sum_range_sub (fun i => (largePrime i : ℝ)), hk, largePrime_zero]
  push_cast
  ring

/-! ### The series `G` -/

/-- The `i`-th term `(p'ᵢ₊₂ - p'ᵢ₊₁) / (p'₁ ⋯ p'ᵢ₊₁)` of the series defining `G`. -/
noncomputable def summandG (i : ℕ) : ℝ :=
  ((largePrime (i + 1) : ℝ) - largePrime i) / ∏ j ∈ range (i + 1), (largePrime j : ℝ)

theorem G_eq : G = 17 + ∑' i, summandG i :=
  rfl

theorem summandG_eq (i : ℕ) :
    summandG i = ((largePrime (i + 1) : ℝ) - largePrime i) / largePrimeProd (i + 1) := by
  rw [summandG, largePrimeProd, Nat.cast_prod]

theorem summandG_nonneg (i : ℕ) : 0 ≤ summandG i := by
  have : (largePrime i : ℝ) ≤ largePrime (i + 1) := by
    exact_mod_cast (largePrime_strictMono i.lt_succ_self).le
  rw [summandG_eq]
  exact div_nonneg (by linarith) (Nat.cast_nonneg _)

/-- By Bertrand's postulate, `summandG (n + i) ≤ (p'₁ ⋯ p'ₙ)⁻¹ ⋅ 19⁻ⁱ`. -/
theorem summandG_add_le (n i : ℕ) :
    summandG (n + i) ≤ (largePrimeProd n : ℝ)⁻¹ * 19⁻¹ ^ i := by
  set m := n + i
  have hp : (0 : ℝ) < largePrime m := by exact_mod_cast (largePrime_prime m).pos
  have hB : (largePrime (m + 1) : ℝ) - largePrime m ≤ largePrime m := by
    have := largePrime_succ_le_two_mul m
    rw [sub_le_iff_le_add]
    exact_mod_cast (by omega : largePrime (m + 1) ≤ largePrime m + largePrime m)
  have hprod : (largePrimeProd n : ℝ) * 19 ^ i ≤ largePrimeProd m := by
    exact_mod_cast largePrimeProd_mul_pow_le n i
  have hn : (0 : ℝ) < largePrimeProd n := by exact_mod_cast largePrimeProd_pos n
  calc summandG m
      = ((largePrime (m + 1) : ℝ) - largePrime m) / (largePrimeProd m * largePrime m) := by
        rw [summandG_eq, largePrimeProd_succ, Nat.cast_mul]
    _ ≤ largePrime m / (largePrimeProd m * largePrime m) := by gcongr
    _ = (largePrimeProd m : ℝ)⁻¹ := by field_simp
    _ ≤ ((largePrimeProd n : ℝ) * 19 ^ i)⁻¹ := by gcongr
    _ = (largePrimeProd n : ℝ)⁻¹ * 19⁻¹ ^ i := by rw [mul_inv, inv_pow]

/-- The terms of the series defining `G` are summable. -/
theorem summable_G :
    Summable fun i : ℕ => ((largePrime (i + 1) : ℝ) - largePrime i) /
      ∏ j ∈ Finset.range (i + 1), (largePrime j : ℝ) := by
  show Summable summandG
  refine Summable.of_nonneg_of_le summandG_nonneg (fun i => ?_)
    (summable_geometric_of_lt_one (r := 19⁻¹) (by norm_num) (by norm_num))
  simpa [largePrimeProd_zero] using summandG_add_le 0 i

/-- **Lemma 14**: `∑_{j = 1}^{K} (P(2 M j) - 2) ≤ G K`, where `P(d)` is the least prime not
dividing `d`. -/
theorem sum_leastNonDivisor_two_mul_M_le (K : ℕ) :
    ∑ j ∈ Finset.Icc 1 K, ((leastNonDivisor (2 * M * j) : ℝ) - 2) ≤ G * K := by
  have hK (j) (hj : j ∈ Icc 1 K) : ¬largePrimeProd K ∣ j := fun h => by
    have := Nat.le_of_dvd (by simp at hj; omega) h
    have := lt_largePrimeProd K
    simp at hj
    omega
  rw [sum_congr rfl fun j hj => leastNonDivisor_two_mul_M_sub_two (by simp at hj; omega) (hK j hj),
    sum_add_distrib, sum_comm]
  simp_rw [← sum_filter, sum_const, nsmul_eq_mul]
  rw [show Icc 1 K = Ioc 0 K from rfl]
  simp_rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.card_Ioc, Nat.sub_zero]
  have h1 : ∑ i ∈ range K, ((K / largePrimeProd (i + 1) : ℕ) : ℝ) *
      ((largePrime (i + 1) : ℝ) - largePrime i) ≤ K * ∑ i ∈ range K, summandG i := by
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    have hc : (0 : ℝ) ≤ (largePrime (i + 1) : ℝ) - largePrime i := by
      rw [sub_nonneg]
      exact_mod_cast (largePrime_strictMono i.lt_succ_self).le
    calc ((K / largePrimeProd (i + 1) : ℕ) : ℝ) * ((largePrime (i + 1) : ℝ) - largePrime i)
        ≤ (K / largePrimeProd (i + 1) : ℝ) * ((largePrime (i + 1) : ℝ) - largePrime i) := by
          gcongr
          exact Nat.cast_div_le
      _ = K * summandG i := by
          rw [summandG_eq]
          ring
  have h2 : ∑ i ∈ range K, summandG i ≤ ∑' i, summandG i :=
    (summable_G : Summable summandG).sum_le_tsum _ fun i _ => summandG_nonneg i
  have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) K)
  rw [G_eq]
  linarith

/-- The first four terms of the series defining `G`. -/
theorem sum_range_four_summandG :
    ∑ i ∈ range 4, summandG i = 4 / 19 + 6 / 437 + 2 / 12673 + 6 / 392863 := by
  simp [sum_range_succ, summandG, prod_range_succ, largePrime_zero, largePrime_one,
    largePrime_two, largePrime_three, largePrime_four]
  norm_num

/-- **Lemma 15** (upper bound). -/
theorem G_lt_bound : G < 17.2245 := by
  have hs : Summable summandG := summable_G
  have htail : ∑' i, summandG (i + 4) ≤ ∑' i, (largePrimeProd 4 : ℝ)⁻¹ * 19⁻¹ ^ i := by
    refine ((summable_nat_add_iff 4).mpr hs).tsum_le_tsum (fun i => ?_)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
    rw [add_comm]
    exact summandG_add_le 4 i
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at htail
  have h4 : largePrimeProd 4 = 392863 := by
    simp [largePrimeProd, prod_range_succ, largePrime_zero, largePrime_one, largePrime_two,
      largePrime_three]
  rw [G_eq, ← hs.sum_add_tsum_nat_add 4, sum_range_four_summandG]
  rw [h4] at htail
  norm_num at htail ⊢
  linarith

/-- **Lemma 15** (lower bound). -/
theorem lt_G_bound : 17.2244 < G := by
  have := (summable_G : Summable summandG).sum_le_tsum (range 4) fun i _ => summandG_nonneg i
  rw [sum_range_four_summandG] at this
  rw [G_eq]
  norm_num at this ⊢
  linarith

end Erdos455
