/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.LeastNonDivisor

/-!
# Arithmetic progressions of primes

Two elementary facts about the least prime `P(d)` not dividing `d` (Section 2 of the paper).

* **Lemma 3**: if `a, a + d, …, a + k d` are all prime, `d ≥ 2` and `k ≥ P(d) - 1`, then
  `a = P(d)` and `k ≤ P(d) - 1`. Indeed, one of the first `P(d)` terms is divisible by `P(d)`,
  hence equal to it, and this term can only be the first one.
* A form of **Lemma 2(b)**: all the primes below `P(d)` divide `d`, so a set `S` of values of
  `P` on `[1, D]` satisfies `2 ^ |S| ≤ 2 D`. This bounds the number of exceptional gaps in
  `Erdos455.FreeGaps`.

## Main statements

* `Erdos455.exists_lt_prime_dvd_add_mul`: one of `a, a + d, …, a + (p - 1) d` is divisible by
  the prime `p ∤ d`.
* `Erdos455.eq_leastNonDivisor_of_prime_add_mul`: Lemma 3.
* `Erdos455.two_pow_card_le_of_leastNonDivisor`: `2 ^ |S| ≤ 2 D` for a set `S` of values of `P`
  on `[1, D]`.
-/

namespace Erdos455

/-- If the prime `p` does not divide `d`, then `p` divides one of the `p` numbers `a + j d`,
`0 ≤ j < p`. -/
theorem exists_lt_prime_dvd_add_mul {p d : ℕ} (hp : p.Prime) (hpd : ¬p ∣ d) (a : ℕ) :
    ∃ j < p, p ∣ a + j * d := by
  have := Fact.mk hp
  have hd : (d : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  refine ⟨(-(a : ZMod p) / d).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, div_mul_cancel₀ _ hd]
  exact add_neg_cancel _

/-- `P(2) = 3`. -/
theorem leastNonDivisor_two : leastNonDivisor 2 = 3 := by
  refine le_antisymm (leastNonDivisor_le_of_not_dvd two_ne_zero Nat.prime_three (by decide)) ?_
  have h2 := (leastNonDivisor_prime 2).two_le
  have hne : leastNonDivisor 2 ≠ 2 := fun h =>
    not_dvd_leastNonDivisor two_ne_zero (h.symm ▸ dvd_rfl : leastNonDivisor 2 ∣ 2)
  omega

/-- The first `P(d)` terms of a progression of primes with difference `d ≥ 2` can only contain
the prime `P(d)` as their first term. -/
theorem leastNonDivisor_lt_add {a d : ℕ} (ha : a.Prime) (hd : 2 ≤ d) :
    leastNonDivisor d < a + d := by
  have ha2 := ha.two_le
  rcases hd.eq_or_lt with rfl | hd
  · rw [leastNonDivisor_two]
    omega
  · have := leastNonDivisor_le_sub_one hd
    omega

/-- **Lemma 3** (arithmetic progressions of primes). Let `d ≥ 2` and `p = P(d)` be the least
prime not dividing `d`. If `a, a + d, …, a + k d` are all prime and `k ≥ p - 1`, then `a = p`
and `k ≤ p - 1`. -/
theorem eq_leastNonDivisor_of_prime_add_mul {a d k : ℕ} (hd : 2 ≤ d)
    (hprime : ∀ j ≤ k, (a + j * d).Prime) (hk : leastNonDivisor d - 1 ≤ k) :
    a = leastNonDivisor d ∧ k ≤ leastNonDivisor d - 1 := by
  set p := leastNonDivisor d
  have hd0 : d ≠ 0 := by omega
  have hp : p.Prime := leastNonDivisor_prime d
  have hpd : ¬p ∣ d := not_dvd_leastNonDivisor hd0
  have ha : a.Prime := by simpa using hprime 0 (Nat.zero_le _)
  obtain ⟨j, hjp, hdvd⟩ := exists_lt_prime_dvd_add_mul hp hpd a
  have hj : a + j * d = p :=
    ((Nat.prime_dvd_prime_iff_eq hp (hprime j (by omega))).mp hdvd).symm
  have hj0 : j = 0 := by
    by_contra hj0
    have : a + d ≤ a + j * d := Nat.add_le_add_left (Nat.le_mul_of_pos_left d (by omega)) a
    have := leastNonDivisor_lt_add ha hd
    omega
  subst hj0
  simp only [zero_mul, add_zero] at hj
  refine ⟨hj, Nat.le_sub_one_of_lt (lt_of_not_ge fun hpk => ?_)⟩
  have hmul : a + p * d = p * (1 + d) := by rw [hj]; ring
  exact Nat.not_prime_mul hp.one_lt.ne' (by omega) (hmul ▸ hprime p hpk)

/-- A form of **Lemma 2(b)**. Every prime below `P(d)` divides `d`, so if `S` is a set of values
of `P` on `[1, D]`, then the product of all elements of `S` but the largest divides some
`d ≤ D`; hence `2 ^ |S| ≤ 2 D`. -/
theorem two_pow_card_le_of_leastNonDivisor {S : Finset ℕ} {D : ℕ} (hD : 0 < D)
    (hS : ∀ p ∈ S, ∃ d, d ≠ 0 ∧ d ≤ D ∧ leastNonDivisor d = p) :
    2 ^ S.card ≤ 2 * D := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.card_empty, pow_zero]
    omega
  set p := S.max' hne
  obtain ⟨d, hd0, hdD, hdp⟩ := hS p (S.max'_mem hne)
  have hprime : ∀ s ∈ S, s.Prime := fun s hs => by
    obtain ⟨e, -, -, rfl⟩ := hS s hs
    exact leastNonDivisor_prime e
  have hdvd : ∏ s ∈ S.erase p, s ∣ d := by
    refine Finset.prod_primes_dvd d (fun s hs => (hprime s (Finset.mem_of_mem_erase hs)).prime)
      fun s hs => dvd_of_lt_leastNonDivisor hd0 (hprime s (Finset.mem_of_mem_erase hs)) ?_
    rw [hdp]
    exact lt_of_le_of_ne (S.le_max' s (Finset.mem_of_mem_erase hs)) (Finset.ne_of_mem_erase hs)
  have hpow : 2 ^ (S.erase p).card ≤ ∏ s ∈ S.erase p, s :=
    Finset.pow_card_le_prod _ _ _ fun s hs => (hprime s (Finset.mem_of_mem_erase hs)).two_le
  have hcard : (S.erase p).card + 1 = S.card := Finset.card_erase_add_one (S.max'_mem hne)
  rw [← hcard, pow_succ]
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hdvd
  omega

end Erdos455
