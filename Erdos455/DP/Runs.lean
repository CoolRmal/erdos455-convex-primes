/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.DP.Spec
import Erdos455.DP.Step

/-!
# Runs of units in arithmetic progressions

A run `r + d, …, r + m d` of units modulo `M` starting at a unit `r` has length `m ≤ p - 2`
for every prime `p ∣ M` not dividing `d` (Lemma 8 of the paper): otherwise the `p` numbers
`r + j d`, `0 ≤ j ≤ p - 1`, are pairwise incongruent modulo `p`, so one of them is divisible by
`p`. For a gap `d ≡ 2 i [MOD M]` with `0 < i < M`, this gives `m ≤ runBound i`.

## Main statements

* `Erdos455.IsRun.add_two_le`: Lemma 8.
* `Erdos455.IsRun.le_runBound`: the bound used by the value iteration.
-/

namespace Erdos455

/-- A prime dividing a number and `M` contradicts coprimality with `M`. -/
theorem not_coprime_of_dvd {p a : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hpa : p ∣ a) :
    ¬Nat.Coprime a M :=
  fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h hpa hpM)

/-- **Lemma 8**: a run of units modulo `M` starting at a unit has length at most `p - 2` for
every prime `p ∣ M` not dividing the difference. -/
theorem IsRun.add_two_le {p d r m : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hpd : ¬p ∣ d)
    (hr : Nat.Coprime r M) (h : IsRun d r m) : m + 2 ≤ p := by
  have := Fact.mk hp
  by_contra hlt
  have hd : (d : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  set j := (-(r : ZMod p) * (d : ZMod p)⁻¹).val with hj
  have hjp : j < p := ZMod.val_lt _
  have hjd : (j : ZMod p) * d = -r := by
    rw [hj, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hd, mul_one]
  have hdvd : p ∣ r + j * d := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hjd]
    exact add_neg_cancel _
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0, zero_mul, add_zero] at hdvd
    exact not_coprime_of_dvd hp hpM hdvd hr
  · exact not_coprime_of_dvd hp hpM hdvd (h j hpos (by omega))

/-- For an odd prime `p ∣ M` and `d ≡ 2 i [MOD M]`, `p ∣ d ↔ p ∣ i`. -/
theorem dvd_iff_of_mod_eq {p d i : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpM : p ∣ M)
    (hd : d % M = 2 * i % M) : p ∣ d ↔ p ∣ i := by
  have hmod : d % p = 2 * i % p := by
    rw [← Nat.mod_mod_of_dvd d hpM, hd, Nat.mod_mod_of_dvd _ hpM]
  rw [Nat.dvd_iff_mod_eq_zero, hmod, ← Nat.dvd_iff_mod_eq_zero]
  exact (Nat.Coprime.dvd_mul_left
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)).trans Iff.rfl

theorem runBound_eq (i : ℕ) : DP.runBound i =
    if ¬3 ∣ i then 1 else if ¬5 ∣ i then 3 else if ¬7 ∣ i then 5 else if ¬11 ∣ i then 9
    else if ¬13 ∣ i then 11 else 15 := by
  simp only [DP.runBound, Nat.dvd_iff_mod_eq_zero]
  split_ifs <;> simp_all

/-- If `3, 5, 7, 11, 13` all divide `0 < i < M`, then `17 ∤ i`. -/
theorem not_seventeen_dvd {i : ℕ} (hi : 0 < i) (hiM : i < M) (h3 : 3 ∣ i) (h5 : 5 ∣ i)
    (h7 : 7 ∣ i) (h11 : 11 ∣ i) (h13 : 13 ∣ i) : ¬17 ∣ i := by
  intro h17
  have h15 : 3 * 5 ∣ i := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5
  have h105 : 3 * 5 * 7 ∣ i := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h15 h7
  have h1155 : 3 * 5 * 7 * 11 ∣ i := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h105 h11
  have h15015 : 3 * 5 * 7 * 11 * 13 ∣ i :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1155 h13
  have hM : 3 * 5 * 7 * 11 * 13 * 17 ∣ i :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h15015 h17
  exact absurd hiM (not_lt.mpr (M_eq ▸ Nat.le_of_dvd hi hM))

/-- A run of units along a gap `d ≡ 2 i [MOD M]`, `0 < i < M`, has length at most
`runBound i`. -/
theorem IsRun.le_runBound {i d r m : ℕ} (hi : 0 < i) (hiM : i < M) (hd : d % M = 2 * i % M)
    (hr : Nat.Coprime r M) (h : IsRun d r m) : m ≤ DP.runBound i := by
  have key : ∀ p, p.Prime → p ≠ 2 → p ∣ M → ¬p ∣ i → m + 2 ≤ p := fun p hp hp2 hpM hpi =>
    h.add_two_le hp hpM (fun hpd => hpi ((dvd_iff_of_mod_eq hp hp2 hpM hd).mp hpd)) hr
  rw [runBound_eq]
  by_cases h3 : 3 ∣ i
  swap
  · rw [ite_eq_left h3]; have := key 3 Nat.prime_three (by norm_num) (by norm_num [M]) h3; omega
  rw [ite_eq_right (not_not.mpr h3)]
  by_cases h5 : 5 ∣ i
  swap
  · rw [ite_eq_left h5]; have := key 5 (by norm_num) (by norm_num) (by norm_num [M]) h5; omega
  rw [ite_eq_right (not_not.mpr h5)]
  by_cases h7 : 7 ∣ i
  swap
  · rw [ite_eq_left h7]; have := key 7 (by norm_num) (by norm_num) (by norm_num [M]) h7; omega
  rw [ite_eq_right (not_not.mpr h7)]
  by_cases h11 : 11 ∣ i
  swap
  · rw [ite_eq_left h11]; have := key 11 (by norm_num) (by norm_num) (by norm_num [M]) h11
    omega
  rw [ite_eq_right (not_not.mpr h11)]
  by_cases h13 : 13 ∣ i
  swap
  · rw [ite_eq_left h13]; have := key 13 (by norm_num) (by norm_num) (by norm_num [M]) h13
    omega
  rw [ite_eq_right (not_not.mpr h13)]
  have := key 17 (by norm_num) (by norm_num) (by norm_num [M])
    (not_seventeen_dvd hi hiM h3 h5 h7 h11 h13)
  omega

end Erdos455
