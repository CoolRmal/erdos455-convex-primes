/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.Packed.Ops

/-!
# Periodic packed vectors

`rep b m n = ∑_{j < n} 2 ^ (b m j)` is the packed vector (fields of width `b`) with fields `1` at
the multiples of `m` below `m n` and `0` elsewhere. It has the closed form
`(2 ^ (b m n) - 1) / (2 ^ (b m) - 1)`, which the kernel evaluates with a few GMP operations; this
is how the packed constants of the value iteration are checked.

## Main statements

* `Erdos455.Packed.field_rep`: the fields of `rep b m n`.
* `Erdos455.Packed.rep_eq_div`: the closed form.
* `Erdos455.Packed.spec_unitInd`: the packed indicator `unitInd b R ps` of the numbers below `R`
  divisible by none of the numbers `ps`, computed from closed forms.
-/

namespace Erdos455.Packed

open Finset

/-- The packed vector with fields `1` at the multiples of `m` below `m n` and `0` elsewhere. -/
def rep (b m n : ℕ) : ℕ :=
  ∑ j ∈ range n, 2 ^ (b * m * j)

variable {b m n t : ℕ}

/-- The fields of a power `2 ^ (b k)`: a single `1` at field `k` (for `0 < b`). -/
theorem field_two_pow_mul (hb : 0 < b) (k t : ℕ) :
    field b (2 ^ (b * k)) t = if t = k then 1 else 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [testBit_field, Nat.testBit_two_pow]
  split_ifs with h
  · subst h
    by_cases hi : i = 0
    · simp [hi, hb]
    · have : (1 : ℕ).testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos
          (Nat.one_le_iff_ne_zero.mpr hi)))
      rw [this]
      by_cases hib : i < b
      · simp [hib]; omega
      · simp [hib]
  · rw [Nat.zero_testBit]
    by_cases hib : i < b
    · simp only [hib, decide_true, Bool.true_and, decide_eq_false_iff_not]
      intro heq
      have : (b * k + 0) / b = (b * t + i) / b := by rw [add_zero, heq]
      rw [Nat.mul_add_div hb, Nat.mul_add_div hb, Nat.zero_div, Nat.div_eq_of_lt hib] at this
      omega
    · simp [hib]

/-- `rep b m 0 = 0`. -/
theorem rep_zero : rep b m 0 = 0 := by simp [rep]

/-- One more period: `rep b m (n + 1) = rep b m n + 2 ^ (b m n)`. -/
theorem rep_succ : rep b m (n + 1) = rep b m n + 2 ^ (b * m * n) := by
  simp [rep, sum_range_succ]

/-- `rep b m n` has at most `m n` fields. -/
theorem rep_lt (hb : 0 < b) (hm : 0 < m) : ∀ n, rep b m n < 2 ^ (b * (m * n))
  | 0 => by simp [rep_zero]
  | n + 1 => by
    rw [rep_succ]
    have := rep_lt hb hm n
    have h1 : 2 ^ (b * (m * n)) + 2 ^ (b * m * n) ≤ 2 ^ (b * (m * (n + 1))) := by
      rw [show b * m * n = b * (m * n) by ring, ← two_mul, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega

/-- The fields of `rep b m n`: `1` at the multiples of `m` below `m n`, and `0` elsewhere. -/
theorem field_rep (hb : 0 < b) (hm : 0 < m) :
    ∀ n t, field b (rep b m n) t = if t < m * n ∧ m ∣ t then 1 else 0
  | 0, t => by simp [rep_zero]
  | n + 1, t => by
    have hpow : ∀ s, field b (2 ^ (b * m * n)) s = if s = m * n then 1 else 0 := fun s => by
      rw [show b * m * n = b * (m * n) by ring]; exact field_two_pow_mul hb _ s
    have hb2 : 1 < 2 ^ b := Nat.one_lt_two_pow hb.ne'
    rw [rep_succ, field_add, field_rep hb hm n, hpow]
    · by_cases h : t = m * n
      · subst h; simp [hm]
      · have : t < m * (n + 1) ∧ m ∣ t ↔ t < m * n ∧ m ∣ t := by
          constructor
          · rintro ⟨h1, ⟨c, rfl⟩⟩
            refine ⟨?_, ⟨c, rfl⟩⟩
            have : c < n + 1 := by nlinarith
            have : c ≠ n := fun hc => h (by rw [hc])
            nlinarith [Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp ‹c < n + 1›) this]
          · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, h2⟩
        simp only [h, ite_false, add_zero, this]
    · intro s _
      rw [field_rep hb hm n, hpow]
      split_ifs with h1 h2 <;> omega

/-- The closed form of `rep b m n`, a geometric sum. -/
theorem rep_eq_div (hbm : 0 < b * m) :
    rep b m n = (2 ^ (b * m * n) - 1) / (2 ^ (b * m) - 1) := by
  have h2 : 2 ≤ 2 ^ (b * m) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (b * m) := Nat.pow_le_pow_right (by norm_num) hbm
  rw [rep, pow_mul, ← Nat.geomSum_eq h2 n]
  exact sum_congr rfl fun j _ => pow_mul _ _ _

/-- `rep b 1 n` has all its `n` fields equal to `1`. -/
theorem spec_rep_one (hb : 0 < b) (n : ℕ) : Spec b n (rep b 1 n) fun _ => 1 :=
  ⟨by simpa using rep_lt hb one_pos n, fun t ht => by simp [field_rep hb one_pos, ht]⟩

/-- The closed form `(2 ^ (b m n) - 1) / (2 ^ (b m) - 1)` of `rep b m n`, evaluated by the kernel
with a few GMP operations. -/
def repC (b m n : ℕ) : ℕ :=
  (2 ^ (b * m * n) - 1) / (2 ^ (b * m) - 1)

/-- `rep` agrees with its closed form `repC`. -/
theorem rep_eq_repC (hbm : 0 < b * m) : rep b m n = repC b m n :=
  rep_eq_div hbm

/-- The packed indicator of the numbers `t < R` divisible by none of the numbers `ps`. -/
def unitInd (b R : ℕ) : List ℕ → ℕ
  | [] => repC b 1 R
  | p :: ps => (repC b 1 R - repC b p (R / p)) &&& unitInd b R ps

/-- The packed indicator of the numbers `t < R` not divisible by `p ∣ R`. -/
theorem spec_not_dvd (hb : 0 < b) {R p : ℕ} (hp : 0 < p) (hpR : p ∣ R) :
    Spec b R (repC b 1 R - repC b p (R / p)) fun t => if p ∣ t then 0 else 1 := by
  have hbp : 0 < b * p := Nat.mul_pos hb hp
  rw [← rep_eq_repC (by simpa using hb), ← rep_eq_repC hbp]
  have hmul : p * (R / p) = R := Nat.mul_div_cancel' hpR
  have hle : ∀ s, field b (rep b p (R / p)) s ≤ field b (rep b 1 R) s := by
    intro s
    rw [field_rep hb hp, field_rep hb one_pos, hmul, one_mul]
    split_ifs with h1 h2 <;> simp_all
  refine ⟨lt_of_le_of_lt (Nat.sub_le _ _) (by simpa using rep_lt hb one_pos R), fun t ht => ?_⟩
  rw [field_sub hb hle, field_rep hb hp, field_rep hb one_pos, hmul, one_mul]
  by_cases h : p ∣ t <;> simp [h, ht]

/-- The fields of `unitInd b R ps`: `1` at the numbers `t < R` divisible by none of `ps`. -/
theorem spec_unitInd (hb : 0 < b) {R : ℕ} :
    ∀ ps : List ℕ, (∀ p ∈ ps, 0 < p ∧ p ∣ R) →
      Spec b R (unitInd b R ps) fun t => if ∀ p ∈ ps, ¬p ∣ t then 1 else 0
  | [], _ => by
    rw [unitInd, ← rep_eq_repC (by simpa using hb)]
    simpa using spec_rep_one hb R
  | p :: ps, h => by
    have h₁ := spec_not_dvd hb (h p (by simp)).1 (h p (by simp)).2
    have h₂ := spec_unitInd hb ps fun q hq => h q (by simp [hq])
    refine ⟨lt_of_le_of_lt Nat.and_le_left h₁.lt, fun t ht => ?_⟩
    rw [unitInd, field_and, h₁.field_eq t ht, h₂.field_eq t ht]
    by_cases hpt : p ∣ t
    · simp [hpt]
    · have hcons : (∀ q ∈ p :: ps, ¬q ∣ t) ↔ ∀ q ∈ ps, ¬q ∣ t := by simp [hpt]
      rw [ite_eq_right hpt, if_congr hcons rfl rfl]
      split_ifs <;> rfl

end Erdos455.Packed
