/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.Packed.Field

/-!
# Operations on packed vectors

We describe a packed vector of `n` fields of width `b` by `Spec b n x f`: `x < 2 ^ (b * n)` and
field `t < n` of `x` is `f t`. This file proves the specifications of the composite operations
used by the value iteration: rotation of the fields, fieldwise maximum and fieldwise
comparison. The maximum and the comparison use the top bit `b - 1` of every field as a guard
bit, so they require all fields to be below `2 ^ (b - 1)`.

## Main statements

* `Spec.rot`: rotating the fields by `k` places.
* `Spec.pmax`: the fieldwise maximum, computed with the guard bits.
* `Spec.le_of_ple`: soundness of the fieldwise comparison.
-/

namespace Erdos455.Packed

variable {b n x y t : ℕ}

/-- `x` packs `n` fields of width `b`, field `t < n` being `f t`. -/
structure Spec (b n x : ℕ) (f : ℕ → ℕ) : Prop where
  lt : x < 2 ^ (b * n)
  field_eq : ∀ t < n, field b x t = f t

theorem Spec.field_of_le {f : ℕ → ℕ} (h : Spec b n x f) (ht : n ≤ t) : field b x t = 0 :=
  field_eq_zero_of_lt_pow h.lt ht

/-- A packed number whose fields vanish from `n` on has at most `n` fields. -/
theorem lt_pow_of_field_eq_zero (hb : 0 < b) (h : ∀ t, n ≤ t → field b x t = 0) :
    x < 2 ^ (b * n) := by
  refine Nat.lt_pow_two_of_testBit x fun i hi => ?_
  have hi' : n ≤ i / b := (Nat.le_div_iff_mul_le hb).mpr (by rw [mul_comm]; exact hi)
  have := congrArg (fun z => z.testBit (i % b)) (h (i / b) hi')
  simp only [testBit_field, Nat.mod_lt i hb, decide_true, Bool.true_and, Nat.div_add_mod,
    Nat.zero_testBit] at this
  exact this

theorem spec_of_field (hb : 0 < b) {f : ℕ → ℕ} (h : ∀ t, field b x t = if t < n then f t else 0) :
    Spec b n x f :=
  ⟨lt_pow_of_field_eq_zero hb fun t ht => by simp [h, Nat.not_lt.mpr ht],
    fun t ht => by simp [h, ht]⟩

/-! ### Rotation -/

/-- Rotating the fields of `x` by `k ≤ n` places: field `t` of the result is field
`(t + n - k) % n` of `x`. The result may have fields beyond `n`. -/
theorem field_rot (hx : x < 2 ^ (b * n)) {k : ℕ} (hk : k ≤ n) (ht : t < n) :
    field b ((x <<< (b * k)) ||| (x >>> (b * (n - k)))) t = field b x ((t + n - k) % n) := by
  rw [field_or, field_shiftLeft, field_shiftRight]
  split_ifs with htk
  · have : t + (n - k) < n := by omega
    rw [Nat.zero_or, Nat.mod_eq_of_lt (by omega)]
    congr 1
    omega
  · rw [field_eq_zero_of_lt_pow hx (by omega : n ≤ t + (n - k)), Nat.or_zero]
    congr 1
    rw [show t + n - k = t - k + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-! ### Fieldwise maximum -/

section pmax

variable {a h : ℕ}

theorem field_or_high {k : ℕ} (hv : x < 2 ^ k) : x ||| 2 ^ k = x + 2 ^ k :=
  Nat.or_two_pow_eq_add_of_lt hv

/-- For `u < 2 ^ (k + 1)`, the bit `k` of `u` is set iff `2 ^ k ≤ u`. -/
theorem and_two_pow_of_lt {u k : ℕ} (hu : u < 2 ^ (k + 1)) :
    u &&& 2 ^ k = if 2 ^ k ≤ u then 2 ^ k else 0 := by
  rw [Nat.and_comm, Nat.two_pow_and, Nat.testBit_eq_decide_div_mod_eq]
  have hdiv : u / 2 ^ k < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]; rw [pow_succ] at hu; linarith
  split_ifs with hle
  · have : 1 ≤ u / 2 ^ k := (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).mpr (by simpa using hle)
    have h1 : u / 2 ^ k % 2 = 1 := by rw [Nat.mod_eq_of_lt hdiv]; omega
    simp [h1]
  · have : u / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]

/-- Fields whose low `c` bits vanish: a right shift by `c ≤ b` bits acts fieldwise. -/
theorem field_shiftRight_of_low {c : ℕ} (hc : c ≤ b) (hlow : ∀ s, field b x s % 2 ^ c = 0) :
    field b (x >>> c) t = field b x t >>> c := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [testBit_field, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hi : i < b
  · simp only [hi, decide_true, Bool.true_and]
    by_cases hic : c + i < b
    · rw [testBit_field]; simp only [hic, decide_true, Bool.true_and]; congr 1; ring
    · rw [show c + (b * t + i) = b * (t + 1) + (c + i - b) by rw [Nat.mul_succ]; omega]
      have h1 : (field b x (t + 1)).testBit (c + i - b) = false := by
        have := congrArg (fun z => z.testBit (c + i - b)) (hlow (t + 1))
        simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit] at this
        simpa [show c + i - b < c by omega] using this
      rw [testBit_field] at h1
      simp only [show c + i - b < b by omega, decide_true, Bool.true_and] at h1
      rw [h1, testBit_field]
      simp [hic]
  · simp only [hi, decide_false, Bool.false_and]
    rw [testBit_field]
    simp [show ¬ c + i < b by omega]

/-- The per-field computation of `pmax`: with `u = a₀ + 2 ^ k - x₀` and `c` its bit `k`,
`u &&& (c - c / 2 ^ k)` is the truncated difference `a₀ - x₀`. -/
theorem pmax_field_aux {k a₀ x₀ : ℕ} (ha : a₀ < 2 ^ k) (hx : x₀ < 2 ^ k) :
    let u := a₀ + 2 ^ k - x₀
    let c := if 2 ^ k ≤ u then 2 ^ k else 0
    (u &&& (c - c / 2 ^ k)) = a₀ - x₀ := by
  intro u c
  by_cases hle : x₀ ≤ a₀
  · have hc : c = 2 ^ k := if_pos (by omega)
    rw [hc, Nat.div_self (Nat.two_pow_pos k), Nat.and_two_pow_sub_one_eq_mod,
      show u = (a₀ - x₀) + 2 ^ k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · have hc : c = 0 := if_neg (by omega)
    rw [hc]
    simp only [Nat.zero_div, Nat.sub_zero, Nat.and_zero]
    omega

/-- The fieldwise maximum of two packed vectors whose fields are below `2 ^ (b - 1)`, computed
with the guard bits `h`. -/
theorem Spec.pmax (hb : 0 < b) {fa fx : ℕ → ℕ} (hh : Spec b n h fun _ => 2 ^ (b - 1))
    (ha : Spec b n a fa) (hx : Spec b n x fx) (hfa : ∀ t < n, fa t < 2 ^ (b - 1))
    (hfx : ∀ t < n, fx t < 2 ^ (b - 1)) :
    let u := (a ||| h) - x
    let c := u &&& h
    Spec b n (x + (u &&& (c - (c >>> (b - 1))))) fun t => max (fa t) (fx t) := by
  intro u c
  have hpow : 2 ^ b = 2 ^ (b - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  -- the fields of `a ||| h`
  have hah : ∀ s, field b (a ||| h) s = if s < n then fa s + 2 ^ (b - 1) else 0 := by
    intro s
    rw [field_or]
    by_cases hs : s < n
    · rw [if_pos hs, ha.field_eq s hs, hh.field_eq s hs, field_or_high (hfa s hs)]
    · rw [if_neg hs, ha.field_of_le (not_lt.mp hs), hh.field_of_le (not_lt.mp hs), Nat.zero_or]
  -- the fields of `u`
  have hu : ∀ s, field b u s = if s < n then fa s + 2 ^ (b - 1) - fx s else 0 := by
    intro s
    rw [field_sub hb]
    · rw [hah]
      by_cases hs : s < n
      · rw [if_pos hs, if_pos hs, hx.field_eq s hs]
      · rw [if_neg hs, if_neg hs, hx.field_of_le (not_lt.mp hs)]
    · intro s
      rw [hah]
      by_cases hs : s < n
      · rw [if_pos hs, hx.field_eq s hs]; have := hfx s hs; omega
      · rw [if_neg hs, hx.field_of_le (not_lt.mp hs)]
  -- the fields of `c`
  have hc : ∀ s, field b c s = if s < n then
      (if 2 ^ (b - 1) ≤ fa s + 2 ^ (b - 1) - fx s then 2 ^ (b - 1) else 0) else 0 := by
    intro s
    rw [field_and, hu]
    by_cases hs : s < n
    · rw [if_pos hs, if_pos hs, hh.field_eq s hs, and_two_pow_of_lt]
      rw [show b - 1 + 1 = b by omega]
      have := hfa s hs
      omega
    · rw [if_neg hs, if_neg hs, Nat.zero_and]
  have hclow : ∀ s, field b c s % 2 ^ (b - 1) = 0 := by
    intro s; rw [hc]; split_ifs <;> simp
  have hcs : ∀ s, field b (c >>> (b - 1)) s = field b c s / 2 ^ (b - 1) := by
    intro s
    rw [field_shiftRight_of_low (by omega) hclow, Nat.shiftRight_eq_div_pow]
  have hdiff : ∀ s, field b (c - (c >>> (b - 1))) s =
      field b c s - field b c s / 2 ^ (b - 1) := by
    intro s
    rw [field_sub hb (fun s => by rw [hcs]; exact Nat.div_le_self _ _), hcs]
  -- the fields of the summand are the truncated differences
  have hand : ∀ s, field b (u &&& (c - (c >>> (b - 1)))) s =
      if s < n then fa s - fx s else 0 := by
    intro s
    rw [field_and, hdiff, hu, hc]
    by_cases hs : s < n
    · rw [if_pos hs, if_pos hs, if_pos hs]
      exact pmax_field_aux (hfa s hs) (hfx s hs)
    · rw [if_neg hs, if_neg hs, if_neg hs, Nat.zero_and]
  refine spec_of_field hb fun s => ?_
  rw [field_add]
  · rw [hand]
    by_cases hs : s < n
    · rw [if_pos hs, if_pos hs, hx.field_eq s hs]; omega
    · rw [if_neg hs, if_neg hs, hx.field_of_le (not_lt.mp hs)]
  · intro s' _
    rw [hand]
    by_cases hs' : s' < n
    · rw [if_pos hs', hx.field_eq s' hs']
      have := hfa s' hs'; have := hfx s' hs'
      omega
    · rw [if_neg hs', hx.field_of_le (not_lt.mp hs')]; exact Nat.two_pow_pos b

end pmax

/-! ### Fieldwise comparison -/

/-- If the fieldwise comparison `((y ||| h) - x) &&& h = h` holds, with guard bits `h` on the
fields `t` with `g t`, and `x` vanishes off those fields, then `x ≤ y` on those fields. -/
theorem Spec.le_of_ple (hb : 0 < b) {h : ℕ} {g : ℕ → Bool} {fx fy : ℕ → ℕ}
    (hh : Spec b n h fun t => bif g t then 2 ^ (b - 1) else 0)
    (hx : Spec b n x fx) (hy : Spec b n y fy) (hfx : ∀ t < n, fx t < 2 ^ (b - 1))
    (hfy : ∀ t < n, fy t < 2 ^ (b - 1)) (hoff : ∀ t < n, g t = false → fx t = 0)
    (hle : ((y ||| h) - x) &&& h = h) : ∀ t < n, g t = true → fx t ≤ fy t := by
  intro t ht hg
  have hb' : b = b - 1 + 1 := by omega
  have hyh : ∀ s, field b (y ||| h) s =
      if s < n then (bif g s then fy s + 2 ^ (b - 1) else fy s) else 0 := by
    intro s
    rw [field_or]
    split_ifs with hs
    · rw [hy.field_eq s hs, hh.field_eq s hs]
      cases g s
      · simp
      · simp [field_or_high (hfy s hs)]
    · rw [hy.field_of_le (not_lt.mp hs), hh.field_of_le (not_lt.mp hs), Nat.zero_or]
  have hsub : field b ((y ||| h) - x) t = fy t + 2 ^ (b - 1) - fx t := by
    rw [field_sub hb, hyh, if_pos ht, hg, hx.field_eq t ht]
    · rfl
    · intro s
      rw [hyh]
      split_ifs with hs
      · rw [hx.field_eq s hs]
        cases hgs : g s
        · simp [hoff s hs hgs]
        · have := hfx s hs; simp; omega
      · rw [hx.field_of_le (not_lt.mp hs)]
  have := congrArg (fun z => field b z t) hle
  simp only [field_and, hsub, hh.field_eq t ht, hg, Bool.cond_true] at this
  have hpos := Nat.two_pow_pos (b - 1)
  rw [and_two_pow_of_lt] at this
  · split_ifs at this with h2
    · omega
    · exact absurd this.symm hpos.ne'
  · rw [← hb']
    have := hfy t ht
    have : 2 ^ b = 2 ^ (b - 1) * 2 := by rw [← pow_succ, ← hb']
    omega

end Erdos455.Packed
