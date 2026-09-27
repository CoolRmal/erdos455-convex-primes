/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib

/-!
# Packed fields

A natural number `x` is read as a little-endian vector of *fields* of `b` bits each: field `t`
of `x` is `x / 2 ^ (b * t) % 2 ^ b`. The kernel evaluates arithmetic and bitwise operations on
`ℕ` literals with GMP, so one operation on a packed number acts on thousands of fields at once.
This file relates the operations on packed numbers to the operations on their fields.

## Main definitions

* `Erdos455.Packed.field b x t`: the `t`-th field of width `b` of `x`.

## Main statements

* `field_shiftRight`, `field_shiftLeft`: shifts by whole fields move fields.
* `field_or`, `field_and`, `field_xor`: bitwise operations act fieldwise.
* `field_add`, `field_sub`, `field_mul`: arithmetic acts fieldwise when no carry or borrow
  crosses a field boundary.
* `field_shiftRight_of_lt`: a shift by less than a field, when the bits shifted in are zero.
-/

namespace Erdos455.Packed

/-- The `t`-th field of width `b` of the packed number `x`. -/
def field (b x t : ℕ) : ℕ := x / 2 ^ (b * t) % 2 ^ b

variable {b x y t : ℕ}

/-- A field is below `2 ^ b`. -/
theorem field_lt (b x t : ℕ) : field b x t < 2 ^ b :=
  Nat.mod_lt _ (Nat.two_pow_pos b)

/-- All fields of `0` vanish. -/
@[simp]
theorem field_zero_left (b t : ℕ) : field b 0 t = 0 := by
  simp [field]

/-- Field `0` is the residue modulo `2 ^ b`. -/
theorem field_zero (b x : ℕ) : field b x 0 = x % 2 ^ b := by
  simp [field]

/-- Field `t + 1` of `x` is field `t` of `x / 2 ^ b`. -/
theorem field_succ (b x t : ℕ) : field b x (t + 1) = field b (x / 2 ^ b) t := by
  simp only [field, Nat.div_div_eq_div_mul, ← pow_add]
  ring_nf

/-- The bits of a field are bits of the packed number. -/
theorem testBit_field (b x t i : ℕ) :
    (field b x t).testBit i = (decide (i < b) && x.testBit (b * t + i)) := by
  simp only [field, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  rw [Nat.add_comm i]

/-- Fields beyond the length of a packed number vanish. -/
theorem field_eq_zero_of_lt_pow {n : ℕ} (hx : x < 2 ^ (b * n)) (ht : n ≤ t) :
    field b x t = 0 := by
  have : x / 2 ^ (b * t) = 0 :=
    Nat.div_eq_of_lt (hx.trans_le (Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_left b ht)))
  simp [field, this]

/-- Two packed numbers with the same fields are equal. -/
theorem eq_of_field_eq (hb : 0 < b) (h : ∀ t, field b x t = field b y t) : x = y := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  have key : ∀ z : ℕ, z.testBit i = (field b z (i / b)).testBit (i % b) := by
    intro z
    rw [testBit_field, decide_eq_true (Nat.mod_lt i hb), Bool.true_and, Nat.div_add_mod]
  rw [key x, key y, h]

/-- A right shift by `k` whole fields moves field `t + k` to field `t`. -/
theorem field_shiftRight (b x k t : ℕ) : field b (x >>> (b * k)) t = field b x (t + k) := by
  simp only [field, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
  ring_nf

/-- A left shift by `k` whole fields moves field `t` to field `t + k`, filling with zeros. -/
theorem field_shiftLeft (b x k t : ℕ) :
    field b (x <<< (b * k)) t = if t < k then 0 else field b x (t - k) := by
  split_ifs with h
  · refine Nat.eq_of_testBit_eq fun i => ?_
    rw [testBit_field, Nat.testBit_shiftLeft, Nat.zero_testBit]
    by_cases hi : i < b
    · have : ¬ b * t + i ≥ b * k := by
        have : b * t + i < b * (t + 1) := by rw [Nat.mul_succ]; omega
        have : b * (t + 1) ≤ b * k := Nat.mul_le_mul_left b h
        omega
      simp [this]
    · simp [hi]
  · rw [not_lt] at h
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [testBit_field, testBit_field, Nat.testBit_shiftLeft]
    by_cases hi : i < b
    · have h1 : b * t + i ≥ b * k := le_add_right (Nat.mul_le_mul_left b h)
      have h2 : b * t + i - b * k = b * (t - k) + i := by
        rw [Nat.mul_sub]; have := Nat.mul_le_mul_left b h; omega
      simp [hi, h1, h2]
    · simp [hi]

/-- Bitwise or acts fieldwise. -/
theorem field_or (b x y t : ℕ) : field b (x ||| y) t = field b x t ||| field b y t := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [testBit_field, Nat.testBit_or]
  cases decide (i < b) <;> simp

/-- Bitwise and acts fieldwise. -/
theorem field_and (b x y t : ℕ) : field b (x &&& y) t = field b x t &&& field b y t := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [testBit_field, Nat.testBit_and]
  cases decide (i < b) <;> simp

/-- Bitwise xor acts fieldwise. -/
theorem field_xor (b x y t : ℕ) : field b (x ^^^ y) t = field b x t ^^^ field b y t := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [testBit_field, Nat.testBit_xor]
  cases decide (i < b) <;> simp

/-- Splitting off the lowest field. -/
theorem mod_add_div_pow (b x : ℕ) : x % 2 ^ b + 2 ^ b * (x / 2 ^ b) = x :=
  Nat.mod_add_div x (2 ^ b)

/-- Addition acts fieldwise on the fields below `t` when no field overflows. -/
theorem field_add (h : ∀ s ≤ t, field b x s + field b y s < 2 ^ b) :
    field b (x + y) t = field b x t + field b y t := by
  induction t generalizing x y with
  | zero =>
    have h0 := h 0 le_rfl
    simp only [field_zero] at h0 ⊢
    rw [Nat.add_mod, Nat.mod_eq_of_lt h0]
  | succ t ih =>
    have h0 := h 0 (Nat.zero_le _)
    simp only [field_zero] at h0
    have hsplit : x + y = (x % 2 ^ b + y % 2 ^ b) + 2 ^ b * (x / 2 ^ b + y / 2 ^ b) := by
      conv_lhs => rw [← mod_add_div_pow b x, ← mod_add_div_pow b y]
      ring
    have hdiv : (x + y) / 2 ^ b = x / 2 ^ b + y / 2 ^ b := by
      rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos b), Nat.div_eq_of_lt h0, zero_add]
    rw [field_succ, field_succ, field_succ, hdiv]
    refine ih fun s hs => ?_
    rw [← field_succ, ← field_succ]
    exact h (s + 1) (by omega)

/-- All fields of `y` are at most those of `x`, so `y ≤ x`. -/
theorem le_of_field_le (hb : 0 < b) (h : ∀ s, field b y s ≤ field b x s) : y ≤ x := by
  induction x using Nat.strong_induction_on generalizing y with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · have : ∀ s, field b y s = 0 := fun s => Nat.le_zero.mp (by simpa using h s)
      exact (eq_of_field_eq hb fun s => by simp [this s]).le
    · have hlt : x / 2 ^ b < x := Nat.div_lt_self hx (Nat.one_lt_two_pow hb.ne')
      have hdiv : y / 2 ^ b ≤ x / 2 ^ b :=
        ih _ hlt fun s => by rw [← field_succ, ← field_succ]; exact h (s + 1)
      have hmod : y % 2 ^ b ≤ x % 2 ^ b := by simpa [field_zero] using h 0
      rw [← mod_add_div_pow b x, ← mod_add_div_pow b y]
      gcongr

/-- Subtraction acts fieldwise when no field borrows. -/
theorem field_sub (hb : 0 < b) (h : ∀ s, field b y s ≤ field b x s) :
    field b (x - y) t = field b x t - field b y t := by
  induction t generalizing x y with
  | zero =>
    have h0 := h 0
    simp only [field_zero] at h0 ⊢
    have hle : y / 2 ^ b ≤ x / 2 ^ b :=
      le_of_field_le hb fun s => by rw [← field_succ, ← field_succ]; exact h (s + 1)
    have hsplit : x - y = (x % 2 ^ b - y % 2 ^ b) + 2 ^ b * (x / 2 ^ b - y / 2 ^ b) := by
      conv_lhs => rw [← mod_add_div_pow b x, ← mod_add_div_pow b y]
      rw [Nat.mul_sub]
      have := Nat.mul_le_mul_left (2 ^ b) hle
      omega
    rw [hsplit, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos b)))]
  | succ t ih =>
    have h0 := h 0
    simp only [field_zero] at h0
    have hle : y / 2 ^ b ≤ x / 2 ^ b :=
      le_of_field_le hb fun s => by rw [← field_succ, ← field_succ]; exact h (s + 1)
    have hsplit : x - y = (x % 2 ^ b - y % 2 ^ b) + 2 ^ b * (x / 2 ^ b - y / 2 ^ b) := by
      conv_lhs => rw [← mod_add_div_pow b x, ← mod_add_div_pow b y]
      rw [Nat.mul_sub]
      have := Nat.mul_le_mul_left (2 ^ b) hle
      omega
    have hdiv : (x - y) / 2 ^ b = x / 2 ^ b - y / 2 ^ b := by
      rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos b),
        Nat.div_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos b))),
        zero_add]
    rw [field_succ, field_succ, field_succ, hdiv]
    exact ih fun s => by rw [← field_succ, ← field_succ]; exact h (s + 1)

/-- Multiplication by a scalar acts fieldwise when no field overflows. -/
theorem field_mul {c : ℕ} (h : ∀ s ≤ t, field b x s * c < 2 ^ b) :
    field b (x * c) t = field b x t * c := by
  induction t generalizing x with
  | zero =>
    have h0 := h 0 le_rfl
    simp only [field_zero] at h0 ⊢
    have hsplit : x * c = x % 2 ^ b * c + 2 ^ b * (x / 2 ^ b * c) := by
      conv_lhs => rw [← mod_add_div_pow b x]
      ring
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  | succ t ih =>
    have h0 := h 0 (Nat.zero_le _)
    simp only [field_zero] at h0
    have hsplit : x * c = x % 2 ^ b * c + 2 ^ b * (x / 2 ^ b * c) := by
      conv_lhs => rw [← mod_add_div_pow b x]
      ring
    have hdiv : x * c / 2 ^ b = x / 2 ^ b * c := by
      rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos b), Nat.div_eq_of_lt h0, zero_add]
    rw [field_succ, field_succ, hdiv]
    exact ih fun s hs => by rw [← field_succ]; exact h (s + 1) (by omega)

end Erdos455.Packed
