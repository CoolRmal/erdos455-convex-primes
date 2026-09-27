/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.Packed.Ops

/-!
# Checking the fields of a packed vector

`checkSpec b n f x` tests `Spec b n x f` by a divide-and-conquer recursion that splits `x` into
its lower and upper halves, so that the kernel evaluates it with `O(size · log n)` bit
operations and recursion depth `O(log n)`.

## Main statements

* `Erdos455.Packed.spec_of_checkSpec`: soundness of `checkSpec`.
-/

namespace Erdos455.Packed

/-- Whether fields `t < n` of `x` are `f (k + t)`, by divide and conquer with recursion depth at
most `depth` (it answers `false` if the depth does not suffice). -/
def checkFields (b : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | depth + 1, k, n, x =>
    if n ≤ 1 then n == 0 || x % 2 ^ b == f k
    else
      checkFields b f depth k (n / 2) (x % 2 ^ (b * (n / 2))) &&
        checkFields b f depth (k + n / 2) (n - n / 2) (x >>> (b * (n / 2)))

/-- Whether `Spec b n x f` holds, tested by `checkFields` (with recursion depth `32`). -/
def checkSpec (b n : ℕ) (f : ℕ → ℕ) (x : ℕ) : Bool :=
  x < 2 ^ (b * n) && checkFields b f 32 0 n x

theorem field_mod_two_pow {b x h t : ℕ} (ht : t < h) :
    field b (x % 2 ^ (b * h)) t = field b x t := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [testBit_field, testBit_field, Nat.testBit_mod_two_pow]
  by_cases hi : i < b
  · have : b * t + i < b * h := by
      have : b * t + i < b * (t + 1) := by rw [Nat.mul_succ]; omega
      exact this.trans_le (Nat.mul_le_mul_left b ht)
    simp [hi, this]
  · simp [hi]

/-- Soundness of `checkFields`. -/
theorem field_eq_of_checkFields {b : ℕ} {f : ℕ → ℕ} :
    ∀ {depth k n x : ℕ}, checkFields b f depth k n x = true → ∀ t < n, field b x t = f (k + t)
  | 0, _, _, _, h => by simp [checkFields] at h
  | depth + 1, k, n, x, h => by
    intro t ht
    simp only [checkFields] at h
    split_ifs at h with hn
    · obtain rfl : t = 0 := by omega
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · omega
      · rw [field_zero, h, add_zero]
    · simp only [Bool.and_eq_true] at h
      by_cases hth : t < n / 2
      · rw [← field_mod_two_pow hth]
        exact field_eq_of_checkFields h.1 t hth
      · have := field_eq_of_checkFields h.2 (t - n / 2) (by omega)
        rw [field_shiftRight, Nat.sub_add_cancel (not_lt.mp hth)] at this
        rw [this]
        congr 1
        omega

/-- Soundness of `checkSpec`. -/
theorem spec_of_checkSpec {b n : ℕ} {f : ℕ → ℕ} {x : ℕ} (h : checkSpec b n f x = true) :
    Spec b n x f := by
  simp only [checkSpec, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun t ht => by simpa using field_eq_of_checkFields h.2 t ht⟩

end Erdos455.Packed
