/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.Packed.Ops
import Erdos455.DP.Step

/-!
# Soundness of the packed operations

For a well-formed layout (`Layout.WF`: the packed constants have the specified fields), the
operations of `Erdos455.DP.Step` act on packed vectors as intended: `shift` rotates the fields,
adds one and clears the non-units, and `pmax` is the fieldwise maximum.

## Main definitions

* `Erdos455.DP.Layout.WF`: the specification of the packed constants of a layout.
* `Erdos455.DP.Layout.Bounded L x B`: `x` has at most `R` fields, all at most `B`.

## Main statements

* `Erdos455.DP.Layout.WF.shift`, `Erdos455.DP.Layout.WF.pmax`: the chain step and the fieldwise
  maximum.
-/

namespace Erdos455.DP

open Packed

namespace Layout

variable {L : Layout}

/-- The specification of the packed constants of a layout. -/
structure WF (L : Layout) : Prop where
  two_le_b : 2 ≤ L.b
  R_pos : 0 < L.R
  ones : Spec L.b L.R L.ones fun _ => 1
  highs : Spec L.b L.R L.highs fun _ => 2 ^ (L.b - 1)
  umask : Spec L.b L.R L.umask fun t => if Nat.Coprime t L.R then 2 ^ L.b - 1 else 0
  uones : Spec L.b L.R L.uones fun t => if Nat.Coprime t L.R then 1 else 0
  uhighs : Spec L.b L.R L.uhighs fun t => if Nat.Coprime t L.R then 2 ^ (L.b - 1) else 0

/-- `x` is a packed vector of at most `R` fields, all at most `B`. -/
def Bounded (L : Layout) (x B : ℕ) : Prop :=
  x < 2 ^ (L.b * L.R) ∧ ∀ t, field L.b x t ≤ B

/-- A bound on the fields can be weakened. -/
theorem Bounded.mono {x B B' : ℕ} (h : L.Bounded x B) (hB : B ≤ B') : L.Bounded x B' :=
  ⟨h.1, fun t => (h.2 t).trans hB⟩

/-- A bounded packed vector is specified by its own fields. -/
theorem Bounded.spec {x B : ℕ} (h : L.Bounded x B) : Spec L.b L.R x (field L.b x) :=
  ⟨h.1, fun _ _ => rfl⟩

/-- The fields of a bounded packed vector vanish from `R` on. -/
theorem Bounded.field_eq_zero {x B t : ℕ} (h : L.Bounded x B) (ht : L.R ≤ t) :
    field L.b x t = 0 :=
  field_eq_zero_of_lt_pow h.1 ht

namespace WF

variable (hL : L.WF)
include hL

/-- The field width is positive. -/
theorem b_pos : 0 < L.b := by have := hL.two_le_b; omega

/-- The guard bit is below the field size: `2 ^ (b - 1) < 2 ^ b`. -/
theorem pow_pred_lt : 2 ^ (L.b - 1) < 2 ^ L.b :=
  Nat.pow_lt_pow_right (by norm_num) (by have := hL.two_le_b; omega)

/-- The chain step: `shift k x` rotates the fields of `x` by `k`, adds one and clears the
non-units. -/
theorem shift {x B k : ℕ} (hx : L.Bounded x B) (hB : B + 1 < 2 ^ L.b) (hk : k ≤ L.R) :
    L.Bounded (L.shift k x) (B + 1) ∧ ∀ t < L.R, Nat.Coprime t L.R →
      field L.b (L.shift k x) t = field L.b x ((t + L.R - k) % L.R) + 1 := by
  have hrot : ∀ t < L.R, field L.b (L.rot k x) t = field L.b x ((t + L.R - k) % L.R) :=
    fun t ht => field_rot hx.1 hk ht
  have hsum : ∀ t < L.R, field L.b (L.rot k x + L.ones) t =
      field L.b x ((t + L.R - k) % L.R) + 1 := by
    intro t ht
    rw [field_add, hrot t ht, hL.ones.field_eq t ht]
    intro s hs
    rw [hrot s (by omega), hL.ones.field_eq s (by omega)]
    exact lt_of_le_of_lt (by gcongr; exact hx.2 _) hB
  have hfield : ∀ t, field L.b (L.shift k x) t =
      if t < L.R ∧ Nat.Coprime t L.R then field L.b x ((t + L.R - k) % L.R) + 1 else 0 := by
    intro t
    rw [Layout.shift, field_and]
    by_cases ht : t < L.R
    · rw [hL.umask.field_eq t ht, hsum t ht]
      by_cases hc : Nat.Coprime t L.R
      · rw [ite_eq_left hc, ite_eq_left ⟨ht, hc⟩, Nat.and_two_pow_sub_one_of_lt_two_pow]
        exact lt_of_le_of_lt (by gcongr; exact hx.2 _) hB
      · rw [ite_eq_right hc, Nat.and_zero, ite_eq_right fun h => hc h.2]
    · rw [hL.umask.field_of_le (not_lt.mp ht), Nat.and_zero, ite_eq_right fun h => ht h.1]
  refine ⟨⟨lt_of_le_of_lt Nat.and_le_right hL.umask.lt, fun t => ?_⟩, fun t ht hc => ?_⟩
  · rw [hfield]
    split_ifs
    · gcongr; exact hx.2 _
    · exact Nat.zero_le _
  · rw [hfield, ite_eq_left ⟨ht, hc⟩]

/-- `pmax` is the fieldwise maximum. -/
theorem pmax {a x A X : ℕ} (ha : L.Bounded a A) (hx : L.Bounded x X) (hA : A < 2 ^ (L.b - 1))
    (hX : X < 2 ^ (L.b - 1)) :
    L.Bounded (L.pmax a x) (max A X) ∧
      ∀ t, field L.b (L.pmax a x) t = max (field L.b a t) (field L.b x t) := by
  have hs := Spec.pmax hL.b_pos hL.highs ha.spec hx.spec (fun t _ => (ha.2 t).trans_lt hA)
    (fun t _ => (hx.2 t).trans_lt hX)
  have hfield : ∀ t, field L.b (L.pmax a x) t = max (field L.b a t) (field L.b x t) := by
    intro t
    by_cases ht : t < L.R
    · exact hs.field_eq t ht
    · rw [ha.field_eq_zero (not_lt.mp ht), hx.field_eq_zero (not_lt.mp ht), max_self]
      exact hs.field_of_le (not_lt.mp ht)
  exact ⟨⟨hs.lt, fun t => by rw [hfield]; exact max_le_max (ha.2 t) (hx.2 t)⟩, hfield⟩

end WF

end Layout

end Erdos455.DP
