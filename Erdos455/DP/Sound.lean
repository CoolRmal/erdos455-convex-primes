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
adds one and clears the non-units, `pmax` is the fieldwise maximum, `chainMax` dominates all
the iterates of `shift`, and the comparisons `ple` are sound.

## Main definitions

* `Erdos455.DP.Layout.WF`: the specification of the packed constants of a layout.
* `Erdos455.DP.Layout.Bounded L x B`: `x` has at most `R` fields, all at most `B`.

## Main statements

* `Erdos455.DP.Layout.WF.shift`, `Erdos455.DP.Layout.WF.pmax`,
  `Erdos455.DP.Layout.WF.chainMax`: the chain operations.
* `Erdos455.DP.Layout.WF.field_shift_iterate`: the iterates of `shift` along a run of units.
-/

namespace Erdos455.DP

open Packed

namespace Layout

variable {L : Layout}

/-- The specification of the packed constants of a layout. -/
structure WF (L : Layout) : Prop where
  two_le_b : 2 ≤ L.b
  ones : Spec L.b L.R L.ones fun _ => 1
  highs : Spec L.b L.R L.highs fun _ => 2 ^ (L.b - 1)
  umask : Spec L.b L.R L.umask fun t => if Nat.Coprime t L.R then 2 ^ L.b - 1 else 0
  uones : Spec L.b L.R L.uones fun t => if Nat.Coprime t L.R then 1 else 0
  uhighs : Spec L.b L.R L.uhighs fun t => if Nat.Coprime t L.R then 2 ^ (L.b - 1) else 0

/-- `x` is a packed vector of at most `R` fields, all at most `B`. -/
def Bounded (L : Layout) (x B : ℕ) : Prop :=
  x < 2 ^ (L.b * L.R) ∧ ∀ t, field L.b x t ≤ B

theorem Bounded.mono {x B B' : ℕ} (h : L.Bounded x B) (hB : B ≤ B') : L.Bounded x B' :=
  ⟨h.1, fun t => (h.2 t).trans hB⟩

theorem Bounded.spec {x B : ℕ} (h : L.Bounded x B) : Spec L.b L.R x (field L.b x) :=
  ⟨h.1, fun _ _ => rfl⟩

theorem Bounded.field_eq_zero {x B t : ℕ} (h : L.Bounded x B) (ht : L.R ≤ t) :
    field L.b x t = 0 :=
  field_eq_zero_of_lt_pow h.1 ht

namespace WF

variable (hL : L.WF)
include hL

theorem b_pos : 0 < L.b := by have := hL.two_le_b; omega

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

/-- `chainMax k n x acc` dominates `acc` and the iterates `shift^[j] x` for `1 ≤ j ≤ n`. -/
theorem chainMax {k : ℕ} (hk : k ≤ L.R) :
    ∀ (n : ℕ) {x acc B A : ℕ}, L.Bounded x B → L.Bounded acc A → B + n < 2 ^ (L.b - 1) →
      A < 2 ^ (L.b - 1) →
      L.Bounded (L.chainMax k n x acc) (max A (B + n)) ∧
        (∀ t, field L.b acc t ≤ field L.b (L.chainMax k n x acc) t) ∧
        ∀ j, 1 ≤ j → j ≤ n → ∀ t,
          field L.b ((L.shift k)^[j] x) t ≤ field L.b (L.chainMax k n x acc) t
  | 0, x, acc, B, A, _, hacc, _, _ => by
    refine ⟨hacc.mono (le_max_left _ _), fun t => le_rfl, fun j hj hjn => by omega⟩
  | n + 1, x, acc, B, A, hx, hacc, hBn, hA => by
    have hB1 : B + 1 < 2 ^ L.b := by have := hL.pow_pred_lt; omega
    obtain ⟨hy, -⟩ := hL.shift hx hB1 hk
    obtain ⟨hacc', hmax⟩ := hL.pmax hacc hy hA (by omega)
    obtain ⟨hb, hge, hiter⟩ := chainMax hk n hy hacc' (by omega) (max_lt hA (by omega))
    have heq : L.chainMax k (n + 1) x acc =
        L.chainMax k n (L.shift k x) (L.pmax acc (L.shift k x)) := rfl
    rw [heq]
    refine ⟨hb.mono (by omega), fun t => (le_max_left _ _).trans ((hmax t).symm ▸ hge t),
      fun j hj hjn t => ?_⟩
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · obtain rfl : j = 1 := by omega
      exact (le_max_right _ _).trans ((hmax t).symm ▸ hge t)
    · have := hiter (j - 1) (by omega) (by omega) t
      rwa [← Function.iterate_succ_apply, show (j - 1).succ = j by omega] at this

/-- The iterates of `shift k` are bounded. -/
theorem bounded_shift_iterate {k x B : ℕ} (hk : k ≤ L.R) (hx : L.Bounded x B) :
    ∀ j, B + j < 2 ^ L.b → L.Bounded ((L.shift k)^[j] x) (B + j)
  | 0, _ => hx
  | j + 1, h => by
    rw [Function.iterate_succ_apply']
    exact (hL.shift (bounded_shift_iterate hk hx j (by omega)) (by omega) hk).1

end WF

end Layout

end Erdos455.DP
