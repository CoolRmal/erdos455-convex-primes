/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.DP.Invariant

/-!
# Soundness of a run of the value iteration

Normalisation does not change the values of a state (`Layout.WF.normalize`), so a successful
run of the value iteration propagates the conclusion `Sim` of the value iteration
(`Layout.WF.run`). The initial state and the final comparison are checked by the Boolean
tests `Layout.goodB` and `Layout.finalB`, which the kernel evaluates.

## Main statements

* `Erdos455.DP.Layout.WF.run`: soundness of `Layout.run`.
* `Erdos455.DP.Layout.WF.good_of_goodB`: soundness of the test of the invariant.
* `Erdos455.DP.Layout.WF.value_le_of_finalB`: soundness of the final comparison.
-/

namespace Erdos455.DP

open Packed

theorem cond_eq_some {α : Type*} {c : Bool} {x y : α} :
    (bif c then some x else none) = some y ↔ c = true ∧ x = y := by
  cases c <;> simp

namespace Layout

variable {L : Layout}

/-- A kernel-checkable test of the invariant `State.Good`. -/
def goodB (L : Layout) (st : State) : Bool :=
  st.bound < 2 ^ (L.b - 1) && st.w₁ < 2 ^ (L.b * L.R) && st.w₂ < 2 ^ (L.b * L.R) &&
    st.w₁ &&& L.highs == 0 && st.w₂ &&& L.highs == 0 &&
    ple L.highs st.w₁ (L.ones * st.bound) && ple L.highs st.w₂ (L.ones * st.bound)

/-- A kernel-checkable test of `value st r ≤ value st₀ r + Λ` for all units `r`. -/
def finalB (L : Layout) (st₀ st : State) (Λ : ℕ) : Bool :=
  st.offset ≤ st₀.offset + Λ && st₀.bound + (st₀.offset + Λ - st.offset) < 2 ^ (L.b - 1) &&
    ple L.highs st.w₁ (st₀.w₁ + L.ones * (st₀.offset + Λ - st.offset)) &&
    ple L.highs st.w₂ (st₀.w₂ + L.ones * (st₀.offset + Λ - st.offset))

theorem normalize_eq_some {s B : ℕ} {st st' : State} :
    L.normalize s B st = some st' ↔
      (s < 2 ^ (L.b - 1) ∧ B < 2 ^ (L.b - 1) ∧ ple L.uhighs (L.uones * s) st.w₁ = true ∧
        ple L.uhighs (L.uones * s) st.w₂ = true ∧
        ple L.highs (st.w₁ - L.uones * s) (L.ones * B) = true ∧
        ple L.highs (st.w₂ - L.uones * s) (L.ones * B) = true) ∧
      ⟨st.w₁ - L.uones * s, st.w₂ - L.uones * s, st.offset + s, B⟩ = st' := by
  simp only [Layout.normalize, cond_eq_some, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

namespace WF

variable (hL : L.WF)
include hL

theorem highs_spec : Spec L.b L.R L.highs fun t => if (fun _ => True) t then 2 ^ (L.b - 1) else 0 :=
  by simpa using hL.highs

/-- The fieldwise comparison `ple L.highs` is sound. -/
theorem le_of_ple_highs {x y X Y : ℕ} (hx : L.Bounded x X) (hy : L.Bounded y Y)
    (hX : X < 2 ^ (L.b - 1)) (hY : Y < 2 ^ (L.b - 1)) (h : ple L.highs x y = true) :
    ∀ t, field L.b x t ≤ field L.b y t := by
  intro t
  by_cases ht : t < L.R
  · exact Spec.le_of_ple hL.b_pos hL.highs_spec hx.spec hy.spec (fun t _ => (hx.2 t).trans_lt hX)
      (fun t _ => (hy.2 t).trans_lt hY) (fun t _ h => absurd trivial h)
      (by simpa [ple] using h) t ht trivial
  · rw [hx.field_eq_zero (not_lt.mp ht)]; exact Nat.zero_le _

/-- The packed vector `ones * B` has all fields equal to `B`. -/
theorem bounded_ones_mul {B : ℕ} (hB : B < 2 ^ L.b) : L.Bounded (L.ones * B) B ∧
    ∀ t < L.R, field L.b (L.ones * B) t = B := by
  have hs := hL.ones.mul_const (c := B) hL.b_pos fun _ _ => by omega
  refine ⟨⟨hs.lt, fun t => ?_⟩, fun t ht => by rw [hs.field_eq t ht, one_mul]⟩
  by_cases ht : t < L.R
  · rw [hs.field_eq t ht, one_mul]
  · rw [hs.field_of_le (not_lt.mp ht)]; exact Nat.zero_le _

/-- **Normalisation** subtracts `s` from every value, and adds `s` to the offset: it does not
change the values at the units. -/
theorem normalize {s B : ℕ} {st st' : State} (h : L.normalize s B st = some st')
    (hg : st.Good L) :
    st'.Good L ∧ st'.offset = st.offset + s ∧
      ∀ r, r % 3 ≠ 0 → Nat.Coprime (r % L.R) L.R → st'.value L r = st.value L r := by
  obtain ⟨⟨hs, hB, h₁, h₂, h₁', h₂'⟩, rfl⟩ := normalize_eq_some.mp h
  have hb := hL.b_pos
  have hpow := hL.pow_pred_lt
  have hsu : Spec L.b L.R (L.uones * s) fun t => (if Nat.Coprime t L.R then 1 else 0) * s :=
    hL.uones.mul_const hb fun t _ => by split_ifs <;> omega
  -- one component
  have comp : ∀ w, L.Bounded w st.bound → ple L.uhighs (L.uones * s) w = true →
      ple L.highs (w - L.uones * s) (L.ones * B) = true →
      L.Bounded (w - L.uones * s) B ∧ ∀ t < L.R, Nat.Coprime t L.R →
        s ≤ field L.b w t ∧ field L.b (w - L.uones * s) t = field L.b w t - s := by
    intro w hw hlo hhi
    have hle := Spec.le_of_ple hb hL.uhighs hsu hw.spec
      (fun t _ => by split_ifs <;> omega) (fun t _ => (hw.2 t).trans_lt hg.bound_lt)
      (fun t _ hc => by simp [hc]) (by simpa [ple] using hlo)
    have hle' : ∀ t, field L.b (L.uones * s) t ≤ field L.b w t := by
      intro t
      by_cases ht : t < L.R
      · rw [hsu.field_eq t ht]
        by_cases hc : Nat.Coprime t L.R
        · exact hle t ht hc
        · simp [hc]
      · rw [hsu.field_of_le (not_lt.mp ht)]; exact Nat.zero_le _
    have hsub : ∀ t, field L.b (w - L.uones * s) t =
        field L.b w t - field L.b (L.uones * s) t := fun t => field_sub hb hle'
    have hwb : L.Bounded (w - L.uones * s) st.bound :=
      ⟨lt_of_le_of_lt (Nat.sub_le _ _) hw.1, fun t => by rw [hsub]; exact (Nat.sub_le _ _).trans (hw.2 t)⟩
    have hbo := hL.bounded_ones_mul (B := B) (by omega)
    have hup := hL.le_of_ple_highs hwb hbo.1 hg.bound_lt hB hhi
    refine ⟨⟨hwb.1, fun t => ?_⟩, fun t ht hc => ?_⟩
    · by_cases ht : t < L.R
      · rw [← hbo.2 t ht]; exact hup t
      · rw [hwb.field_eq_zero (not_lt.mp ht)]; exact Nat.zero_le _
    · have h1 := hle' t
      rw [hsu.field_eq t ht, ite_eq_left hc, one_mul] at h1
      rw [hsub, hsu.field_eq t ht, ite_eq_left hc, one_mul]
      exact ⟨h1, rfl⟩
  obtain ⟨hb₁, hv₁⟩ := comp _ hg.w₁ h₁ h₁'
  obtain ⟨hb₂, hv₂⟩ := comp _ hg.w₂ h₂ h₂'
  refine ⟨⟨hB, hb₁, hb₂⟩, rfl, fun r hr hc => ?_⟩
  simp only [State.value]
  rcases (by omega : r % 3 = 1 ∨ r % 3 = 2) with h3 | h3
  · rw [h3, State.comp_one, State.comp_one]
    obtain ⟨hle, heq⟩ := hv₁ _ (Nat.mod_lt _ hL.R_pos) hc
    dsimp only
    omega
  · rw [h3, State.comp_two, State.comp_two]
    obtain ⟨hle, heq⟩ := hv₂ _ (Nat.mod_lt _ hL.R_pos) hc
    dsimp only
    omega

/-- One step of a run propagates the conclusion of the value iteration. -/
theorem runStep (hR : 3 * L.R = M) (φ : ℕ → ℕ) {K lo : ℕ}
    {k : List (ℕ × ℕ) → State → Option (List (ℕ × ℕ) × State)} {sched : List (ℕ × ℕ)}
    {st : State} {res : List (ℕ × ℕ) × State} (h : L.runStep K lo k sched st = some res)
    (hlo : lo + 1 < M) (hg : st.Good L) (hs : Sim L φ lo st) :
    ∃ sched' st', k sched' st' = some res ∧ st'.Good L ∧ Sim L φ (lo + 1) st' := by
  simp only [Layout.runStep] at h
  split at h
  · simp at h
  rename_i st₁ hstep
  obtain ⟨hg₁, -, hdom⟩ := hL.step hR (Nat.succ_pos lo) hlo hstep hg
  -- after the step
  have hs₁ : Sim L φ (lo + 1) st₁ := by
    intro d t μ hp
    have h0 := hs d t μ hp.of_succ
    have hrun := hp.isRun (lo + 1) (by omega) le_rfl
    have hstep' := hp.step (lo + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at hrun hstep'
    have := hdom (d (lo + 1)) (t lo) (μ (lo + 1)) (hp.gap_mod (lo + 1) (by omega) le_rfl)
      (hp.coprime lo (by omega)) hrun
    rw [Finset.sum_Ico_succ_top (by omega), hstep']
    omega
  cases hK : (lo + 1) % K == 0
  · simp only [hK, Bool.cond_false] at h
    exact ⟨sched, st₁, h, hg₁, hs₁⟩
  · simp only [hK, Bool.cond_true] at h
    split at h
    · simp at h
    rename_i s B sched'
    split at h
    · simp at h
    rename_i st₂ hnorm
    obtain ⟨hg₂, -, hval⟩ := hL.normalize hnorm hg₁
    refine ⟨sched', st₂, h, hg₂, fun d t μ hp => ?_⟩
    have hc := hp.coprime (lo + 1) le_rfl
    rw [hval _ (mod_three_ne_zero hc) (coprime_mod_R hR hc)]
    exact hs₁ d t μ hp

/-- **Soundness of a run**: a successful run of `n` steps from a state satisfying the conclusion
of the value iteration after `lo` steps satisfies it after `lo + n` steps. -/
theorem run (hR : 3 * L.R = M) (φ : ℕ → ℕ) (K : ℕ) :
    ∀ (n lo : ℕ) (sched : List (ℕ × ℕ)) (st : State) (res : List (ℕ × ℕ) × State),
      L.run K n lo sched st = some res → lo + n < M → st.Good L → Sim L φ lo st →
        res.2.Good L ∧ Sim L φ (lo + n) res.2
  | 0, lo, sched, st, res, h, _, hg, hs => by
    rw [run_zero] at h
    cases h
    exact ⟨hg, hs⟩
  | n + 1, lo, sched, st, res, h, hlt, hg, hs => by
    rw [run_succ] at h
    obtain ⟨sched', st', hk, hg', hs'⟩ := hL.runStep hR φ h (by omega) hg hs
    have := run hR φ K n (lo + 1) sched' st' res hk (by omega) hg' hs'
    rwa [show lo + 1 + n = lo + (n + 1) by ring] at this

/-- All fields of `x` are below `2 ^ (b - 1)` if the guard bits of `x` vanish. -/
theorem field_lt_of_and_highs {x : ℕ} (hx : x < 2 ^ (L.b * L.R)) (h : x &&& L.highs = 0)
    (t : ℕ) : field L.b x t < 2 ^ (L.b - 1) := by
  have hb : L.b - 1 + 1 = L.b := by have := hL.two_le_b; omega
  by_cases ht : t < L.R
  · have := congrArg (fun z => field L.b z t) h
    simp only [field_and, hL.highs.field_eq t ht, field_zero_left] at this
    have hlt : field L.b x t < 2 ^ (L.b - 1 + 1) := hb ▸ field_lt _ _ _
    rw [and_two_pow_of_lt hlt] at this
    split_ifs at this with h'
    · exact absurd this (Nat.two_pow_pos _).ne'
    · omega
  · rw [field_eq_zero_of_lt_pow hx (not_lt.mp ht)]; exact Nat.two_pow_pos _

/-- Soundness of the test `goodB` of the invariant. -/
theorem good_of_goodB {st : State} (h : L.goodB st = true) : st.Good L := by
  simp only [goodB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hB, h₁⟩, h₂⟩, hh₁⟩, hh₂⟩, hp₁⟩, hp₂⟩ := h
  have hpow := hL.pow_pred_lt
  have hbo := hL.bounded_ones_mul (B := st.bound) (by omega)
  have comp : ∀ w, w < 2 ^ (L.b * L.R) → w &&& L.highs = 0 →
      ple L.highs w (L.ones * st.bound) = true → L.Bounded w st.bound := by
    intro w hw hh hp
    have hwb : L.Bounded w (2 ^ (L.b - 1) - 1) :=
      ⟨hw, fun t => by have := hL.field_lt_of_and_highs hw hh t; omega⟩
    have hle := hL.le_of_ple_highs hwb hbo.1 (by omega) hB hp
    refine ⟨hw, fun t => ?_⟩
    by_cases ht : t < L.R
    · rw [← hbo.2 t ht]; exact hle t
    · rw [hwb.field_eq_zero (not_lt.mp ht)]; exact Nat.zero_le _
  exact ⟨hB, comp _ h₁ hh₁ hp₁, comp _ h₂ hh₂ hp₂⟩

/-- Soundness of the final comparison `finalB`: `value st r ≤ value st₀ r + Λ` at the units. -/
theorem value_le_of_finalB {st₀ st : State} {Λ : ℕ} (h : L.finalB st₀ st Λ = true)
    (hg₀ : st₀.Good L) (hg : st.Good L) :
    ∀ r, r % 3 ≠ 0 → st.value L r ≤ st₀.value L r + Λ := by
  simp only [finalB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hoff, hc⟩, hp₁⟩, hp₂⟩ := h
  set c := st₀.offset + Λ - st.offset with hcdef
  have hpow := hL.pow_pred_lt
  have hbo := hL.bounded_ones_mul (B := c) (by omega)
  have comp : ∀ w, L.Bounded w st₀.bound → L.Bounded (w + L.ones * c) (st₀.bound + c) ∧
      ∀ t, field L.b (w + L.ones * c) t = field L.b w t + field L.b (L.ones * c) t := by
    intro w hw
    have hadd : ∀ t, field L.b (w + L.ones * c) t = field L.b w t + field L.b (L.ones * c) t :=
      fun t => field_add fun s _ => by have := hw.2 s; have := hbo.1.2 s; omega
    refine ⟨⟨lt_pow_of_field_eq_zero hL.b_pos fun t ht => ?_, fun t => ?_⟩, hadd⟩
    · rw [hadd, hw.field_eq_zero ht, hbo.1.field_eq_zero ht]
    · rw [hadd]; have := hw.2 t; have := hbo.1.2 t; omega
  obtain ⟨hy₁, hadd₁⟩ := comp _ hg₀.w₁
  obtain ⟨hy₂, hadd₂⟩ := comp _ hg₀.w₂
  have hle₁ := hL.le_of_ple_highs hg.w₁ hy₁ hg.bound_lt hc hp₁
  have hle₂ := hL.le_of_ple_highs hg.w₂ hy₂ hg.bound_lt hc hp₂
  intro r hr
  have ht := Nat.mod_lt r hL.R_pos
  simp only [State.value]
  rcases (by omega : r % 3 = 1 ∨ r % 3 = 2) with h3 | h3
  · rw [h3, State.comp_one, State.comp_one]
    have := hle₁ (r % L.R)
    rw [hadd₁, hbo.2 _ ht] at this
    omega
  · rw [h3, State.comp_two, State.comp_two]
    have := hle₂ (r % L.R)
    rw [hadd₂, hbo.2 _ ht] at this
    omega

end WF

end Layout

end Erdos455.DP
