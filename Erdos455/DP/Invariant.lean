/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.DP.Sound
import Erdos455.DP.Runs

/-!
# Soundness of the value iteration

A `State` represents the function `r ↦ State.value L st r` on the units modulo `M = 3 R`. We
show that a successful step of the value iteration dominates the max-plus operator of the
dynamic program (`Layout.WF.step`), that normalisation does not change the values
(`Layout.WF.normalize`), and hence that a successful run dominates every path of runs
(`Layout.WF.run`): along a path starting at `t 0`, `value st₀ (t 0) + ∑ μ i ≤ value st (t n)`.

## Main definitions

* `Erdos455.DP.State.value`: the function represented by a state.
* `Erdos455.DP.State.Good`: the invariant of the states (all fields at most the bound).
* `Erdos455.PathUpTo`: a path of runs along the first `n` gap values of a period.
* `Erdos455.DP.Sim`: the conclusion of the value iteration after `n` steps.
-/

namespace Erdos455

/-- A path of runs along the first `n` gap values of a period: starting at the unit `t 0`, for
`1 ≤ i ≤ n` a run of length `μ i` with gap `d i ≡ 2 i [MOD M]` leads from `t (i - 1)` to
`t i`. -/
structure PathUpTo (n : ℕ) (d t μ : ℕ → ℕ) : Prop where
  coprime_zero : Nat.Coprime (t 0) M
  gap_mod : ∀ i, 1 ≤ i → i ≤ n → d i % M = 2 * i % M
  isRun : ∀ i, 1 ≤ i → i ≤ n → IsRun (d i) (t (i - 1)) (μ i)
  step : ∀ i, 1 ≤ i → i ≤ n → t i = t (i - 1) + μ i * d i

namespace PathUpTo

variable {n : ℕ} {d t μ : ℕ → ℕ}

/-- A path of length `n + 1` restricts to a path of length `n`. -/
theorem of_succ (h : PathUpTo (n + 1) d t μ) : PathUpTo n d t μ :=
  ⟨h.coprime_zero, fun i hi hin => h.gap_mod i hi (by omega),
    fun i hi hin => h.isRun i hi (by omega), fun i hi hin => h.step i hi (by omega)⟩

/-- All points of a path are units. -/
theorem coprime (h : PathUpTo n d t μ) : ∀ i ≤ n, Nat.Coprime (t i) M
  | 0, _ => h.coprime_zero
  | i + 1, hi => by
    rw [h.step (i + 1) (by omega) hi, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos (μ (i + 1)) with h0 | hpos
    · rw [h0, zero_mul, add_zero]; exact coprime h i (by omega)
    · have := h.isRun (i + 1) (by omega) hi (μ (i + 1)) hpos le_rfl
      rwa [Nat.add_sub_cancel] at this

end PathUpTo

/-- A path over a period is a path of length `M - 1`. -/
theorem PeriodPath.pathUpTo {d t μ : ℕ → ℕ} (h : PeriodPath d t μ) : PathUpTo (M - 1) d t μ :=
  ⟨h.coprime_zero, fun i hi hin => h.gap_mod i hi (by simp only [M] at hin ⊢; omega),
    fun i hi hin => h.isRun i hi (by simp only [M] at hin ⊢; omega),
    fun i hi hin => h.step i hi (by simp only [M] at hin ⊢; omega)⟩

namespace DP

open Packed

/-- The component of a state holding the residues `≡ c [MOD 3]`. -/
def State.comp (st : State) (c : ℕ) : ℕ :=
  if c = 1 then st.w₁ else if c = 2 then st.w₂ else 0

/-- The value of a state at the residue `r` (meaningful for units `r`). -/
def State.value (L : Layout) (st : State) (r : ℕ) : ℕ :=
  field L.b (st.comp (r % 3)) (r % L.R) + st.offset

/-- The invariant of the states: the bound is below the guard bit and bounds all fields. -/
structure State.Good (L : Layout) (st : State) : Prop where
  bound_lt : st.bound < 2 ^ (L.b - 1)
  w₁ : L.Bounded st.w₁ st.bound
  w₂ : L.Bounded st.w₂ st.bound

/-- `Sim L φ n st`: along every path of runs of length `n`, `φ (t 0) + ∑ μ i ≤ value st (t n)`.
This is what `n` steps of the value iteration from `φ` establish. -/
def Sim (L : Layout) (φ : ℕ → ℕ) (n : ℕ) (st : State) : Prop :=
  ∀ d t μ, PathUpTo n d t μ → φ (t 0) + ∑ i ∈ Finset.Ico 1 (n + 1), μ i ≤ st.value L (t n)

/-! ### Modular arithmetic -/

/-- Rotating back by `d % R` undoes the addition of `d` modulo `R`. -/
theorem mod_add_sub_mod {R : ℕ} (hR : 0 < R) (r d : ℕ) :
    ((r + d) % R + R - d % R) % R = r % R := by
  have h1 := Nat.mod_lt r hR
  have h2 := Nat.mod_lt d hR
  rw [Nat.add_mod]
  rcases lt_or_ge (r % R + d % R) R with h | h
  · rw [Nat.mod_eq_of_lt h, show r % R + d % R + R - d % R = r % R + R by omega,
      Nat.add_mod_right, Nat.mod_mod]
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (show r % R + d % R - R < R by omega),
      show r % R + d % R - R + R - d % R = r % R by omega, Nat.mod_mod]

section

variable {L : Layout}

/-- The number of fields is positive. -/
theorem three_R_pos (hR : 3 * L.R = M) : 0 < L.R := by
  simp only [M] at hR; omega

/-- Residues modulo `M = 3 R` determine the residues modulo `3`. -/
theorem mod_three_of_dvd {a : ℕ} (hR : 3 * L.R = M) : a % M % 3 = a % 3 :=
  Nat.mod_mod_of_dvd a ⟨L.R, hR.symm⟩

/-- Residues modulo `M = 3 R` determine the residues modulo `R`. -/
theorem mod_R_of_dvd {a : ℕ} (hR : 3 * L.R = M) : a % M % L.R = a % L.R :=
  Nat.mod_mod_of_dvd a ⟨3, by rw [← hR, mul_comm]⟩

/-- A unit modulo `M` is not divisible by `3`. -/
theorem mod_three_ne_zero {r : ℕ} (hr : Nat.Coprime r M) : r % 3 ≠ 0 := by
  intro h
  exact not_coprime_of_dvd Nat.prime_three (by norm_num [M]) (Nat.dvd_of_mod_eq_zero h) hr

/-- A unit modulo `M = 3 R` is a unit modulo `R`. -/
theorem coprime_mod_R {r : ℕ} (hR : 3 * L.R = M) (hr : Nat.Coprime r M) :
    Nat.Coprime (r % L.R) L.R := by
  rw [ZMod.coprime_mod_iff_coprime]
  exact Nat.Coprime.coprime_dvd_right ⟨3, by rw [← hR, mul_comm]⟩ hr

/-- A gap `d ≡ 2 i [MOD M]` satisfies `d ≡ 2 i [MOD 3]`. -/
theorem gap_mod_three {i d : ℕ} (hR : 3 * L.R = M) (hd : d % M = 2 * i % M) :
    d % 3 = 2 * i % 3 := by
  rw [← mod_three_of_dvd (L := L) hR, hd, mod_three_of_dvd (L := L) hR]

/-- A gap `d ≡ 2 i [MOD M]` satisfies `d ≡ 2 i [MOD R]`. -/
theorem gap_mod_R {i d : ℕ} (hR : 3 * L.R = M) (hd : d % M = 2 * i % M) :
    d % L.R = 2 * i % L.R := by
  rw [← mod_R_of_dvd hR, hd, mod_R_of_dvd hR]

end

namespace Layout.WF

variable {L : Layout} (hL : L.WF)
include hL

/-- The iterates of the chain step along a run of units. -/
theorem field_shift_iterate {x B d r : ℕ} (hR : 0 < L.R) (hx : L.Bounded x B) :
    ∀ j, B + j < 2 ^ L.b → (∀ l, 1 ≤ l → l ≤ j → Nat.Coprime ((r + l * d) % L.R) L.R) →
      field L.b ((L.shift (d % L.R))^[j] x) ((r + j * d) % L.R) = field L.b x (r % L.R) + j
  | 0, _, _ => by simp
  | j + 1, hj, hco => by
    have hk : d % L.R ≤ L.R := (Nat.mod_lt d hR).le
    rw [Function.iterate_succ_apply', (hL.shift (hL.bounded_shift_iterate hk hx j (by omega))
      (by omega) hk).2 _ (Nat.mod_lt _ hR) (hco (j + 1) (by omega) le_rfl),
      show r + (j + 1) * d = r + j * d + d by ring, mod_add_sub_mod hR,
      field_shift_iterate hR hx j (by omega) fun l hl hlj => hco l hl (by omega)]
    ring

/-- Both arguments of a fieldwise maximum are dominated by it. -/
theorem le_field_pmax {a x A X : ℕ} (ha : L.Bounded a A) (hx : L.Bounded x X)
    (hA : A < 2 ^ (L.b - 1)) (hX : X < 2 ^ (L.b - 1)) (t : ℕ) :
    field L.b a t ≤ field L.b (L.pmax a x) t ∧ field L.b x t ≤ field L.b (L.pmax a x) t := by
  rw [(hL.pmax ha hx hA hX).2 t]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- A run within one component (`3 ∣ i`): `chainMax` dominates the runs of the component. -/
theorem chain_run {w B n d r m : ℕ} (hR : 0 < L.R) (hw : L.Bounded w B)
    (hBn : B + n < 2 ^ (L.b - 1)) (hmn : m ≤ n)
    (hco : ∀ l, 1 ≤ l → l ≤ m → Nat.Coprime ((r + l * d) % L.R) L.R) :
    L.Bounded (L.chainMax (d % L.R) n w w) (B + n) ∧
      field L.b w (r % L.R) + m ≤ field L.b (L.chainMax (d % L.R) n w w) ((r + m * d) % L.R) := by
  have hpow := hL.pow_pred_lt
  obtain ⟨hb, hge, hiter⟩ :=
    hL.chainMax (Nat.mod_lt d hR).le n hw hw hBn (by omega)
  refine ⟨hb.mono (by omega), ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hge (r % L.R)
  · rw [← hL.field_shift_iterate hR hw m (by omega) hco]
    exact hiter m hm hmn _

end Layout.WF

namespace Layout

variable {L : Layout}

/-- A successful step: the bound stays below the guard bit, and the components are updated by
`stepComps`. -/
theorem step_eq_some {i : ℕ} {st st' : State} :
    L.step i st = some st' ↔ st.bound + runBound i < 2 ^ (L.b - 1) ∧
      st' = ⟨(L.stepComps i st.w₁ st.w₂).1, (L.stepComps i st.w₁ st.w₂).2, st.offset,
        st.bound + runBound i⟩ := by
  simp only [Layout.step]
  cases h : decide (st.bound + runBound i < 2 ^ (L.b - 1)) <;> simp_all [eq_comm]

/-- For `i ≡ 1 [MOD 3]`, the runs move the class `2` to the class `1`. -/
theorem stepComps_of_mod_one {i w₁ w₂ : ℕ} (h : i % 3 = 1) :
    L.stepComps i w₁ w₂ = (L.pmax w₁ (L.shift (2 * i % L.R) w₂), w₂) := by
  simp [Layout.stepComps, h]

/-- For `i ≡ 2 [MOD 3]`, the runs move the class `1` to the class `2`. -/
theorem stepComps_of_mod_two {i w₁ w₂ : ℕ} (h : i % 3 = 2) :
    L.stepComps i w₁ w₂ = (w₁, L.pmax w₂ (L.shift (2 * i % L.R) w₁)) := by
  simp [Layout.stepComps, h]

/-- For `3 ∣ i`, the runs stay in their class modulo `3`. -/
theorem stepComps_of_mod_zero {i w₁ w₂ : ℕ} (h : i % 3 = 0) :
    L.stepComps i w₁ w₂ = (L.chainMax (2 * i % L.R) (runBound i) w₁ w₁,
      L.chainMax (2 * i % L.R) (runBound i) w₂ w₂) := by
  simp [Layout.stepComps, h]

end Layout

/-- For `3 ∤ i`, runs have length at most one. -/
theorem runBound_of_mod_ne_zero {i : ℕ} (h : i % 3 ≠ 0) : runBound i = 1 := by
  rw [runBound_eq, ite_eq_left (fun h3 => h (Nat.mod_eq_zero_of_dvd h3))]

/-- The component of the class `1` is `w₁`. -/
theorem State.comp_one (st : State) : st.comp 1 = st.w₁ := rfl

/-- The component of the class `2` is `w₂`. -/
theorem State.comp_two (st : State) : st.comp 2 = st.w₂ := by simp [State.comp]

namespace Layout.WF

variable {L : Layout} (hL : L.WF)
include hL

/-- **Soundness of a step**: a successful step `i` of the value iteration dominates the
max-plus operator for the gap `d ≡ 2 i [MOD M]`: `value st r + m ≤ value st' (r + m d)` for
every run of units of length `m` from a unit `r`. -/
theorem step (hR : 3 * L.R = M) {i : ℕ} (hi : 0 < i) (hiM : i < M) {st st' : State}
    (h : L.step i st = some st') (hg : st.Good L) :
    st'.Good L ∧ st'.offset = st.offset ∧
      ∀ d r m, d % M = 2 * i % M → Nat.Coprime r M → IsRun d r m →
        st.value L r + m ≤ st'.value L (r + m * d) := by
  have hRpos := three_R_pos hR
  obtain ⟨hB, rfl⟩ := Layout.step_eq_some.mp h
  have hpow := hL.pow_pred_lt
  have hkR : 2 * i % L.R ≤ L.R := (Nat.mod_lt _ hRpos).le
  have hbnd := hg.bound_lt
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h0 | h1 | h2
  · -- `3 ∣ i`: the runs stay in their class modulo `3`
    rw [Layout.stepComps_of_mod_zero h0]
    refine ⟨⟨hB, (hL.chainMax hkR _ hg.w₁ hg.w₁ hB hbnd).1.mono (by dsimp only; omega),
      (hL.chainMax hkR _ hg.w₂ hg.w₂ hB hbnd).1.mono (by dsimp only; omega)⟩, rfl,
      fun d r m hd hr hrun => ?_⟩
    have hm := hrun.le_runBound hi hiM hd hr
    have hd0 : d % 3 = 0 := by rw [gap_mod_three hR hd]; omega
    have hmd : m * d % 3 = 0 := by rw [Nat.mul_mod, hd0, mul_zero, Nat.zero_mod]
    have key : ∀ w, L.Bounded w st.bound → field L.b w (r % L.R) + m ≤
        field L.b (L.chainMax (2 * i % L.R) (runBound i) w w) ((r + m * d) % L.R) := by
      intro w hw
      rw [← gap_mod_R hR hd]
      exact (hL.chain_run hRpos hw hB hm fun l hl hlm => coprime_mod_R hR (hrun l hl hlm)).2
    have hr3 := mod_three_ne_zero hr
    simp only [State.value]
    rw [show (r + m * d) % 3 = r % 3 by omega]
    rcases (by omega : r % 3 = 1 ∨ r % 3 = 2) with hc | hc
    · rw [hc, State.comp_one, State.comp_one]; have := key _ hg.w₁; dsimp only; omega
    · rw [hc, State.comp_two, State.comp_two]; have := key _ hg.w₂; dsimp only; omega
  · -- `i ≡ 1 [MOD 3]`: a run moves the class `2` to the class `1`
    have hL1 := runBound_of_mod_ne_zero (by omega : i % 3 ≠ 0)
    rw [Layout.stepComps_of_mod_one h1]
    rw [hL1] at hB ⊢
    have hs := hL.shift hg.w₂ (by omega) hkR
    have hp := hL.pmax hg.w₁ hs.1 hbnd (by omega)
    refine ⟨⟨hB, hp.1.mono (by dsimp only; omega), hg.w₂.mono (by dsimp only; omega)⟩, rfl,
      fun d r m hd hr hrun => ?_⟩
    have hm := hrun.le_runBound hi hiM hd hr
    rw [hL1] at hm
    have hr3 := mod_three_ne_zero hr
    simp only [State.value]
    rcases Nat.lt_or_ge m 1 with hm0 | hm1
    · obtain rfl : m = 0 := by omega
      simp only [zero_mul, add_zero]
      rcases (by omega : r % 3 = 1 ∨ r % 3 = 2) with hc | hc
      · rw [hc, State.comp_one, State.comp_one]
        have := (hL.le_field_pmax hg.w₁ hs.1 hbnd (by omega) (r % L.R)).1
        dsimp only
        omega
      · rw [hc, State.comp_two, State.comp_two]
    · obtain rfl : m = 1 := by omega
      have hrd : Nat.Coprime (r + d) M := by simpa using hrun 1 le_rfl le_rfl
      have hd2 : d % 3 = 2 := by rw [gap_mod_three hR hd]; omega
      have hrd3 := mod_three_ne_zero hrd
      have hc : r % 3 = 2 := by omega
      rw [one_mul, show (r + d) % 3 = 1 by omega, hc, State.comp_two, State.comp_one]
      have := (hL.le_field_pmax hg.w₁ hs.1 hbnd (by omega) ((r + d) % L.R)).2
      rw [hs.2 _ (Nat.mod_lt _ hRpos) (coprime_mod_R hR hrd)] at this
      rw [← gap_mod_R hR hd] at this ⊢
      rw [mod_add_sub_mod hRpos] at this
      dsimp only
      omega
  · -- `i ≡ 2 [MOD 3]`: a run moves the class `1` to the class `2`
    have hL1 := runBound_of_mod_ne_zero (by omega : i % 3 ≠ 0)
    rw [Layout.stepComps_of_mod_two h2]
    rw [hL1] at hB ⊢
    have hs := hL.shift hg.w₁ (by omega) hkR
    have hp := hL.pmax hg.w₂ hs.1 hbnd (by omega)
    refine ⟨⟨hB, hg.w₁.mono (by dsimp only; omega), hp.1.mono (by dsimp only; omega)⟩, rfl,
      fun d r m hd hr hrun => ?_⟩
    have hm := hrun.le_runBound hi hiM hd hr
    rw [hL1] at hm
    have hr3 := mod_three_ne_zero hr
    simp only [State.value]
    rcases Nat.lt_or_ge m 1 with hm0 | hm1
    · obtain rfl : m = 0 := by omega
      simp only [zero_mul, add_zero]
      rcases (by omega : r % 3 = 1 ∨ r % 3 = 2) with hc | hc
      · rw [hc, State.comp_one, State.comp_one]
      · rw [hc, State.comp_two, State.comp_two]
        have := (hL.le_field_pmax hg.w₂ hs.1 hbnd (by omega) (r % L.R)).1
        dsimp only
        omega
    · obtain rfl : m = 1 := by omega
      have hrd : Nat.Coprime (r + d) M := by simpa using hrun 1 le_rfl le_rfl
      have hd1 : d % 3 = 1 := by rw [gap_mod_three hR hd]; omega
      have hrd3 := mod_three_ne_zero hrd
      have hc : r % 3 = 1 := by omega
      rw [one_mul, show (r + d) % 3 = 2 by omega, hc, State.comp_two, State.comp_one]
      have := (hL.le_field_pmax hg.w₂ hs.1 hbnd (by omega) ((r + d) % L.R)).2
      rw [hs.2 _ (Nat.mod_lt _ hRpos) (coprime_mod_R hR hrd)] at this
      rw [← gap_mod_R hR hd] at this ⊢
      rw [mod_add_sub_mod hRpos] at this
      dsimp only
      omega

end Layout.WF

end DP

end Erdos455
