/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.DP.Gen

/-!
# The certificate for the dynamic program

Proposition 11 of the paper, in the path form used by the counting argument: there is a
potential `φ` on the residues modulo `M`, with values in `[0, 255]`, such that along every path
of runs over one period of gap values, `φ (t 0) + ∑ μ i ≤ φ (t (M - 1)) + 295318`.

The potential is computed at elaboration time by one period of the value iteration from zero
(`dp_certificate%`, see `Erdos455.DP.Gen`); up to an additive constant it is the potential of
the paper (whose values span `[-109, 0]`). The kernel then checks one period of the value
iteration from `φ`, in `499` chunks of `512` steps (`Erdos455.DP.phi17.chunk_k`), and the final
comparison with `φ + 295318` (`Erdos455.DP.phi17_final`).

## Main statements

* `Erdos455.exists_potential`: Proposition 11.
-/

-- The generator refers to earlier theorems of this file, whose kernel checks must have finished.
set_option Elab.async false

namespace Erdos455

namespace DP

-- The packed layout for the units modulo `M = 3 · 85085`: two components of `85085` fields of
-- `9` bits.
dp_layout% layout17 85085 9

theorem layout17_R : 3 * layout17.R = M := by decide +kernel

namespace layout17

open Packed

/-! The packed constants of `layout17` have the specified fields (checked by the kernel). -/

theorem ones_spec : checkSpec layout17.b layout17.R (fun _ => 1) layout17.ones = true := by
  decide +kernel

theorem highs_spec :
    checkSpec layout17.b layout17.R (fun _ => 2 ^ (layout17.b - 1)) layout17.highs = true := by
  decide +kernel

theorem umask_spec : checkSpec layout17.b layout17.R
    (fun t => if Nat.Coprime t layout17.R then 2 ^ layout17.b - 1 else 0) layout17.umask =
      true := by
  decide +kernel

theorem uones_spec : checkSpec layout17.b layout17.R
    (fun t => if Nat.Coprime t layout17.R then 1 else 0) layout17.uones = true := by
  decide +kernel

theorem uhighs_spec : checkSpec layout17.b layout17.R
    (fun t => if Nat.Coprime t layout17.R then 2 ^ (layout17.b - 1) else 0) layout17.uhighs =
      true := by
  decide +kernel

end layout17

/-- The packed constants of `layout17` have the specified fields. -/
theorem layout17_wf : layout17.WF where
  two_le_b := by decide +kernel
  R_pos := by decide +kernel
  ones := Packed.spec_of_checkSpec layout17.ones_spec
  highs := Packed.spec_of_checkSpec layout17.highs_spec
  umask := Packed.spec_of_checkSpec layout17.umask_spec
  uones := Packed.spec_of_checkSpec layout17.uones_spec
  uhighs := Packed.spec_of_checkSpec layout17.uhighs_spec

-- The potential `phi17`, the value iteration from it in chunks, and the final state.
dp_certificate% layout17 32 512 phi17 layout17_wf layout17_R

/-- After one period from `phi17`, the values are at most `phi17 + 295318`. -/
theorem phi17_final : layout17.finalB phi17 phi17.final growth = true := by decide +kernel

end DP

open DP Packed

/-- **Proposition 11** (path form): the dynamic program gains at most `growth = 295318` per
period, up to a bounded potential. -/
theorem exists_potential : ∃ φ : ℕ → ℕ, (∀ r, φ r ≤ 255) ∧ (∀ r, φ (r % M) = φ r) ∧
    ∀ d t μ : ℕ → ℕ, PeriodPath d t μ →
      φ (t 0) + ∑ i ∈ Finset.Ico 1 M, μ i ≤ φ (t (M - 1)) + growth := by
  obtain ⟨hg, hsim⟩ := phi17.final_sim
  have hg₀ := phi17.sim_0.1
  have hbound : phi17.bound < 2 ^ (layout17.b - 1) := hg₀.bound_lt
  have hb : layout17.b = 9 := by decide +kernel
  have hoff : phi17.offset = 0 := by decide +kernel
  refine ⟨phi17.value layout17, fun r => ?_, fun r => ?_, fun d t μ hp => ?_⟩
  · have hfield : field layout17.b (phi17.comp (r % 3)) (r % layout17.R) ≤ phi17.bound := by
      simp only [State.comp]
      split_ifs
      · exact hg₀.w₁.2 _
      · exact hg₀.w₂.2 _
      · simp
    rw [hb] at hbound
    simp only [State.value, hoff]
    omega
  · simp only [State.value, mod_three_of_dvd layout17_R, mod_R_of_dvd layout17_R]
  · have hpath := hp.pathUpTo
    have h₁ : phi17.value layout17 (t 0) + ∑ i ∈ Finset.Ico 1 M, μ i ≤
        phi17.final.value layout17 (t (M - 1)) := hsim d t μ hpath
    have h₂ := layout17_wf.value_le_of_finalB phi17_final hg₀ hg (t (M - 1))
      (mod_three_ne_zero (hpath.coprime (M - 1) le_rfl))
    omega

end Erdos455
