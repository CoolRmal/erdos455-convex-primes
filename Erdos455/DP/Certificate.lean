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

/-! The packed constants of `layout17` are closed forms (checked by the kernel with a few GMP
operations), whose fields are known by `Erdos455.Packed.spec_unitInd`. -/

/-- The primes dividing `85085`. -/
def primes : List ℕ := [5, 7, 11, 13, 17]

theorem b_eq : layout17.b = 9 := by decide +kernel

theorem R_eq : layout17.R = 85085 := by decide +kernel

theorem ones_eq : layout17.ones = repC 9 1 85085 := by decide +kernel

theorem highs_eq : layout17.highs = repC 9 1 85085 * 2 ^ 8 := by decide +kernel

theorem uones_eq : layout17.uones = unitInd 9 85085 primes := by decide +kernel

theorem umask_eq : layout17.umask = unitInd 9 85085 primes * (2 ^ 9 - 1) := by decide +kernel

theorem uhighs_eq : layout17.uhighs = unitInd 9 85085 primes * 2 ^ 8 := by decide +kernel

/-- The units modulo `85085` are the numbers divisible by none of its prime factors. -/
theorem coprime_iff (t : ℕ) : Nat.Coprime t 85085 ↔ ∀ p ∈ primes, ¬p ∣ t := by
  have hp : ∀ p ∈ primes, p.Prime := by decide
  rw [show (85085 : ℕ) = 5 * 7 * 11 * 13 * 17 by norm_num]
  simp only [Nat.coprime_mul_iff_right, primes, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  simp only [primes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hp
  rw [Nat.coprime_comm.trans (hp.1.coprime_iff_not_dvd), Nat.coprime_comm.trans
    (hp.2.1.coprime_iff_not_dvd), Nat.coprime_comm.trans (hp.2.2.1.coprime_iff_not_dvd),
    Nat.coprime_comm.trans (hp.2.2.2.1.coprime_iff_not_dvd),
    Nat.coprime_comm.trans (hp.2.2.2.2.coprime_iff_not_dvd)]
  tauto

end layout17

open Packed in
/-- The packed constants of `layout17` have the specified fields. -/
theorem layout17_wf : layout17.WF := by
  have hb : 0 < 9 := by norm_num
  have hones : Spec 9 85085 (repC 9 1 85085) fun _ => 1 :=
    rep_eq_repC (b := 9) (m := 1) (by norm_num) ▸ spec_rep_one hb 85085
  have hunits := spec_unitInd hb (R := 85085) layout17.primes (by decide)
  have hind : ∀ t, (if ∀ p ∈ layout17.primes, ¬p ∣ t then 1 else 0) =
      if Nat.Coprime t 85085 then 1 else 0 := fun t => by
    rw [if_congr (layout17.coprime_iff t).symm rfl rfl]
  have hmul : ∀ (c : Prop) [Decidable c] (k : ℕ), (if c then 1 else 0) * k = if c then k else 0 :=
    fun c _ k => by split_ifs <;> simp
  have hunits' : Spec 9 85085 (unitInd 9 85085 layout17.primes)
      fun t => if Nat.Coprime t 85085 then 1 else 0 :=
    ⟨hunits.lt, fun t ht => (hunits.field_eq t ht).trans (hind t)⟩
  have spec_mul : ∀ {x : ℕ} {f : ℕ → ℕ} (k : ℕ), Spec 9 85085 x f → (∀ t, f t ≤ 1) →
      k < 2 ^ 9 → Spec 9 85085 (x * k) fun t => f t * k := fun k hx hf hk =>
    hx.mul_const hb fun t _ =>
      lt_of_le_of_lt ((Nat.mul_le_mul_right k (hf t)).trans (by rw [one_mul])) hk
  have hf1 : ∀ t, (if Nat.Coprime t 85085 then 1 else 0) ≤ 1 := fun t => by split_ifs <;> simp
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [layout17.b_eq, layout17.R_eq]
  · rw [layout17.ones_eq]; exact hones
  · rw [layout17.highs_eq]
    exact ⟨(spec_mul _ hones (fun _ => le_rfl) (by norm_num)).lt, fun t ht => by
      rw [(spec_mul _ hones (fun _ => le_rfl) (by norm_num)).field_eq t ht]; norm_num⟩
  · rw [layout17.umask_eq]
    exact ⟨(spec_mul _ hunits' hf1 (by norm_num)).lt, fun t ht => by
      rw [(spec_mul _ hunits' hf1 (by norm_num)).field_eq t ht, hmul]⟩
  · rw [layout17.uones_eq]; exact hunits'
  · rw [layout17.uhighs_eq]
    exact ⟨(spec_mul _ hunits' hf1 (by norm_num)).lt, fun t ht => by
      rw [(spec_mul _ hunits' hf1 (by norm_num)).field_eq t ht, hmul]⟩

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
