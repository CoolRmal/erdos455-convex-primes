/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.DP.Sound
import Erdos455.DP.Runs

/-!
# Soundness of the value iteration

A `State` represents the function `r ↦ State.value L st r` on the units modulo `M = 15 R`. We
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

/-! ### Quads -/

namespace Quad

/-- The entries of `Quad.ofFun f` are the values of `f`. -/
theorem get_ofFun (f : ℕ → ℕ) {c : ℕ} (hc : c % 5 = c) (hc0 : c ≠ 0) :
    (Quad.ofFun f).get c = f c := by
  have : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rfl

/-- The entries outside the classes `1, 2, 3, 4` vanish. -/
theorem get_of_not_mem (q : Quad) {c : ℕ} (h : ¬(c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4)) :
    q.get c = 0 := by
  simp only [get]
  push Not at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp [h1, h2, h3, h4]

/-- All four entries of a quad are bounded by `B`. -/
def Bounded (L : Layout) (q : Quad) (B : ℕ) : Prop :=
  L.Bounded q.q₁ B ∧ L.Bounded q.q₂ B ∧ L.Bounded q.q₃ B ∧ L.Bounded q.q₄ B

theorem Bounded.get {L : Layout} {q : Quad} {B : ℕ} (h : q.Bounded L B) (c : ℕ) :
    L.Bounded (q.get c) B := by
  by_cases hc : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4
  · rcases hc with rfl | rfl | rfl | rfl
    exacts [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · rw [get_of_not_mem q hc]
    exact ⟨Nat.two_pow_pos _, fun t => by simp⟩

theorem Bounded.mono {L : Layout} {q : Quad} {B B' : ℕ} (h : q.Bounded L B) (hB : B ≤ B') :
    q.Bounded L B' :=
  ⟨h.1.mono hB, h.2.1.mono hB, h.2.2.1.mono hB, h.2.2.2.mono hB⟩

theorem bounded_ofFun {L : Layout} {f : ℕ → ℕ} {B : ℕ} (h : ∀ c, L.Bounded (f c) B) :
    (Quad.ofFun f).Bounded L B :=
  ⟨h 1, h 2, h 3, h 4⟩

theorem bounded_of_get {L : Layout} {q : Quad} {B : ℕ} (h : ∀ c, L.Bounded (q.get c) B) :
    q.Bounded L B :=
  ⟨h 1, h 2, h 3, h 4⟩

/-- `0` is bounded by every bound. -/
theorem _root_.Erdos455.DP.Layout.bounded_zero (L : Layout) (B : ℕ) : L.Bounded 0 B :=
  ⟨Nat.two_pow_pos _, fun t => by simp⟩

/-- The zero quad is bounded by every bound. -/
theorem bounded_zero (L : Layout) (B : ℕ) : (⟨0, 0, 0, 0⟩ : Quad).Bounded L B :=
  ⟨L.bounded_zero B, L.bounded_zero B, L.bounded_zero B, L.bounded_zero B⟩

end Quad

/-- The component of a state holding the residues `≡ c [MOD 3]`. -/
def State.comp (st : State) (c : ℕ) : Quad :=
  if c = 1 then st.w₁ else if c = 2 then st.w₂ else ⟨0, 0, 0, 0⟩

/-- The value of a state at the residue `r` (meaningful for units `r`). -/
def State.value (L : Layout) (st : State) (r : ℕ) : ℕ :=
  field L.b ((st.comp (r % 3)).get (r % 5)) (r % L.R) + st.offset

/-- The invariant of the states: the bound is below the guard bit and bounds all fields. -/
structure State.Good (L : Layout) (st : State) : Prop where
  bound_lt : st.bound < 2 ^ (L.b - 1)
  w₁ : st.w₁.Bounded L st.bound
  w₂ : st.w₂.Bounded L st.bound

/-- The components of a state satisfying the invariant are bounded. -/
theorem State.Good.comp {L : Layout} {st : State} (hg : st.Good L) (c : ℕ) :
    (st.comp c).Bounded L st.bound := by
  simp only [State.comp]
  split_ifs
  · exact hg.w₁
  · exact hg.w₂
  · exact Quad.bounded_zero L _

/-- The component of the class `1` is `w₁`. -/
theorem State.comp_one (st : State) : st.comp 1 = st.w₁ := rfl

/-- The component of the class `2` is `w₂`. -/
theorem State.comp_two (st : State) : st.comp 2 = st.w₂ := by simp [State.comp]

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

/-- The class modulo `5` from which a move by `d` reaches `(r + d) % 5` is `r % 5`. -/
theorem src5_add (r d : ℕ) : Layout.src5 (d % 5) ((r + d) % 5) = r % 5 :=
  mod_add_sub_mod (by norm_num) r d

section

variable {L : Layout}

/-- The number of fields is positive. -/
theorem R_pos (hR : 15 * L.R = M) : 0 < L.R := by
  simp only [M] at hR; omega

/-- Residues modulo `M = 15 R` determine the residues modulo `3`. -/
theorem mod_three_of_dvd {a : ℕ} (hR : 15 * L.R = M) : a % M % 3 = a % 3 :=
  Nat.mod_mod_of_dvd a ⟨5 * L.R, by rw [← hR]; ring⟩

/-- Residues modulo `M = 15 R` determine the residues modulo `5`. -/
theorem mod_five_of_dvd {a : ℕ} (hR : 15 * L.R = M) : a % M % 5 = a % 5 :=
  Nat.mod_mod_of_dvd a ⟨3 * L.R, by rw [← hR]; ring⟩

/-- Residues modulo `M = 15 R` determine the residues modulo `R`. -/
theorem mod_R_of_dvd {a : ℕ} (hR : 15 * L.R = M) : a % M % L.R = a % L.R :=
  Nat.mod_mod_of_dvd a ⟨15, by rw [← hR, mul_comm]⟩

/-- A unit modulo `M` is not divisible by `3`. -/
theorem mod_three_ne_zero {r : ℕ} (hr : Nat.Coprime r M) : r % 3 ≠ 0 := by
  intro h
  exact not_coprime_of_dvd Nat.prime_three (by norm_num [M]) (Nat.dvd_of_mod_eq_zero h) hr

/-- A unit modulo `M` is not divisible by `5`. -/
theorem mod_five_ne_zero {r : ℕ} (hr : Nat.Coprime r M) : r % 5 ≠ 0 := by
  intro h
  exact not_coprime_of_dvd (by norm_num) (by norm_num [M]) (Nat.dvd_of_mod_eq_zero h) hr

/-- A unit modulo `M = 15 R` is a unit modulo `R`. -/
theorem coprime_mod_R {r : ℕ} (hR : 15 * L.R = M) (hr : Nat.Coprime r M) :
    Nat.Coprime (r % L.R) L.R := by
  rw [ZMod.coprime_mod_iff_coprime]
  exact Nat.Coprime.coprime_dvd_right ⟨15, by rw [← hR, mul_comm]⟩ hr

/-- A gap `d ≡ 2 i [MOD M]` satisfies `d ≡ 2 i [MOD 3]`. -/
theorem gap_mod_three {i d : ℕ} (hR : 15 * L.R = M) (hd : d % M = 2 * i % M) :
    d % 3 = 2 * i % 3 := by
  rw [← mod_three_of_dvd (L := L) hR, hd, mod_three_of_dvd (L := L) hR]

/-- A gap `d ≡ 2 i [MOD M]` satisfies `d ≡ 2 i [MOD 5]`. -/
theorem gap_mod_five {i d : ℕ} (hR : 15 * L.R = M) (hd : d % M = 2 * i % M) :
    d % 5 = 2 * i % 5 := by
  rw [← mod_five_of_dvd (L := L) hR, hd, mod_five_of_dvd (L := L) hR]

/-- A gap `d ≡ 2 i [MOD M]` satisfies `d ≡ 2 i [MOD R]`. -/
theorem gap_mod_R {i d : ℕ} (hR : 15 * L.R = M) (hd : d % M = 2 * i % M) :
    d % L.R = 2 * i % L.R := by
  rw [← mod_R_of_dvd hR, hd, mod_R_of_dvd hR]

end

namespace Layout.WF

variable {L : Layout} (hL : L.WF)
include hL

/-- Both arguments of a fieldwise maximum are dominated by it. -/
theorem le_field_pmax {a x A X : ℕ} (ha : L.Bounded a A) (hx : L.Bounded x X)
    (hA : A < 2 ^ (L.b - 1)) (hX : X < 2 ^ (L.b - 1)) (t : ℕ) :
    field L.b a t ≤ field L.b (L.pmax a x) t ∧ field L.b x t ≤ field L.b (L.pmax a x) t := by
  rw [(hL.pmax ha hx hA hX).2 t]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- A chain step within a class modulo `3` keeps the chain bounded, one more than before. -/
theorem bounded_chainStep {δ k B : ℕ} (hk : k ≤ L.R) {p : Quad × (ℕ → Bool)}
    (hp : p.1.Bounded L B) (hB : B + 1 < 2 ^ L.b) :
    (L.chainStep δ k p).1.Bounded L (B + 1) := by
  have key : ∀ (a : Bool) (y : ℕ), L.Bounded y B →
      L.Bounded (bif a then L.shift k y else 0) (B + 1) := fun a y hy => by
    cases a
    · exact L.bounded_zero _
    · exact (hL.shift hy hB hk).1
  exact Quad.bounded_ofFun fun c => key _ _ (hp.get _)

/-- Folding a chain into the accumulator keeps it bounded and dominates both. -/
theorem accum {A B : ℕ} {acc : Quad} {p : Quad × (ℕ → Bool)} (hacc : acc.Bounded L A)
    (hp : p.1.Bounded L B) (hA : A < 2 ^ (L.b - 1)) (hB : B < 2 ^ (L.b - 1)) :
    (L.accum acc p).Bounded L (max A B) ∧
      (∀ c, c % 5 = c → c ≠ 0 → ∀ t, field L.b (acc.get c) t ≤ field L.b ((L.accum acc p).get c) t)
      ∧ ∀ c, c % 5 = c → c ≠ 0 → p.2 c = true → ∀ t,
        field L.b (p.1.get c) t ≤ field L.b ((L.accum acc p).get c) t := by
  refine ⟨Quad.bounded_ofFun fun c => ?_, fun c hc hc0 t => ?_, fun c hc hc0 hal t => ?_⟩
  · cases p.2 c
    · exact (hacc.get c).mono (le_max_left _ _)
    · exact (hL.pmax (hacc.get c) (hp.get c) hA hB).1
  · rw [Layout.accum, Quad.get_ofFun _ hc hc0]
    cases p.2 c
    · exact le_rfl
    · exact (hL.le_field_pmax (hacc.get c) (hp.get c) hA hB t).1
  · rw [Layout.accum, Quad.get_ofFun _ hc hc0, hal]
    exact (hL.le_field_pmax (hacc.get c) (hp.get c) hA hB t).2

/-- The iterates of the chain step stay bounded. -/
theorem bounded_chainStep_iterate {δ k B : ℕ} (hk : k ≤ L.R) {p : Quad × (ℕ → Bool)}
    (hp : p.1.Bounded L B) : ∀ j, B + j < 2 ^ L.b → ((L.chainStep δ k)^[j] p).1.Bounded L (B + j)
  | 0, _ => hp
  | j + 1, h => by
    rw [Function.iterate_succ_apply']
    exact hL.bounded_chainStep hk (bounded_chainStep_iterate hk hp j (by omega)) (by omega)

/-- `chains δ k n p acc` dominates `acc` and the live entries of the iterates of the chain
step. -/
theorem chains {δ k : ℕ} (hk : k ≤ L.R) :
    ∀ (n : ℕ) {p : Quad × (ℕ → Bool)} {acc : Quad} {B A : ℕ}, p.1.Bounded L B →
      acc.Bounded L A → B + n < 2 ^ (L.b - 1) → A < 2 ^ (L.b - 1) →
      (L.chains δ k n p acc).Bounded L (max A (B + n)) ∧
        (∀ c, c % 5 = c → c ≠ 0 → ∀ t,
          field L.b (acc.get c) t ≤ field L.b ((L.chains δ k n p acc).get c) t) ∧
        ∀ j, 1 ≤ j → j ≤ n → ∀ c, c % 5 = c → c ≠ 0 → ((L.chainStep δ k)^[j] p).2 c = true →
          ∀ t, field L.b (((L.chainStep δ k)^[j] p).1.get c) t ≤
            field L.b ((L.chains δ k n p acc).get c) t
  | 0, p, acc, B, A, _, hacc, _, _ =>
    ⟨hacc.mono (le_max_left _ _), fun _ _ _ _ => le_rfl, fun j hj hjn => by omega⟩
  | n + 1, p, acc, B, A, hp, hacc, hBn, hA => by
    have hpow := hL.pow_pred_lt
    have hp' := hL.bounded_chainStep (δ := δ) hk hp (by omega)
    obtain ⟨hacc', hdom₁, hdom₂⟩ := hL.accum hacc hp' hA (by omega)
    obtain ⟨hb, hge, hiter⟩ := chains hk n hp' hacc' (by omega) (max_lt hA (by omega))
    have heq : L.chains δ k (n + 1) p acc =
        L.chains δ k n (L.chainStep δ k p) (L.accum acc (L.chainStep δ k p)) := rfl
    rw [heq]
    refine ⟨hb.mono (by omega), fun c hc hc0 t => (hdom₁ c hc hc0 t).trans (hge c hc hc0 t),
      fun j hj hjn c hc hc0 hal t => ?_⟩
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · obtain rfl : j = 1 := by omega
      exact (hdom₂ c hc hc0 hal t).trans (hge c hc hc0 t)
    · have hj' : (L.chainStep δ k)^[j] p = (L.chainStep δ k)^[j - 1] (L.chainStep δ k p) := by
        rw [← Function.iterate_succ_apply, show (j - 1).succ = j by omega]
      rw [hj'] at hal ⊢
      exact hiter (j - 1) (by omega) (by omega) c hc hc0 hal t

/-- The chain along a run of units within a class modulo `3`: after `j` steps, the chain into
the class of `r + j d` is live and its field at `r + j d` is the field of `w` at `r` plus `j`. -/
theorem chainStep_run {w : Quad} {B d r m : ℕ} (hR : 0 < L.R) (hw : w.Bounded L B)
    (hBm : B + m < 2 ^ L.b) (h5 : ∀ l ≤ m, (r + l * d) % 5 ≠ 0)
    (hco : ∀ l, 1 ≤ l → l ≤ m → Nat.Coprime ((r + l * d) % L.R) L.R) :
    ∀ j ≤ m, ((L.chainStep (d % 5) (d % L.R))^[j] (w, (· != 0))).2 ((r + j * d) % 5) = true ∧
      field L.b (((L.chainStep (d % 5) (d % L.R))^[j] (w, (· != 0))).1.get ((r + j * d) % 5))
        ((r + j * d) % L.R) = field L.b (w.get (r % 5)) (r % L.R) + j
  | 0, _ => by simpa using h5 0 (Nat.zero_le _)
  | j + 1, hj => by
    have hk : d % L.R ≤ L.R := (Nat.mod_lt d hR).le
    obtain ⟨hal, hval⟩ := chainStep_run hR hw hBm h5 hco j (by omega)
    have hiter := hL.bounded_chainStep_iterate (δ := d % 5) (p := (w, (· != 0))) hk hw j
      (by omega)
    set p := (L.chainStep (d % 5) (d % L.R))^[j] (w, (· != 0)) with hp
    have hsrc : Layout.src5 (d % 5) ((r + (j + 1) * d) % 5) = (r + j * d) % 5 := by
      rw [show r + (j + 1) * d = r + j * d + d by ring, src5_add]
    have h5' := h5 (j + 1) hj
    have halive : (L.chainStep (d % 5) (d % L.R) p).2 ((r + (j + 1) * d) % 5) = true := by
      simp only [Layout.chainStep, hsrc, hal, Bool.and_true, bne_iff_ne, ne_eq]
      exact h5 j (by omega)
    rw [Function.iterate_succ_apply', ← hp]
    refine ⟨halive, ?_⟩
    have hget : (L.chainStep (d % 5) (d % L.R) p).1.get ((r + (j + 1) * d) % 5) =
        L.shift (d % L.R) (p.1.get ((r + j * d) % 5)) := by
      simp only [Layout.chainStep]
      rw [Quad.get_ofFun _ (Nat.mod_mod _ _) h5']
      have := halive
      simp only [Layout.chainStep] at this
      rw [this, hsrc]
      rfl
    rw [hget, (hL.shift (hiter.get _) (by omega) hk).2 _ (Nat.mod_lt _ hR) (hco _ (by omega) hj),
      show r + (j + 1) * d = r + j * d + d by ring, mod_add_sub_mod hR, hval]
    ring

/-- A move between the classes modulo `3` (for `3 ∤ i`) keeps the fields bounded, dominates the
old values, and dominates the shifted values of the source. -/
theorem transfer {δ k B : ℕ} (hk : k ≤ L.R) {src dst : Quad} (hs : src.Bounded L B)
    (hd : dst.Bounded L B) (hB : B + 1 < 2 ^ (L.b - 1)) :
    (L.transfer δ k src dst).Bounded L (B + 1) ∧
      (∀ c, c % 5 = c → c ≠ 0 → ∀ t,
        field L.b (dst.get c) t ≤ field L.b ((L.transfer δ k src dst).get c) t) ∧
      ∀ c, c % 5 = c → c ≠ 0 → Layout.src5 δ c ≠ 0 → ∀ t,
        field L.b (L.shift k (src.get (Layout.src5 δ c))) t ≤
          field L.b ((L.transfer δ k src dst).get c) t := by
  have hpow := hL.pow_pred_lt
  have hsh : ∀ c, L.Bounded (L.shift k (src.get c)) (B + 1) := fun c =>
    (hL.shift (hs.get c) (by omega) hk).1
  refine ⟨Quad.bounded_ofFun fun c => ?_, fun c hc hc0 t => ?_, fun c hc hc0 hsrc t => ?_⟩
  · cases Layout.src5 δ c != 0
    · exact (hd.get c).mono (by omega)
    · exact (hL.pmax (hd.get c) (hsh _) (by omega) hB).1.mono (by omega)
  · rw [Layout.transfer, Quad.get_ofFun _ hc hc0]
    cases Layout.src5 δ c != 0
    · exact le_rfl
    · exact (hL.le_field_pmax (hd.get c) (hsh _) (by omega) hB t).1
  · rw [Layout.transfer, Quad.get_ofFun _ hc hc0,
      show (Layout.src5 δ c != 0) = true from bne_iff_ne.mpr hsrc]
    exact (hL.le_field_pmax (hd.get c) (hsh _) (by omega) hB t).2

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
theorem stepComps_of_mod_one {i : ℕ} {w₁ w₂ : Quad} (h : i % 3 = 1) :
    L.stepComps i w₁ w₂ = (L.transfer (2 * i % 5) (2 * i % L.R) w₂ w₁, w₂) := by
  simp [Layout.stepComps, h]

/-- For `i ≡ 2 [MOD 3]`, the runs move the class `1` to the class `2`. -/
theorem stepComps_of_mod_two {i : ℕ} {w₁ w₂ : Quad} (h : i % 3 = 2) :
    L.stepComps i w₁ w₂ = (w₁, L.transfer (2 * i % 5) (2 * i % L.R) w₁ w₂) := by
  simp [Layout.stepComps, h]

/-- For `3 ∣ i`, the runs stay in their class modulo `3`. -/
theorem stepComps_of_mod_zero {i : ℕ} {w₁ w₂ : Quad} (h : i % 3 = 0) :
    L.stepComps i w₁ w₂ =
      (L.chains (2 * i % 5) (2 * i % L.R) (runBound i) (w₁, (· != 0)) w₁,
        L.chains (2 * i % 5) (2 * i % L.R) (runBound i) (w₂, (· != 0)) w₂) := by
  simp [Layout.stepComps, h]

end Layout

/-- For `3 ∤ i`, runs have length at most one. -/
theorem runBound_of_mod_ne_zero {i : ℕ} (h : i % 3 ≠ 0) : runBound i = 1 := by
  rw [runBound_eq, ite_eq_left (fun h3 => h (Nat.mod_eq_zero_of_dvd h3))]

namespace Layout.WF

variable {L : Layout} (hL : L.WF)
include hL

/-- A move from the class of `src` to the class of `dst` modulo `3` dominates the runs of
length one: `field src (r % 5) (r % R) + 1 ≤ field (transfer …) ((r + d) % 5) ((r + d) % R)`. -/
theorem transfer_run {B d r : ℕ} (hR : 0 < L.R) {src dst : Quad} (hs : src.Bounded L B)
    (hd : dst.Bounded L B) (hB : B + 1 < 2 ^ (L.b - 1)) (hr5 : r % 5 ≠ 0)
    (hrd5 : (r + d) % 5 ≠ 0) (hco : Nat.Coprime ((r + d) % L.R) L.R) :
    field L.b (src.get (r % 5)) (r % L.R) + 1 ≤
      field L.b ((L.transfer (d % 5) (d % L.R) src dst).get ((r + d) % 5)) ((r + d) % L.R) := by
  have hk : d % L.R ≤ L.R := (Nat.mod_lt d hR).le
  have hpow := hL.pow_pred_lt
  have := (hL.transfer hk hs hd hB).2.2 ((r + d) % 5) (Nat.mod_mod _ _) hrd5
    (by rw [src5_add]; exact hr5) ((r + d) % L.R)
  rw [src5_add, (hL.shift (hs.get _) (by omega) hk).2 _ (Nat.mod_lt _ hR) hco,
    mod_add_sub_mod hR] at this
  exact this

/-- **Soundness of a step**: a successful step `i` of the value iteration dominates the
max-plus operator for the gap `d ≡ 2 i [MOD M]`: `value st r + m ≤ value st' (r + m d)` for
every run of units of length `m` from a unit `r`. -/
theorem step (hR : 15 * L.R = M) {i : ℕ} (hi : 0 < i) (hiM : i < M) {st st' : State}
    (h : L.step i st = some st') (hg : st.Good L) :
    st'.Good L ∧ st'.offset = st.offset ∧
      ∀ d r m, d % M = 2 * i % M → Nat.Coprime r M → IsRun d r m →
        st.value L r + m ≤ st'.value L (r + m * d) := by
  have hRpos := hL.R_pos
  obtain ⟨hB, rfl⟩ := Layout.step_eq_some.mp h
  have hpow := hL.pow_pred_lt
  have hkR : 2 * i % L.R ≤ L.R := (Nat.mod_lt _ hRpos).le
  have hbnd := hg.bound_lt
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h0 | h1 | h2
  · -- `3 ∣ i`: the runs stay in their class modulo `3`
    rw [Layout.stepComps_of_mod_zero h0]
    have hc₁ := hL.chains (δ := 2 * i % 5) hkR (runBound i) (p := (st.w₁, (· != 0))) hg.w₁
      hg.w₁ hB hbnd
    have hc₂ := hL.chains (δ := 2 * i % 5) hkR (runBound i) (p := (st.w₂, (· != 0))) hg.w₂
      hg.w₂ hB hbnd
    refine ⟨⟨hB, hc₁.1.mono (by dsimp only; omega), hc₂.1.mono (by dsimp only; omega)⟩, rfl,
      fun d r m hd hr hrun => ?_⟩
    have hm := hrun.le_runBound hi hiM hd hr
    have hd0 : d % 3 = 0 := by rw [gap_mod_three hR hd]; omega
    have hmd : m * d % 3 = 0 := by rw [Nat.mul_mod, hd0, mul_zero, Nat.zero_mod]
    have h5 : ∀ l ≤ m, (r + l * d) % 5 ≠ 0 := fun l hl => by
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · simpa using mod_five_ne_zero hr
      · exact mod_five_ne_zero (hrun l hl0 hl)
    have hco : ∀ l, 1 ≤ l → l ≤ m → Nat.Coprime ((r + l * d) % L.R) L.R :=
      fun l hl hlm => coprime_mod_R hR (hrun l hl hlm)
    have key : ∀ w : Quad, w.Bounded L st.bound → field L.b (w.get (r % 5)) (r % L.R) + m ≤
        field L.b ((L.chains (2 * i % 5) (2 * i % L.R) (runBound i) (w, (· != 0)) w).get
          ((r + m * d) % 5)) ((r + m * d) % L.R) := by
      intro w hw
      rw [← gap_mod_five hR hd, ← gap_mod_R hR hd]
      obtain ⟨-, hge, hiter⟩ := hL.chains (δ := d % 5) (Nat.mod_lt d hRpos).le (runBound i)
        (p := (w, (· != 0))) hw hw hB hbnd
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · simpa using hge (r % 5) (Nat.mod_mod _ _) (mod_five_ne_zero hr) (r % L.R)
      · obtain ⟨hal, hval⟩ := hL.chainStep_run hRpos hw (by omega) h5 hco m le_rfl
        have := hiter m hmpos hm _ (Nat.mod_mod _ _) (h5 m le_rfl) hal ((r + m * d) % L.R)
        rwa [hval] at this
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
    have ht := hL.transfer (δ := 2 * i % 5) hkR hg.w₂ hg.w₁ hB
    refine ⟨⟨hB, ht.1, hg.w₂.mono (by dsimp only; omega)⟩, rfl, fun d r m hd hr hrun => ?_⟩
    have hm := hrun.le_runBound hi hiM hd hr
    rw [hL1] at hm
    have hr3 := mod_three_ne_zero hr
    simp only [State.value]
    rcases Nat.lt_or_ge m 1 with hm0 | hm1
    · obtain rfl : m = 0 := by omega
      simp only [zero_mul, add_zero]
      rcases (by omega : r % 3 = 1 ∨ r % 3 = 2) with hc | hc
      · rw [hc, State.comp_one, State.comp_one]
        have := ht.2.1 (r % 5) (Nat.mod_mod _ _) (mod_five_ne_zero hr) (r % L.R)
        dsimp only
        omega
      · rw [hc, State.comp_two, State.comp_two]
    · obtain rfl : m = 1 := by omega
      have hrd : Nat.Coprime (r + d) M := by simpa using hrun 1 le_rfl le_rfl
      have hd2 : d % 3 = 2 := by rw [gap_mod_three hR hd]; omega
      have hrd3 := mod_three_ne_zero hrd
      have hc : r % 3 = 2 := by omega
      rw [one_mul, show (r + d) % 3 = 1 by omega, hc, State.comp_two, State.comp_one]
      have := hL.transfer_run hRpos (dst := st.w₁) hg.w₂ hg.w₁ hB (mod_five_ne_zero hr)
        (mod_five_ne_zero hrd) (coprime_mod_R hR hrd)
      rw [gap_mod_five hR hd, gap_mod_R hR hd] at this
      dsimp only
      omega
  · -- `i ≡ 2 [MOD 3]`: a run moves the class `1` to the class `2`
    have hL1 := runBound_of_mod_ne_zero (by omega : i % 3 ≠ 0)
    rw [Layout.stepComps_of_mod_two h2]
    rw [hL1] at hB ⊢
    have ht := hL.transfer (δ := 2 * i % 5) hkR hg.w₁ hg.w₂ hB
    refine ⟨⟨hB, hg.w₁.mono (by dsimp only; omega), ht.1⟩, rfl, fun d r m hd hr hrun => ?_⟩
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
        have := ht.2.1 (r % 5) (Nat.mod_mod _ _) (mod_five_ne_zero hr) (r % L.R)
        dsimp only
        omega
    · obtain rfl : m = 1 := by omega
      have hrd : Nat.Coprime (r + d) M := by simpa using hrun 1 le_rfl le_rfl
      have hd1 : d % 3 = 1 := by rw [gap_mod_three hR hd]; omega
      have hrd3 := mod_three_ne_zero hrd
      have hc : r % 3 = 1 := by omega
      rw [one_mul, show (r + d) % 3 = 2 by omega, hc, State.comp_two, State.comp_one]
      have := hL.transfer_run hRpos (dst := st.w₂) hg.w₁ hg.w₂ hB (mod_five_ne_zero hr)
        (mod_five_ne_zero hrd) (coprime_mod_R hR hrd)
      rw [gap_mod_five hR hd, gap_mod_R hR hd] at this
      dsimp only
      omega

end Layout.WF

end DP

end Erdos455
