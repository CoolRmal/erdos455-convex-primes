/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib

/-!
# The packed value iteration

This file defines the computation that certifies the growth rate of the max-plus dynamic
program (Proposition 11 of the paper). It is designed to be evaluated by the Lean kernel,
whose `ℕ` arithmetic and bitwise operations run on GMP.

A function on the units modulo `M = 3 * R` (with `3 ∤ R`) is stored as two packed numbers
`w₁` and `w₂`, one for each unit residue class modulo `3`. Each has `R` fields of `b` bits:
field `t` of `wₖ` holds the value at the residue `r` with `r ≡ k [MOD 3]` and `r ≡ t [MOD R]`.
One bignum operation therefore acts on `R` residues at once.

The step for the gap `d = 2 i` is the max-plus operator
`(T w)(s) = max {w(r) + m : r + j d is a unit for 1 ≤ j ≤ m, r + m d = s}`. It is computed as
the maximum of the *chains* `X₀ = w` and `X_{m+1}(s) = X_m(s - d) + 1` (on units),
`m < runBound i`, where `runBound i` bounds the length of a run of units in an arithmetic
progression with difference `d` (Lemma 8 of the paper). When `3 ∤ i`, a run has length at most
one and moves the class `-d` modulo `3` to the class `d`; when `3 ∣ i`, runs stay in their class.

The values are kept small by periodically subtracting a constant from all of them
(`Layout.normalize`), which is recorded in the offset of the state. All operations check the
invariants they need (no field reaches the guard bit `b - 1`, no field borrows), so that the
soundness proof in `Erdos455.DP.Sound` needs no information about the particular values.

## Main definitions

* `Erdos455.DP.Layout`: the parameters and packed constants.
* `Erdos455.DP.State`: a packed function together with an offset and a bound on its fields.
* `Erdos455.DP.Layout.step`: one step of the value iteration.
* `Erdos455.DP.Layout.normalize`: subtracts a constant from all values.
* `Erdos455.DP.Layout.run`: a run of consecutive steps with periodic normalisation.
-/

namespace Erdos455.DP

/-- The parameters and packed constants of a packed layout for functions on the units of
`ZMod (3 * R)`. The constants are stored as literals so that the kernel never has to recompute
them; their specification is `Layout.WF`. -/
structure Layout where
  /-- The number of fields of a component. -/
  R : ℕ
  /-- The width of a field in bits; bit `b - 1` of every field is a guard bit. -/
  b : ℕ
  /-- Every field below `R` is `1`. -/
  ones : ℕ
  /-- Every field below `R` is `2 ^ (b - 1)`. -/
  highs : ℕ
  /-- Field `t < R` is `2 ^ b - 1` if `t` is coprime to `R`, and `0` otherwise. -/
  umask : ℕ
  /-- Field `t < R` is `1` if `t` is coprime to `R`, and `0` otherwise. -/
  uones : ℕ
  /-- Field `t < R` is `2 ^ (b - 1)` if `t` is coprime to `R`, and `0` otherwise. -/
  uhighs : ℕ

/-- A packed function on the units modulo `3 * R` together with an offset: the value at a unit
`r` is field `r % R` of `w₁` or `w₂` (according to `r % 3`), plus `offset`. All fields are at
most `bound`. -/
structure State where
  /-- The values at the residues `≡ 1 [MOD 3]`. -/
  w₁ : ℕ
  /-- The values at the residues `≡ 2 [MOD 3]`. -/
  w₂ : ℕ
  /-- The amount subtracted from all values so far. -/
  offset : ℕ
  /-- An upper bound for all fields of `w₁` and `w₂`. -/
  bound : ℕ
  deriving DecidableEq, Repr

/-- The least prime `p ∈ {3, 5, 7, 11, 13}` not dividing `i`, minus `2`, and `15` if there is
none: for `i < 255255` this is `P(2 i) - 2`, where `P(d)` is the least prime not dividing `d`,
and bounds the length of a run of units modulo `255255` in an arithmetic progression with
difference `2 i`. -/
def runBound (i : ℕ) : ℕ :=
  bif i % 3 != 0 then 1 else bif i % 5 != 0 then 3 else bif i % 7 != 0 then 5 else
    bif i % 11 != 0 then 9 else bif i % 13 != 0 then 11 else 15

/-- Fieldwise comparison: whether every field of `x` selected by the guard mask `h` is at most
the corresponding field of `y` (for fields below `2 ^ (b - 1)`). -/
def ple (h x y : ℕ) : Bool :=
  ((y ||| h) - x) &&& h == h

namespace Layout

variable (L : Layout)

/-- Rotation of the fields of a packed number `x < 2 ^ (b * R)` by `k ≤ R` places: field `t`
of the result is field `(t + R - k) % R` of `x`. -/
def rot (k x : ℕ) : ℕ :=
  (x <<< (L.b * k)) ||| (x >>> (L.b * (L.R - k)))

/-- The chain step: rotate by `k`, add one to every field and clear the non-units. -/
def shift (k x : ℕ) : ℕ :=
  (L.rot k x + L.ones) &&& L.umask

/-- Fieldwise maximum of two packed numbers whose fields are below `2 ^ (b - 1)`. -/
def pmax (a x : ℕ) : ℕ :=
  let t := (a ||| L.highs) - x
  let c := t &&& L.highs
  x + (t &&& (c - (c >>> (L.b - 1))))

/-- `n` further chain steps within one component: `chainMax k n x acc` is the fieldwise
maximum of `acc` and `shift^[j] x` for `1 ≤ j ≤ n`. -/
def chainMax (k : ℕ) (n : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih x acc => let y := L.shift k x; ih y (L.pmax acc y)) n

/-- The max-plus step for the gap `2 i` on the two components. -/
def stepComps (i w₁ w₂ : ℕ) : ℕ × ℕ :=
  let k := 2 * i % L.R
  bif i % 3 == 1 then (L.pmax w₁ (L.shift k w₂), w₂)
  else bif i % 3 == 2 then (w₁, L.pmax w₂ (L.shift k w₁))
  else (L.chainMax k (runBound i) w₁ w₁, L.chainMax k (runBound i) w₂ w₂)

/-- Step `i` of the value iteration, failing if a field could reach the guard bit. -/
def step (i : ℕ) (st : State) : Option State :=
  let B := st.bound + runBound i
  bif B < 2 ^ (L.b - 1) then
    let w := L.stepComps i st.w₁ st.w₂
    some ⟨w.1, w.2, st.offset, B⟩
  else none

/-- Subtract `s` from every value (the fields at units), after checking that no field borrows,
and check that the new fields are at most `B`. -/
def normalize (s B : ℕ) (st : State) : Option State :=
  let su := s * L.uones
  let bo := B * L.ones
  let w₁ := st.w₁ - su
  let w₂ := st.w₂ - su
  bif s < 2 ^ (L.b - 1) && B < 2 ^ (L.b - 1) && ple L.uhighs su st.w₁ &&
      ple L.uhighs su st.w₂ && ple L.highs w₁ bo && ple L.highs w₂ bo then
    some ⟨w₁, w₂, st.offset + s, B⟩
  else none

/-- Steps `lo + 1, …, lo + n`. After every step `i` with `K ∣ i`, the state is normalised with
the next entry `(s, B)` of the schedule. Returns the unused schedule and the final state. -/
def run (K : ℕ) (n : ℕ) : ℕ → List (ℕ × ℕ) → State → Option (List (ℕ × ℕ) × State) :=
  Nat.rec (motive := fun _ => ℕ → List (ℕ × ℕ) → State → Option (List (ℕ × ℕ) × State))
    (fun _ sched st => some (sched, st))
    (fun _ ih lo sched st =>
      match L.step (lo + 1) st with
      | none => none
      | some st' =>
        bif (lo + 1) % K == 0 then
          match sched with
          | [] => none
          | (s, B) :: sched' =>
            match L.normalize s B st' with
            | none => none
            | some st'' => ih (lo + 1) sched' st''
        else ih (lo + 1) sched st')
    n

end Layout

end Erdos455.DP
