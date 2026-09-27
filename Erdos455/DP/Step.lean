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

A function on the units modulo `M = 15 * R` (with `R` coprime to `15`) is stored as eight
packed numbers, one for each unit residue class modulo `15`: `State.w₁` and `State.w₂` hold the
classes `≡ 1` and `≡ 2 [MOD 3]`, each as a `Quad` of four packed numbers for the classes
`≡ 1, 2, 3, 4 [MOD 5]`. Each packed number has `R` fields of `b` bits: field `t` of the entry
`c` of `wₖ` holds the value at the residue `r` with `r ≡ k [MOD 3]`, `r ≡ c [MOD 5]` and
`r ≡ t [MOD R]`. One bignum operation therefore acts on `R` residues at once.

The step for the gap `d = 2 i` is the max-plus operator
`(T w)(s) = max {w(r) + m : r + j d is a unit for 1 ≤ j ≤ m, r + m d = s}`. It is computed as
the maximum of the *chains* `X₀ = w` and `X_{m+1}(s) = X_m(s - d) + 1` (on units),
`m < runBound i`, where `runBound i` bounds the length of a run of units in an arithmetic
progression with difference `d` (Lemma 8 of the paper). When `3 ∤ i`, a run has length at most
one and moves the class `-d` modulo `3` to the class `d`; when `3 ∣ i`, runs stay in their class
modulo `3`. Modulo `5`, a run moves the class `c` to `c + d`; a chain that reaches the class `0`
dies, which is decided without looking at the values.

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
`ZMod (15 * R)`. The constants are stored as literals so that the kernel never has to recompute
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

/-- Four packed numbers, for the residue classes `≡ 1, 2, 3, 4 [MOD 5]`. -/
structure Quad where
  /-- The class `≡ 1 [MOD 5]`. -/
  q₁ : ℕ
  /-- The class `≡ 2 [MOD 5]`. -/
  q₂ : ℕ
  /-- The class `≡ 3 [MOD 5]`. -/
  q₃ : ℕ
  /-- The class `≡ 4 [MOD 5]`. -/
  q₄ : ℕ
  deriving DecidableEq, Repr

namespace Quad

/-- The entry for the class `c` modulo `5` (and `0` if `c ∉ {1, 2, 3, 4}`). -/
def get (q : Quad) (c : ℕ) : ℕ :=
  bif c == 1 then q.q₁ else bif c == 2 then q.q₂ else bif c == 3 then q.q₃ else
    bif c == 4 then q.q₄ else 0

/-- The quad with entries `f 1, f 2, f 3, f 4`. -/
def ofFun (f : ℕ → ℕ) : Quad :=
  ⟨f 1, f 2, f 3, f 4⟩

/-- Subtract `su` from every entry of a quad. -/
def sub (q : Quad) (su : ℕ) : Quad :=
  ⟨q.q₁ - su, q.q₂ - su, q.q₃ - su, q.q₄ - su⟩

/-- Whether `p` holds for all four entries. -/
def all (q : Quad) (p : ℕ → Bool) : Bool :=
  p q.q₁ && p q.q₂ && p q.q₃ && p q.q₄

end Quad

/-- A packed function on the units modulo `15 * R` together with an offset: the value at a unit
`r` is field `r % R` of the entry `r % 5` of `w₁` or `w₂` (according to `r % 3`), plus `offset`.
All fields are at most `bound`. -/
structure State where
  /-- The values at the residues `≡ 1 [MOD 3]`. -/
  w₁ : Quad
  /-- The values at the residues `≡ 2 [MOD 3]`. -/
  w₂ : Quad
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

/-- The class modulo `5` that the move by `δ` sends to `c`: `(c - δ) % 5`. -/
def src5 (δ c : ℕ) : ℕ :=
  (c + 5 - δ) % 5

/-- A move by `d` from one class modulo `3` to another (for `3 ∤ i`): every entry `c` of `dst`
is replaced by its maximum with the shifted entry `c - d` of `src`, unless `c - d ≡ 0 [MOD 5]`
(then there is no run into `c`). Here `δ = d % 5` and `k = d % R`. -/
def transfer (δ k : ℕ) (src dst : Quad) : Quad :=
  Quad.ofFun fun c =>
    bif src5 δ c != 0 then L.pmax (dst.get c) (L.shift k (src.get (src5 δ c))) else dst.get c

/-- One chain step within a class modulo `3` (for `3 ∣ i`): the chain `X` moves by `d` (the
entry `c` comes from the entry `c - d` modulo `5`), and the flags `alive` record whether the
chain into a class modulo `5` is still defined; a chain dies when it would come from the class
`0`. -/
def chainStep (δ k : ℕ) (p : Quad × (ℕ → Bool)) : Quad × (ℕ → Bool) :=
  let alive := fun c => src5 δ c != 0 && p.2 (src5 δ c)
  (Quad.ofFun fun c => bif alive c then L.shift k (p.1.get (src5 δ c)) else 0, alive)

/-- Fold the live entries of a chain into the accumulator by a fieldwise maximum. -/
def accum (acc : Quad) (p : Quad × (ℕ → Bool)) : Quad :=
  Quad.ofFun fun c => bif p.2 c then L.pmax (acc.get c) (p.1.get c) else acc.get c

/-- `n` further chain steps within one class modulo `3`, accumulated into `acc`. -/
def chains (δ k : ℕ) (n : ℕ) : Quad × (ℕ → Bool) → Quad → Quad :=
  Nat.rec (motive := fun _ => Quad × (ℕ → Bool) → Quad → Quad) (fun _ acc => acc)
    (fun _ ih p acc => let p' := L.chainStep δ k p; ih p' (L.accum acc p')) n

/-- The max-plus step for the gap `2 i` on the two classes modulo `3`. -/
def stepComps (i : ℕ) (w₁ w₂ : Quad) : Quad × Quad :=
  let k := 2 * i % L.R
  let δ := 2 * i % 5
  bif i % 3 == 1 then (L.transfer δ k w₂ w₁, w₂)
  else bif i % 3 == 2 then (w₁, L.transfer δ k w₁ w₂)
  else (L.chains δ k (runBound i) (w₁, (· != 0)) w₁, L.chains δ k (runBound i) (w₂, (· != 0)) w₂)

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
  let su := L.uones * s
  let bo := L.ones * B
  let w₁ := st.w₁.sub su
  let w₂ := st.w₂.sub su
  bif s < 2 ^ (L.b - 1) && B < 2 ^ (L.b - 1) && st.w₁.all (ple L.uhighs su) &&
      st.w₂.all (ple L.uhighs su) && w₁.all (fun x => ple L.highs x bo) &&
      w₂.all (fun x => ple L.highs x bo) then
    some ⟨w₁, w₂, st.offset + s, B⟩
  else none

/-- Step `lo + 1` of a run, followed by the normalisation with the next entry `(s, B)` of the
schedule if `K ∣ lo + 1`, and then by the continuation `k` on the rest of the schedule. -/
def runStep (K lo : ℕ) (k : List (ℕ × ℕ) → State → Option (List (ℕ × ℕ) × State))
    (sched : List (ℕ × ℕ)) (st : State) : Option (List (ℕ × ℕ) × State) :=
  match L.step (lo + 1) st with
  | none => none
  | some st' =>
    bif (lo + 1) % K == 0 then
      match sched with
      | [] => none
      | (s, B) :: sched' =>
        match L.normalize s B st' with
        | none => none
        | some st'' => k sched' st''
    else k sched st'

/-- Steps `lo + 1, …, lo + n`. After every step `i` with `K ∣ i`, the state is normalised with
the next entry `(s, B)` of the schedule. Returns the unused schedule and the final state. -/
def run (K : ℕ) (n : ℕ) : ℕ → List (ℕ × ℕ) → State → Option (List (ℕ × ℕ) × State) :=
  Nat.rec (motive := fun _ => ℕ → List (ℕ × ℕ) → State → Option (List (ℕ × ℕ) × State))
    (fun _ sched st => some (sched, st)) (fun _ ih lo => L.runStep K lo (ih (lo + 1))) n

/-- A run of no steps returns the state and the schedule unchanged. -/
theorem run_zero (K lo : ℕ) (sched : List (ℕ × ℕ)) (st : State) :
    L.run K 0 lo sched st = some (sched, st) := rfl

/-- A run of `n + 1` steps is a step followed by a run of `n` steps. -/
theorem run_succ (K n lo : ℕ) :
    L.run K (n + 1) lo = L.runStep K lo (L.run K n (lo + 1)) := rfl

end Layout

end Erdos455.DP
