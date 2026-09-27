/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.DP.Run
import Erdos455.Packed.Check

/-!
# Generating the certificate

Commands that compute, at elaboration time, the data of the certificate for the dynamic program
and add it to the environment together with the theorems that the kernel checks.

The code in this file is *untrusted*: it only proposes definitions (the packed constants, the
potential `φ`, the normalisation schedule and the intermediate states of the value iteration)
and proof terms of the form `of_decide_eq_true (Eq.refl true)`, which the kernel checks by
evaluating the verified computation `Layout.run` of `Erdos455.DP.Step`. A wrong proposal can
only make the kernel reject a theorem.

* `dp_layout% L R b` defines the layout `L` with `R` fields of `b` bits.
* `dp_certificate% L K C φ hL hR` (with `hL : L.WF` and `hR : 3 * L.R = M`) runs one period of the value iteration from zero to compute the
  potential and defines it as the state `φ`; then runs one period from `φ` in chunks of `C`
  steps (normalising every `K` steps), defining the intermediate states and the theorems
  `φ.chunk_k : L.run K C (k C) sched_k st_k = some ([], st_(k+1))` and
  `φ.sim_k : st_k.Good L ∧ Sim L (φ.value L) (k C) st_k`, ending with the final state `φ.final`
  and `φ.final_sim : φ.final.Good L ∧ Sim L (φ.value L) (M - 1) φ.final`.
-/

namespace Erdos455.DP.Gen

open Lean Meta Elab Command

/-! ### Lemmas with explicit arguments, for the proof terms built by the commands -/

theorem good (L : Layout) (hL : L.WF) (st : State) (h : L.goodB st = true) : st.Good L :=
  hL.good_of_goodB h

theorem sim_zero (L : Layout) (st : State) (hg : st.Good L) :
    st.Good L ∧ Sim L (st.value L) 0 st :=
  ⟨hg, fun _ _ _ _ => by simp⟩

theorem chunk (L : Layout) (hL : L.WF) (hR : 3 * L.R = M) (φ : ℕ → ℕ) (K n lo : ℕ)
    (sched : List (ℕ × ℕ)) (st st' : State) (h : L.run K n lo sched st = some ([], st'))
    (hlt : lo + n < M) (hs : st.Good L ∧ Sim L φ lo st) : st'.Good L ∧ Sim L φ (lo + n) st' :=
  hL.run hR φ K n lo sched st ([], st') h hlt hs.1 hs.2

/-! ### Untrusted computations -/

/-- The packed number with fields `f (k + t)`, `t < n`, built by divide and conquer. -/
partial def packedOf (b : ℕ) (f : ℕ → ℕ) (k n : ℕ) : ℕ :=
  if n ≤ 32 then (List.range n).foldr (fun t acc => (acc <<< b) ||| f (k + t)) 0
  else
    let h := n / 2
    packedOf b f k h ||| (packedOf b f (k + h) (n - h) <<< (b * h))

/-- The layout with `R` fields of `b` bits. -/
def mkLayout (R b : ℕ) : Layout where
  R := R
  b := b
  ones := packedOf b (fun _ => 1) 0 R
  highs := packedOf b (fun _ => 2 ^ (b - 1)) 0 R
  umask := packedOf b (fun t => if Nat.gcd t R == 1 then 2 ^ b - 1 else 0) 0 R
  uones := packedOf b (fun t => if Nat.gcd t R == 1 then 1 else 0) 0 R
  uhighs := packedOf b (fun t => if Nat.gcd t R == 1 then 2 ^ (b - 1) else 0) 0 R

/-- The maximum of the fields `t < n` of `x`, by repeated halving with `pmax`. -/
partial def fieldMax (L : Layout) (x n : ℕ) : ℕ :=
  if n ≤ 1 then x % 2 ^ L.b
  else
    let h := n / 2
    fieldMax L (L.pmax (x % 2 ^ (L.b * h)) (x >>> (L.b * h))) (n - h)

/-- The minimum of the fields of `w` at the units (assuming fields below `2 ^ (b - 1)`). -/
def unitMin (L : Layout) (w : ℕ) : ℕ :=
  let top := 2 ^ (L.b - 1) - 1
  top - fieldMax L (L.uones * top - (w &&& L.umask)) L.R

/-- The least stored value at a unit after normalisation: the chain values created from
non-units are at most `15`, so values at least `16` are never overtaken by them. -/
def margin : ℕ := 16

/-- The normalisation after a step: subtract as much as possible while keeping every value at a
unit at least `margin`; returns the schedule entry and the normalised state. -/
def normalizeAuto (L : Layout) (st : State) : Except String ((ℕ × ℕ) × State) := do
  let lo := min (unitMin L st.w₁) (unitMin L st.w₂)
  let s := lo - margin
  let su := L.uones * s
  let B := max (fieldMax L (st.w₁ - su) L.R) (fieldMax L (st.w₂ - su) L.R)
  match L.normalize s B st with
  | some st' => return ((s, B), st')
  | none => throw s!"normalisation failed (s = {s}, B = {B})"

/-- Steps `lo + 1, …, lo + n` as in `Layout.run`, choosing the schedule on the fly. Returns the
schedule used and the final state. -/
def runAuto (L : Layout) (K n lo : ℕ) (st : State) :
    Except String (Array (ℕ × ℕ) × State) := do
  let mut st := st
  let mut sched := #[]
  for j in [0:n] do
    let i := lo + j + 1
    match L.step i st with
    | none => throw s!"step {i} failed"
    | some st' =>
      st := st'
      if i % K == 0 then
        let (e, st'') ← normalizeAuto L st
        sched := sched.push e
        st := st''
  return (sched, st)

/-! ### Expressions -/

/-- The expression of a natural number literal. -/
def natE (n : ℕ) : Expr := mkRawNatLit n

/-- The expression of a state. -/
def stateE (st : State) : Expr :=
  mkApp4 (mkConst ``State.mk) (natE st.w₁) (natE st.w₂) (natE st.offset) (natE st.bound)

/-- The expression of a schedule. -/
def schedE (sched : Array (ℕ × ℕ)) : Expr :=
  let nat := mkConst ``Nat
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) nat nat
  sched.foldr (init := mkApp (mkConst ``List.nil [0]) pairTy) fun (s, B) acc =>
    mkApp3 (mkConst ``List.cons [0]) pairTy
      (mkApp4 (mkConst ``Prod.mk [0, 0]) nat nat (natE s) (natE B)) acc

/-- The expression of a layout. -/
def layoutE (L : Layout) : Expr :=
  mkAppN (mkConst ``Layout.mk)
    #[natE L.R, natE L.b, natE L.ones, natE L.highs, natE L.umask, natE L.uones, natE L.uhighs]

/-- Add a definition (not compiled: it is only used in proofs). -/
def addDef (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl <| .defnDecl
    { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }

/-- Add a theorem. -/
def addThm (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl <| .thmDecl { name, levelParams := [], type, value }

/-- A proof of the decidable proposition `p` by evaluation in the kernel. -/
def decideProof (p : Expr) : MetaM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  return mkApp3 (mkConst ``of_decide_eq_true) p inst
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))

/-! ### Commands -/

/-- `dp_layout% L R b` defines the layout `L` with `R` fields of `b` bits. -/
elab "dp_layout% " id:ident R:num b:num : command => do
  let L := mkLayout R.getNat b.getNat
  let name := (← getCurrNamespace) ++ id.getId
  liftCoreM <| addDef name (mkConst ``Layout) (layoutE L)

/-- `dp_certificate% L K C φ`: see the module documentation. -/
elab "dp_certificate% " lId:ident K:num C:num phiId:ident wf:ident hR:ident : command => do
  let ns ← getCurrNamespace
  let lName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo lId
  let some (.defnInfo lInfo) := (← getEnv).find? lName | throwError "{lName} is not a definition"
  -- recover the layout from its definition
  let args := lInfo.value.getAppArgs
  let getLit (e : Expr) : CommandElabM ℕ := do
    let some n := e.rawNatLit? | throwError "expected a literal"
    return n
  let L : Layout := ⟨← getLit args[0]!, ← getLit args[1]!, ← getLit args[2]!, ← getLit args[3]!,
    ← getLit args[4]!, ← getLit args[5]!, ← getLit args[6]!⟩
  let K := K.getNat
  let C := C.getNat
  let period := M - 1
  let t0 ← IO.monoMsNow
  -- 1. the potential: one period from the constant function `margin`
  let init : State := ⟨L.uones * margin, L.uones * margin, 0, margin⟩
  let (_, stφ) ← match runAuto L K period 0 init with
    | .ok r => pure r
    | .error e => throwError "computing the potential: {e}"
  let ((_, B), stφ) ← match normalizeAuto L stφ with
    | .ok r => pure r
    | .error e => throwError "computing the potential: {e}"
  let phi : State := ⟨stφ.w₁, stφ.w₂, 0, B⟩
  let phiName := ns ++ phiId.getId
  liftCoreM <| addDef phiName (mkConst ``State) (stateE phi)
  let t1 ← IO.monoMsNow
  logInfo m!"potential computed in {t1 - t0} ms"
  -- 2. the verification run from the potential, in chunks
  let lE := mkConst lName
  let φE := mkApp2 (mkConst ``State.value) lE (mkConst phiName)
  let simE (lo : ℕ) (stE : Expr) : Expr :=
    mkApp2 (mkConst ``And) (mkApp2 (mkConst ``State.Good) lE stE)
      (mkApp4 (mkConst ``Sim) lE φE (natE lo) stE)
  -- `sim_0` from the initial state
  let goodTy := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Layout.goodB) lE (mkConst phiName)) (mkConst ``Bool.true)
  let goodPf ← liftTermElabM <| decideProof goodTy
  let sim0 := phiName ++ `sim_0
  liftCoreM <| addThm sim0 (simE 0 (mkConst phiName))
    (mkApp3 (mkConst ``sim_zero) lE (mkConst phiName)
      (mkApp4 (mkConst ``good) lE (mkConst wf.getId) (mkConst phiName) goodPf))
  let mut st := phi
  let mut stName := phiName
  let mut simName := sim0
  let mut lo : ℕ := 0
  let mut k : ℕ := 0
  while lo < period do
    let n := min C (period - lo)
    let (sched, st') ← match runAuto L K n lo st with
      | .ok r => pure r
      | .error e => throwError "chunk {k}: {e}"
    let schedName := phiName ++ Name.mkSimple s!"sched_{k}"
    let nextName := phiName ++ Name.mkSimple s!"st_{k + 1}"
    let chunkName := phiName ++ Name.mkSimple s!"chunk_{k}"
    let simName' := phiName ++ Name.mkSimple s!"sim_{k + 1}"
    let schedTy := mkApp (mkConst ``List [0])
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat))
    liftCoreM <| addDef schedName schedTy (schedE sched)
    liftCoreM <| addDef nextName (mkConst ``State) (stateE st')
    -- the kernel checks the chunk by evaluation
    let resTy := mkApp2 (mkConst ``Prod [0, 0]) schedTy (mkConst ``State)
    let lhs := mkAppN (mkConst ``Layout.run) #[lE, natE K, natE n, natE lo, mkConst schedName,
      mkConst stName]
    let rhs := mkApp2 (mkConst ``Option.some [0]) resTy
      (mkApp4 (mkConst ``Prod.mk [0, 0]) schedTy (mkConst ``State)
        (mkApp (mkConst ``List.nil [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat)
          (mkConst ``Nat))) (mkConst nextName))
    let chunkTy := mkApp3 (mkConst ``Eq [1]) (mkApp (mkConst ``Option [0]) resTy) lhs rhs
    let chunkPf ← liftTermElabM <| decideProof chunkTy
    liftCoreM <| addThm chunkName chunkTy chunkPf
    -- the conclusion of the value iteration after the chunk
    let ltTy := mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat)
      (natE (lo + n)) (mkConst ``M)
    let ltPf ← liftTermElabM <| decideProof ltTy
    liftCoreM <| addThm simName' (simE (lo + n) (mkConst nextName))
      (mkAppN (mkConst ``chunk) #[lE, mkConst wf.getId, mkConst hR.getId, φE,
        natE K, natE n, natE lo, mkConst schedName, mkConst stName, mkConst nextName,
        mkConst chunkName, ltPf, mkConst simName])
    st := st'
    stName := nextName
    simName := simName'
    lo := lo + n
    k := k + 1
  -- the final state
  liftCoreM <| addDef (phiName ++ `final) (mkConst ``State) (mkConst stName)
  liftCoreM <| addThm (phiName ++ `final_sim) (simE period (mkConst (phiName ++ `final)))
    (mkConst simName)
  let t2 ← IO.monoMsNow
  logInfo m!"{k} chunks checked in {t2 - t1} ms"

end Erdos455.DP.Gen
