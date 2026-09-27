/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib

/-!
# The dynamic program: statement of the certificate

Let `M = 3 · 5 · 7 · 11 · 13 · 17 = 255255`. For a gap `d` and a residue `r`, a *run* of
length `m` is a sequence `r, r + d, …, r + m d` whose terms `r + j d` (`1 ≤ j ≤ m`) are coprime
to `M`. Eventually every term of a convex sequence of primes is coprime to `M`, and all gaps
equal to `d` form such a run.

The certificate (Proposition 11 of the paper) bounds the total length of the runs along one
period of gap values `d ≡ 2, 4, …, 2 (M - 1) [MOD M]`: there is a bounded potential `φ` with
`φ (t 0) + ∑ μ i ≤ φ (t (M - 1)) + 295318` along every such path of runs. It is proved in
`Erdos455.DP.Certificate` by a computation checked by the kernel.

## Main definitions

* `Erdos455.M`: the modulus `255255`.
* `Erdos455.growth`: the growth rate `Λ = 295318` of the dynamic program per period.
* `Erdos455.IsRun`: the terms of an arithmetic progression are coprime to `M`.
* `Erdos455.PeriodPath`: a path of runs along one period of gap values.
-/

namespace Erdos455

/-- The modulus `M = 3 · 5 · 7 · 11 · 13 · 17`. -/
def M : ℕ := 255255

/-- The growth rate `Λ` of the dynamic program over one period of gap values. -/
def growth : ℕ := 295318

/-- `M` is the product of the odd primes up to `17`. -/
theorem M_eq : M = 3 * 5 * 7 * 11 * 13 * 17 := rfl

/-- `IsRun d r m`: the numbers `r + j d` with `1 ≤ j ≤ m` are all coprime to `M`. -/
def IsRun (d r m : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ m → Nat.Coprime (r + j * d) M

/-- A path of runs along one period: starting at the unit `t 0`, for `1 ≤ i < M` a run of
length `μ i` with gap `d i ≡ 2 i [MOD M]` leads from `t (i - 1)` to `t i`. -/
structure PeriodPath (d t μ : ℕ → ℕ) : Prop where
  coprime_zero : Nat.Coprime (t 0) M
  gap_mod : ∀ i, 1 ≤ i → i < M → d i % M = 2 * i % M
  isRun : ∀ i, 1 ≤ i → i < M → IsRun (d i) (t (i - 1)) (μ i)
  step : ∀ i, 1 ≤ i → i < M → t i = t (i - 1) + μ i * d i

end Erdos455
