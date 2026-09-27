/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.DP.Spec

/-!
# The certificate for the dynamic program

Proposition 11 of the paper, in the path form used by the counting argument: there is a
potential `φ` with values in `[0, 255]` such that along every path of runs over one period of
gap values, `φ (t 0) + ∑ μ i ≤ φ (t (M - 1)) + 295318`.
-/

namespace Erdos455

/-- **Proposition 11** (path form): the dynamic program gains at most `growth = 295318` per
period, up to a bounded potential. -/
theorem exists_potential : ∃ φ : ℕ → ℕ, (∀ r, φ r ≤ 255) ∧
    ∀ d t μ : ℕ → ℕ, PeriodPath d t μ →
      φ (t 0) + ∑ i ∈ Finset.Ico 1 M, μ i ≤ φ (t (M - 1)) + growth := by
  sorry

end Erdos455
