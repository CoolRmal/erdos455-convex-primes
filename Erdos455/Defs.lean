/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib

/-!
# Definitions of the statement

The definitions used in the statements of `Challenge.lean`, verbatim: `lake comparator` checks
that the theorems of `Solution.lean` are stated with the same definitions.
-/

namespace Erdos455

/-- The primes that are at least `19`, in increasing order: `largePrime 0 = 19`,
`largePrime 1 = 23`, `largePrime 2 = 29`, … -/
noncomputable def largePrime (i : ℕ) : ℕ :=
  Nat.nth (fun p => p.Prime ∧ 19 ≤ p) i

/-- The constant `G = (19 - 2) + ∑_{i ≥ 1} (p'ᵢ₊₁ - p'ᵢ) / (p'₁ ⋯ p'ᵢ) = 17.2244296…`, where
`19 = p'₁ < p'₂ < ⋯` are the primes that are at least `19` (so `p'ᵢ = largePrime (i - 1)`).
It bounds the average of `P(2Mj) - 2` over `j`, where `P(d)` is the least prime not dividing
`d`: these are the gaps divisible by `2M`, on which the dynamic program gives no information. -/
noncomputable def G : ℝ :=
  17 + ∑' i : ℕ, ((largePrime (i + 1) : ℝ) - largePrime i) /
    ∏ j ∈ Finset.range (i + 1), (largePrime j : ℝ)

end Erdos455
