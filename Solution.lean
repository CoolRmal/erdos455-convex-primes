/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455

/-!
# Solution

Proofs of the statements of `Challenge.lean`. The definitions (`Erdos455.largePrime`,
`Erdos455.G`) are those of `Erdos455/Defs.lean`, which coincide verbatim with the ones in
`Challenge.lean`.
-/

open Filter
open scoped ENNReal

namespace Erdos455

theorem ofReal_le_liminf : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    ENNReal.ofReal (255255 / (295318 + G)) ≤
      liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop := by
  sorry

theorem liminf_gt : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop > 0.864289 := by
  sorry

theorem eventually_lt : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    ∀ᶠ n : ℕ in atTop, (0.864289 : ℝ) * n ^ 2 < q n := by
  sorry

theorem G_lt : G < 17.2245 := by
  sorry

theorem erdos_455.variants.liminf : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop > 0.352 := by
  sorry

end Erdos455
