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

/-- **Main theorem** (sharp form). If `q` is a strictly increasing sequence of primes with
non-decreasing gaps, then `liminf q n / n² ≥ 255255 / (295318 + G)`. -/
theorem ofReal_le_liminf : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    ENNReal.ofReal (255255 / (295318 + G)) ≤
      liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop :=
  Main.ofReal_le_liminf

/-- **Main theorem**. If `q` is a strictly increasing sequence of primes with non-decreasing
gaps, then `liminf q n / n² > 0.864289`. -/
theorem liminf_gt : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop > 0.864289 :=
  Main.liminf_gt

/-- **Main theorem**, eventual form. If `q` is a strictly increasing sequence of primes with
non-decreasing gaps, then `q n > 0.864289 n²` for all sufficiently large `n`. -/
theorem eventually_lt : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    ∀ᶠ n : ℕ in atTop, (0.864289 : ℝ) * n ^ 2 < q n :=
  Main.eventually_lt

/-- Numerical value of the constant: `G < 17.2245`. -/
theorem G_lt : G < 17.2245 :=
  G_lt_bound

/-- **Richter's theorem** [Ri76], stated exactly as `erdos_455.variants.liminf` in Formal
Conjectures: `liminf q n / n² > 0.352`. It follows from the main theorem. -/
theorem erdos_455.variants.liminf : ∀ q : ℕ → ℕ, StrictMono q →
    (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    liminf (fun n : ℕ => (q n : ℝ≥0∞) / n ^ 2) atTop > 0.352 :=
  Main.liminf_gt_richter

end Erdos455
