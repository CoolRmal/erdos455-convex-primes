/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib

/-!
# The least prime not dividing a number

For `d ≠ 0`, `leastNonDivisor d` is the least prime `P(d)` not dividing `d` (Section 2 of the
paper). Every prime below `P(d)` divides `d`.

## Main definitions

* `Erdos455.leastNonDivisor d`: the least prime not dividing `d` (junk value `2` for `d = 0`).

## Main statements

* `Erdos455.leastNonDivisor_prime`, `Erdos455.not_dvd_leastNonDivisor`,
  `Erdos455.dvd_of_lt_leastNonDivisor`: the defining properties.
* `Erdos455.leastNonDivisor_le_sub_one`: `P(d) ≤ d - 1` for `d ≥ 3` (Lemma 2(a)).
-/

namespace Erdos455

theorem exists_prime_not_dvd {d : ℕ} (hd : d ≠ 0) : ∃ p, p.Prime ∧ ¬p ∣ d := by
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (d + 1)
  exact ⟨p, hp, fun h => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) h; omega⟩

open Classical in
/-- The least prime not dividing `d`, for `d ≠ 0` (and `2` for `d = 0`). -/
noncomputable def leastNonDivisor (d : ℕ) : ℕ :=
  if hd : d = 0 then 2 else Nat.find (exists_prime_not_dvd hd)

variable {d : ℕ}

theorem leastNonDivisor_spec (hd : d ≠ 0) :
    (leastNonDivisor d).Prime ∧ ¬leastNonDivisor d ∣ d := by
  classical
  rw [leastNonDivisor, dite_eq_right hd]
  exact Nat.find_spec (exists_prime_not_dvd hd)

theorem leastNonDivisor_prime (d : ℕ) : (leastNonDivisor d).Prime := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [leastNonDivisor, Nat.prime_two]
  · exact (leastNonDivisor_spec hd).1

theorem not_dvd_leastNonDivisor (hd : d ≠ 0) : ¬leastNonDivisor d ∣ d :=
  (leastNonDivisor_spec hd).2

/-- Every prime below `P(d)` divides `d`. -/
theorem dvd_of_lt_leastNonDivisor (hd : d ≠ 0) {p : ℕ} (hp : p.Prime)
    (h : p < leastNonDivisor d) : p ∣ d := by
  classical
  rw [leastNonDivisor, dite_eq_right hd] at h
  by_contra hpd
  exact Nat.find_min (exists_prime_not_dvd hd) h ⟨hp, hpd⟩

/-- `P(d)` is the least prime not dividing `d`. -/
theorem leastNonDivisor_le_of_not_dvd (hd : d ≠ 0) {p : ℕ} (hp : p.Prime) (h : ¬p ∣ d) :
    leastNonDivisor d ≤ p :=
  not_lt.mp fun hlt => h (dvd_of_lt_leastNonDivisor hd hp hlt)

/-- **Lemma 2(a)**: `P(d) ≤ d - 1` for `d ≥ 3`. -/
theorem leastNonDivisor_le_sub_one (hd : 3 ≤ d) : leastNonDivisor d ≤ d - 1 := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show d - 1 ≠ 1 by omega)
  have hle : p ≤ d - 1 := Nat.le_of_dvd (by omega) hpd
  refine (leastNonDivisor_le_of_not_dvd (by omega) hp fun h => ?_).trans hle
  have : p ∣ d - (d - 1) := Nat.dvd_sub h hpd
  rw [show d - (d - 1) = 1 by omega] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

end Erdos455
