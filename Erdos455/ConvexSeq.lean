/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos455.DP.Spec

/-!
# The structure of a convex sequence of primes

Let `q₀ < q₁ < ⋯` be primes with non-decreasing gaps `gap q n = q (n + 1) - q n`. This file
sets up the combinatorics of the runs of equal gaps (Section 3 of the paper: Lemma 4,
Definition 5 and Lemma 6).

Instead of the paper's `n(d) = min {n ≥ n₀ : gap n ≥ d}`, defined only for `d ≥ d* = gap n₀`,
we use `first q x`, the least `n ≥ n₀` with `x ≤ gap q n`, for every `x`. Then
`first q x = n₀` for `x ≤ d*`, so the runs of gaps below `d*` are simply empty and need no
special treatment. The run of gaps equal to `d` is `[first q d, first q (d + 1))`; its length
is `runLength q d` (the paper's `m(d)`).

## Main definitions

* `Erdos455.IsConvexPrimeSeq q`: `q` is a strictly increasing sequence of primes with
  non-decreasing gaps.
* `Erdos455.gap q n`: the gap `q (n + 1) - q n`.
* `Erdos455.start q`: the least index `n₀` with `17 < q n₀`.
* `Erdos455.first q x`: the least index `n ≥ n₀` with `x ≤ gap q n`.
* `Erdos455.runLength q d`: the number `m(d)` of indices `n ≥ n₀` with `gap q n = d`.

## Main statements

* `Erdos455.IsConvexPrimeSeq.exists_le_gap`: the gaps are unbounded (Lemma 4(a)).
* `Erdos455.IsConvexPrimeSeq.coprime_M`, `Erdos455.IsConvexPrimeSeq.even_gap`: from `n₀` on,
  the terms are coprime to `M` and the gaps are even (Lemma 4(b)).
* `Erdos455.IsConvexPrimeSeq.lt_first_iff`: for `n ≥ n₀`, `n < first q x ↔ gap q n < x`.
* `Erdos455.IsConvexPrimeSeq.q_first_add`: the run of gaps `d` is an arithmetic progression
  (Lemma 6(b)).
* `Erdos455.IsConvexPrimeSeq.first_two_mul_add`: the telescoping identity behind Lemma 6(d).
-/

namespace Erdos455

/-- A *convex sequence of primes*: a strictly increasing sequence of primes whose gaps
`q (n + 1) - q n` are non-decreasing. -/
structure IsConvexPrimeSeq (q : ℕ → ℕ) : Prop where
  strictMono : StrictMono q
  prime : ∀ n, (q n).Prime
  gap_le_gap : ∀ n, q (n + 1) - q n ≤ q (n + 2) - q (n + 1)

/-- The gap `q (n + 1) - q n` of a sequence of natural numbers. -/
def gap (q : ℕ → ℕ) (n : ℕ) : ℕ :=
  q (n + 1) - q n

/-- The least index `n₀` with `17 < q n₀` (for a convex sequence of primes, all terms from `n₀`
on are coprime to `M`). -/
noncomputable def start (q : ℕ → ℕ) : ℕ :=
  sInf {n | 17 < q n}

/-- The least index `n ≥ start q` with `x ≤ gap q n`: the start of the run of gaps `x` (the
paper's `n(x)`, for `x ≥ gap q (start q)`). -/
noncomputable def first (q : ℕ → ℕ) (x : ℕ) : ℕ :=
  sInf {n | start q ≤ n ∧ x ≤ gap q n}

/-- The number of indices `n ≥ start q` with `gap q n = d`: the length of the run of gaps `d`
(the paper's `m(d)`). -/
noncomputable def runLength (q : ℕ → ℕ) (d : ℕ) : ℕ :=
  first q (d + 1) - first q d

/-- A prime dividing `M = 3 · 5 · 7 · 11 · 13 · 17` is at most `17`. -/
theorem le_seventeen_of_dvd_M {p : ℕ} (hp : p.Prime) (h : p ∣ M) : p ≤ 17 := by
  rw [M_eq] at h
  have h' : ∀ r : ℕ, r.Prime → p ∣ r → p ≤ r := fun r hr hpr =>
    ((Nat.prime_dvd_prime_iff_eq hp hr).mp hpr).le
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · exact (h' 3 Nat.prime_three h).trans (by norm_num)
          · exact (h' 5 Nat.prime_five h).trans (by norm_num)
        · exact (h' 7 (by norm_num) h).trans (by norm_num)
      · exact (h' 11 (by norm_num) h).trans (by norm_num)
    · exact (h' 13 (by norm_num) h).trans (by norm_num)
  · exact h' 17 (by norm_num) h

/-- The hypotheses of the main theorem, in the form of `Challenge.lean`. -/
theorem IsConvexPrimeSeq.of_forall {q : ℕ → ℕ} (hmono : StrictMono q)
    (h : ∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) : IsConvexPrimeSeq q :=
  ⟨hmono, fun n => (h n).1, fun n => (h n).2⟩

namespace IsConvexPrimeSeq

variable {q : ℕ → ℕ} (hq : IsConvexPrimeSeq q)
include hq

/-! ### Gaps -/

theorem add_gap (n : ℕ) : q n + gap q n = q (n + 1) := by
  have := hq.strictMono (Nat.lt_add_one n)
  rw [gap]
  omega

theorem gap_pos (n : ℕ) : 0 < gap q n := by
  have := hq.strictMono (Nat.lt_add_one n)
  rw [gap]
  omega

theorem gap_mono : Monotone (gap q) :=
  monotone_nat_of_le_succ hq.gap_le_gap

/-- A term of the sequence is the sum of an earlier term and the gaps in between. -/
theorem add_sum_gap (n k : ℕ) : q n + ∑ i ∈ Finset.range k, gap q (n + i) = q (n + k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ← add_assoc, ih, hq.add_gap, add_assoc]

/-- If all the gaps from `n` on are equal to `d`, then the sequence contains the composite
number `q n * (1 + d)`: a convex sequence of primes cannot have eventually constant gaps. -/
theorem not_forall_gap_eq (n d : ℕ) : ¬∀ k, n ≤ k → gap q k = d := by
  intro h
  have hsum := hq.add_sum_gap n (q n)
  rw [Finset.sum_congr rfl fun i _ => h (n + i) (Nat.le_add_right n i), Finset.sum_const,
    Finset.card_range, smul_eq_mul] at hsum
  have hd : d ≠ 0 := by
    have := hq.gap_pos n
    rw [h n le_rfl] at this
    omega
  have hmul : q n + q n * d = q n * (1 + d) := by ring
  exact Nat.not_prime_mul (hq.prime n).one_lt.ne' (by omega)
    (hmul ▸ hsum ▸ hq.prime (n + q n))

/-- **Lemma 4(a)**: the gaps of a convex sequence of primes are unbounded. -/
theorem exists_le_gap (x : ℕ) : ∃ n, x ≤ gap q n := by
  by_contra! h
  have hbdd : BddAbove (Set.range (gap q)) := ⟨x, by rintro _ ⟨n, rfl⟩; exact (h n).le⟩
  obtain ⟨a, ha⟩ := Nat.sSup_mem (Set.range_nonempty (gap q)) hbdd
  refine hq.not_forall_gap_eq a (gap q a) fun k hk => le_antisymm ?_ (hq.gap_mono hk)
  rw [ha]
  exact le_csSup hbdd ⟨k, rfl⟩

/-! ### The terms beyond `17` -/

theorem exists_seventeen_lt : ∃ n, 17 < q n :=
  ⟨18, (hq.strictMono.id_le 18).trans_lt' (by norm_num)⟩

theorem seventeen_lt {n : ℕ} (hn : start q ≤ n) : 17 < q n := by
  have h : 17 < q (start q) := Nat.sInf_mem hq.exists_seventeen_lt
  exact h.trans_le (hq.strictMono.monotone hn)

/-- **Lemma 4(b)**: from `start q` on, the terms are coprime to `M`. -/
theorem coprime_M {n : ℕ} (hn : start q ≤ n) : Nat.Coprime (q n) M :=
  (Nat.Prime.coprime_iff_not_dvd (hq.prime n)).mpr fun h =>
    (le_seventeen_of_dvd_M (hq.prime n) h).not_gt (hq.seventeen_lt hn)

theorem odd {n : ℕ} (hn : start q ≤ n) : Odd (q n) :=
  (hq.prime n).odd_of_ne_two (by have := hq.seventeen_lt hn; omega)

/-- **Lemma 4(b)**: from `start q` on, the gaps are even. -/
theorem even_gap {n : ℕ} (hn : start q ≤ n) : Even (gap q n) :=
  Nat.Odd.sub_odd (hq.odd (hn.trans (Nat.le_succ n))) (hq.odd hn)

theorem two_le_gap {n : ℕ} (hn : start q ≤ n) : 2 ≤ gap q n := by
  obtain ⟨k, hk⟩ := hq.even_gap hn
  have := hq.gap_pos n
  omega

/-! ### The runs of equal gaps -/

theorem exists_first (x : ℕ) : ∃ n, start q ≤ n ∧ x ≤ gap q n := by
  obtain ⟨n, hn⟩ := hq.exists_le_gap x
  exact ⟨max n (start q), le_max_right _ _, hn.trans (hq.gap_mono (le_max_left _ _))⟩

theorem start_le_first (x : ℕ) : start q ≤ first q x :=
  (Nat.sInf_mem (hq.exists_first x)).1

theorem le_gap_first (x : ℕ) : x ≤ gap q (first q x) :=
  (Nat.sInf_mem (hq.exists_first x)).2

omit hq in
theorem first_le {x n : ℕ} (hn : start q ≤ n) (hx : x ≤ gap q n) : first q x ≤ n :=
  Nat.sInf_le ⟨hn, hx⟩

/-- For `n ≥ start q`, the index `n` is before the run of gaps `x` if and only if its gap is
smaller than `x`. -/
theorem lt_first_iff {x n : ℕ} (hn : start q ≤ n) : n < first q x ↔ gap q n < x := by
  refine ⟨fun h => lt_of_not_ge fun hx => (first_le hn hx).not_gt h, fun h => ?_⟩
  by_contra! h'
  exact (h.trans_le ((hq.le_gap_first x).trans (hq.gap_mono h'))).false

theorem first_mono : Monotone (first q) := fun _ y hxy =>
  first_le (hq.start_le_first y) (hxy.trans (hq.le_gap_first y))

/-- Two thresholds that no gap beyond `start q` separates have the same `first`. -/
theorem first_eq_first {x y : ℕ} (h : ∀ n, start q ≤ n → (gap q n < x ↔ gap q n < y)) :
    first q x = first q y := by
  refine le_antisymm (first_le (hq.start_le_first y) (not_lt.mp fun hlt => ?_))
    (first_le (hq.start_le_first x) (not_lt.mp fun hlt => ?_))
  · exact ((h _ (hq.start_le_first y)).mp hlt).not_ge (hq.le_gap_first y)
  · exact ((h _ (hq.start_le_first x)).mpr hlt).not_ge (hq.le_gap_first x)

theorem first_eq_start {x : ℕ} (hx : x ≤ 2) : first q x = start q :=
  le_antisymm (first_le le_rfl (hx.trans (hq.two_le_gap le_rfl))) (hq.start_le_first x)

/-- No gap beyond `start q` is odd, so the run of gaps `2 e + 1` is empty. -/
theorem first_two_mul_add_two (e : ℕ) : first q (2 * e + 2) = first q (2 * e + 1) := by
  refine hq.first_eq_first fun n hn => ?_
  obtain ⟨k, hk⟩ := hq.even_gap hn
  omega

theorem first_add_runLength (d : ℕ) : first q d + runLength q d = first q (d + 1) :=
  Nat.add_sub_of_le (hq.first_mono (Nat.le_succ d))

/-- All the gaps in the run `[first q d, first q (d + 1))` are equal to `d`. -/
theorem gap_eq {d n : ℕ} (h₁ : first q d ≤ n) (h₂ : n < first q (d + 1)) : gap q n = d := by
  have hn := (hq.start_le_first d).trans h₁
  have := (hq.lt_first_iff hn).mp h₂
  have := (hq.le_gap_first d).trans (hq.gap_mono h₁)
  omega

/-- **Lemma 6(b)**: the run of gaps `d` is an arithmetic progression with difference `d`. -/
theorem q_first_add {d j : ℕ} (hj : j ≤ runLength q d) :
    q (first q d + j) = q (first q d) + j * d := by
  rw [← hq.add_sum_gap, Finset.sum_congr rfl fun i hi => hq.gap_eq (Nat.le_add_right _ i)
    (by have := hq.first_add_runLength d; simp at hi; omega)]
  simp

theorem q_first_succ (d : ℕ) : q (first q (d + 1)) = q (first q d) + runLength q d * d := by
  rw [← hq.first_add_runLength, hq.q_first_add le_rfl]

/-- The terms of the run of gaps `d` are primes. -/
theorem prime_add_mul {d j : ℕ} (hj : j ≤ runLength q d) :
    (q (first q d) + j * d).Prime :=
  hq.q_first_add hj ▸ hq.prime _

/-- The terms of the run of gaps `d` are coprime to `M`. -/
theorem coprime_add_mul {d j : ℕ} (hj : j ≤ runLength q d) :
    Nat.Coprime (q (first q d) + j * d) M :=
  hq.q_first_add hj ▸ hq.coprime_M ((hq.start_le_first d).trans (Nat.le_add_right _ _))

/-- **Lemma 6(d)**, telescoped: `first q (2 (e + n))` is `first q (2 e)` plus the lengths of the
runs of the even gaps `2 e, 2 (e + 1), …, 2 (e + n - 1)`. -/
theorem first_two_mul_add (e n : ℕ) :
    first q (2 * (e + n)) = first q (2 * e) + ∑ i ∈ Finset.range n, runLength q (2 * (e + i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (e + (n + 1)) = 2 * (e + n) + 2 by ring, hq.first_two_mul_add_two,
      ← hq.first_add_runLength, Finset.sum_range_succ, ih, add_assoc]

end IsConvexPrimeSeq

end Erdos455
