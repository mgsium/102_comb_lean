
import Mathlib.Tactic


/-!
# Intro 2 (p.2)

The student lockers at Olympic High are numbered consecutively beginning with
locker number 1. The plastic digits used to number the lockers cost two cents
apiece, e.g. it costs 2 cents to label locker numbers 1-9, 4 cents to label
locker numbers 10-99, 6 cents to label locker numbers 100-999, etc.

If it costs 137.94 to label all the lockers, how many lockers are there at the
school?

## Solution Sketch

case analysis go brrr

-/

open Nat
open Finset
open BigOperators

def digit_count (N : ℕ) : ℕ :=
  log 10 N - 1

lemma ree : ∑ x in Icc 1 2001, digit_count x = ∑ x in Icc 1 9, 1
  + ∑ x in Icc 10 99, 2 + ∑ x in Icc 100 999, 3 + ∑ x in Icc 1000 2001, 4
  := by
  have h : Icc 1 2001 = Icc 1 9 ∪ Icc 10 99 ∪ Icc 100 999 ∪ Icc 1000 2001 := by
    ext x
    repeat rw [mem_union]
    simp only [mem_Icc]
    constructor
    . intro g

    . sorry

  repeat rw [sum_union]
  . unfold digit_count
    rw [h]

  . sorry
  . sorry
  . sorry
  done


-- theorem intro1 : ∑ x in Icc 1 n, 0.02 * digit_count x = 137.94 → 2001 := by

--   done
