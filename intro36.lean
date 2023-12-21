import Mathlib.Tactic

open List Set Nat

/-!
# Intro 36 (p. 37)
Determine, with proof, if it is possible to arrange 1, 2, ... , 1000 in a row
such that the average of any pair of distinct numbers is not located in between
the two numbers.

## Solution
...
-/

def isGoodFor (X : List ℕ) (i j : Fin X.length) :=
  i < j ∧ Even (X.get i + X.get j) → ¬ (i ≤ avg ∧ avg ≤ j)
    where avg := List.indexOf ((X.get i + X.get j) / 2)

--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro36 (n : ℕ) (X : List ℕ)
  : ∃ X, Perm X (range n) ∧ (∀ i j, isGoodFor X i j)  := by
  sorry
  done
