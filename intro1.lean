import Mathlib.Tactic

/-!
# Intro 1 (pp. 18) | [Revista Matematica Timişoara]
Mr. and Mrs. Zeta want to name their baby Zeta so that its monogram (first,
middle, and last initials) will be in alphabetical order with no letters
repeated. How nany such monograms are possible?

## Solution
The last initial is fixed at Z. If the first initial is A, then the second
initial must be one of B,C,D,...,X,Y, so there are 24 choices for the second.
If the first initial is B, then the second must be in C,D,E,...,X,Y, so there
are 23 choices for the second initial. Continuing in this way, we see that the
number of monograms is 24+23+22+...+2+1 = 300.

-/

--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

open Nat Set BigOperators


end useful_lemmas


--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------
open Nat Finset BigOperators

def Alphabet : Type := Fin 26

instance instDecidableEqAlphabet : DecidableEq Alphabet := instDecidableEqFin 26
instance instLTAlphabet : LT Alphabet := instLTFin

theorem intro1 {a b : ℕ}: card {(a,b) | (a < b) ∧ (b < 26)} = 300 := by
  simp
  sorry
