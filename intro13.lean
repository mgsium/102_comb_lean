import Mathlib.Tactic

/-!
# Intro 1 (p.3)
Find the number of ordered quadruples (x₁,x₂,x₃,x₄) of positive odd integers
that satisfy x₁ + x₂ + x₃ + x₄ = 98.

## Solution

ree

-/

open Nat Finset BigOperators

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup

def quadProp (x : Fin 99 × Fin 99 × Fin 99 × Fin 99) : Prop :=
  (x.1.val + x.2.1.val + x.2.2.1.val + x.2.2.2.val = 98)
  ∧ (Odd x.1.val ∧ Odd x.2.1.val ∧ Odd x.2.2.1.val ∧ Odd x.2.2.2.val)

instance decQuadProp : DecidablePred quadProp := by
  unfold quadProp
  intro x
  exact And.decidable
  done

def quadSet : Finset (Fin 99 × Fin 99 × Fin 99 × Fin 99) :=
  filter (quadProp ·) univ

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

lemma nCr : Nat.choose 50 3 = 19600 := rfl

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro13 : card quadSet = 19600 := by
  rw [← nCr]
  unfold quadSet quadProp

  done
