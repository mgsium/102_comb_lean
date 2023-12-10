import Mathlib.Tactic

/-!
# Intro 22 (p.4)
Let S be a set with six elements. How many different ways are there to select
two not necessarily distinct subsets A and B of S such that A ∪ B = S?

## Solution
For each element s ∈ S, exactly one of the following statements holds:
⬝ s ∈ A ∧ s ∉ B
⬝ s ∉ A ∧ s ∈ B
⬝ s ∈ A ∧ s ∈ B
So if S has n elements, there are 3ⁿ ways to choose A and B. Apart from cases
with A = B, this counts each pair of sets exactly twice, since we may permute A
and B. Also, since A ∪ B = S, A = B if and only if A = B = S, so the total
number of pairs is ((3ⁿ - 1)/2) + 1.

-/

open Nat Finset Function

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup

-- (ha : A ⊆ S) (hb : B ⊆ S)
def union_prop (A B S : Finset ℕ) : Prop := A ∪ B = S

instance decUnion_prop (S : Finset ℕ) : DecidablePred (uncurry union_prop · S) := by
  unfold uncurry union_prop
  intro ⟨A,B⟩
  simp only
  exact decEq (A ∪ B) S
  done

def subset_pairs (S : Finset ℕ) : (Finset (Finset ℕ × Finset ℕ)) :=
  filter (uncurry union_prop · S) (Finset.product (Finset.powerset S) (Finset.powerset S))

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas


end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro22 : card (subset_pairs {1,2,3,4,5,6}) = 365 := by
  sorry
  done

theorem intro22generalised (n : ℕ) : card (subset_pairs $ Finset.Icc 1 n) = (3^n - 1) / 2 + 1 := by
  sorry
  done
