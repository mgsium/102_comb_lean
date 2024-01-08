import Mathlib.Tactic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2

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

open Finset Function

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup

universe u
variable {α : Type u}

private def swapProp (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
notation:50 lhs:51 " ~ " rhs:51 => swapProp lhs rhs

def union_prop (A B S : Finset ℕ) : Prop := A ∪ B = S

instance decUnion_prop (S : Finset ℕ) : DecidablePred (uncurry union_prop · S) := by
  unfold uncurry union_prop
  intro ⟨A,B⟩
  simp only
  exact decEq (A ∪ B) S
  done

def subset_dup (S : Finset ℕ) : (Finset $ Finset ℕ × Finset ℕ) :=
  filter (uncurry union_prop · S) (Finset.product (Finset.powerset S) (Finset.powerset S))

def upair_union_prop (A B S : Finset ℕ) : Prop := A ∪ B = S

instance decUpair_Union_prop (S : Finset ℕ) : DecidablePred (uncurry upair_union_prop · S) := by
  unfold uncurry upair_union_prop
  intro ⟨A,B⟩
  simp only
  exact decEq (A ∪ B) S
  done

def subset_pairs (S : Finset ℕ) : (Finset $ Finset ℕ × Finset ℕ) :=
  filter (uncurry union_prop · S) (Finset.product (Finset.powerset S) (Finset.powerset S))

def subset_upairs (S : Finset ℕ) : Finset (Sym2 $ Finset ℕ) :=
  image (Quot.mk (Sym2.Rel $ Finset ℕ) · ) $ subset_pairs S

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

set_option maxRecDepth 8000

theorem test : card (subset_upairs {1,2}) = 5 := by
  decide
  done

theorem test2 : card (subset_upairs {1,2,3}) = 14 := by
  decide
  done

theorem test3 : card (subset_upairs {1,2,3,4}) = 41 := by
  decide
  done

theorem test4 : card (subset_upairs {1,2,3,4,5}) = 122 := by
  sorry
  done

theorem intro22 : card (subset_pairs $ Finset.Icc 1 6) = 365 := by
  sorry
  done

theorem intro22generalisation (n : ℕ)
  : card (subset_pairs $ Finset.Icc 1 n) = (3^n - 1) / 2 + 1 := by
  sorry
  done
