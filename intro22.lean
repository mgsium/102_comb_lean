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

open Finset Function

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup

def swapProp (X Y : Finset ℕ × Finset ℕ) : Prop := X = Y ∨ X = Prod.swap Y

lemma swapProp_refl : Reflexive (swapProp) := by
  unfold swapProp
  intro X
  exact Or.inl rfl
  done

lemma swapProp_symm : Symmetric (swapProp) := by
  unfold swapProp
  intro X Y h
  by_cases h' : X = Y
  . exact Or.inl h'.symm
  . simp_rw [h'] at h
    simp only [false_or] at h
    exact Or.inr $ Prod.swap_inj.mp h.symm
  done

lemma swapProp_trans : Transitive (swapProp) := by
  unfold swapProp
  intro X Y Z h h'
  by_cases hxy : X = Y
  . rw [← hxy] at h'
    exact h'
  . simp_rw [hxy, false_or] at h
    apply_fun Prod.swap at h
    simp only [Prod.swap_swap] at h
    rw [← h] at h'
    simp only [Prod.swap_inj] at h'
    by_cases hxz : X = Z
    . exact Or.inl hxz
    . simp_rw [hxz, or_false] at h'
      apply_fun Prod.swap at h'
      simp only [Prod.swap_swap] at h'
      exact Or.inr h'
  done

theorem swapEquiv : Equivalence swapProp :=
  ⟨swapProp_refl, @swapProp_symm, @swapProp_trans⟩

-- (ha : A ⊆ S) (hb : B ⊆ S)
def union_prop (A B S : Finset ℕ) : Prop := A ∪ B = S

instance decUnion_prop (S : Finset ℕ) : DecidablePred (uncurry union_prop · S) := by
  unfold uncurry union_prop
  intro ⟨A,B⟩
  simp only
  exact decEq (A ∪ B) S
  done

def subset_pairs (S : Finset ℕ) : (Finset $ Finset ℕ × Finset ℕ) :=
  filter (uncurry union_prop · S) (Finset.product (Finset.powerset S) (Finset.powerset S))

def subset_quot := Quotient { r := swapProp, iseqv := swapEquiv}


end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

#eval subset_pairs {1,2}

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem test : card (subset_pairs {1,2}) = 9 := by
  decide
  done

theorem intro22 : card (subset_pairs $ Finset.Icc 1 6) = 324 := by
  sorry
  done

theorem intro22generalisation (n : ℕ) : card (subset_pairs $ Finset.Icc 1 n) = (3^n - 1) / 2 + 1 := by
  sorry
  done
