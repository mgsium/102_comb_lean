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


-- universe u
-- variable {α : Type u}

-- def swapProp {α : Type u} (X Y : α × α) : Prop := X = Y ∨ X = Prod.swap Y
-- notation:50 lhs:51 " ~ " rhs:51 => swapProp lhs rhs

-- lemma swap.refl : Reflexive (@swapProp α) := by
--   unfold swapProp
--   intro X
--   exact Or.inl rfl
--   done

-- lemma swap.symm : Symmetric (@swapProp α) := by
--   unfold swapProp
--   intro X Y h
--   by_cases h' : X = Y
--   . exact Or.inl h'.symm
--   . simp_rw [h'] at h
--     simp only [false_or] at h
--     exact Or.inr $ Prod.swap_inj.mp h.symm
--   done

-- lemma swap.trans : Transitive (@swapProp α) := by
--   unfold swapProp
--   intro X Y Z hxy hyz
--   cases' hxy with a ha
--   cases' hyz with b hb
--   . exact Or.inl $ Eq.trans a b
--   . rw [← a] at hb
--     exact Or.inr hb
--   . cases' hyz with c hc
--     . rw [c] at ha
--       exact Or.inr ha
--     . apply_fun Prod.swap at hc
--       simp_rw [Prod.swap_swap] at hc
--       exact Or.inl $ Eq.trans ha hc
--   done

-- theorem swapEquiv : Equivalence $ @swapProp α :=
--   ⟨swapProp.refl, swapProp.symm, swapProp.trans⟩

-- (ha : A ⊆ S) (hb : B ⊆ S)
def union_prop (A B S : Finset ℕ) : Prop := A ∪ B = S

instance decUnion_prop (S : Finset ℕ) : DecidablePred (uncurry union_prop · S) := by
  unfold uncurry union_prop
  intro ⟨A,B⟩
  simp only
  exact decEq (A ∪ B) S
  done

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
  intro X Y Z hxy hyz
  cases' hxy with a ha
  cases' hyz with b hb
  . exact Or.inl $ Eq.trans a b
  . rw [← a] at hb
    exact Or.inr hb
  . cases' hyz with c hc
    . rw [c] at ha
      exact Or.inr ha
    . apply_fun Prod.swap at hc
      simp_rw [Prod.swap_swap] at hc
      exact Or.inl $ Eq.trans ha hc
  done

theorem swapEquiv : Equivalence swapProp :=
  ⟨swapProp_refl, @swapProp_symm, @swapProp_trans⟩

def subsetSetoid : Setoid $ Finset ℕ × Finset ℕ :=
  { r := swapProp, iseqv := swapEquiv}

instance instSubsetSetoid : Setoid $ Finset ℕ × Finset ℕ :=
  { r := swapProp, iseqv := swapEquiv}

def unordered : Type := Quotient instSubsetSetoid

def upair (a b : Finset ℕ) : unordered := Quotient.mk' (a, b)
notation "|" a "," b "|" => upair a b

lemma swap_eq (a b : Finset ℕ) : |a, b| = |b, a| := by
  refine Quot.sound ?_
  unfold Setoid.r
  unfold instSubsetSetoid
  simp only
  unfold swapProp
  right
  trivial

def subset_dup (S : Finset ℕ) : (Finset $ Finset ℕ × Finset ℕ) :=
  filter (uncurry union_prop · S) (Finset.product (Finset.powerset S) (Finset.powerset S))

def upair_union_prop (A B S : Finset ℕ) : Prop := A ∪ B = S

instance decUpair_Union_prop (S : Finset ℕ) : DecidablePred (uncurry upair_union_prop · S) := by
  unfold uncurry upair_union_prop
  intro ⟨A,B⟩
  simp only
  exact decEq (A ∪ B) S
  done


def subset_upairs (S : Finset ℕ) : Finset unordered :=
  filter (uncurry union_prop · S) (upair (Finset.powerset S) (Finset.powerset S))



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

-- theorem test : card (subset_pairs {1,2}) = 9 := by
--   decide
--   done

-- theorem test2 : card (subset_pairs {1,2,3}) = 27 := by
--   decide
--   done

-- theorem test3 : card (subset_pairs {1,2,3,4}) = 81 := by
--   decide
--   done

-- theorem test4 : card (subset_pairs {1,2,3,4,5}) = 243 := by
--   decide
--   done

-- theorem intro22 : card (subset_pairs $ Finset.Icc 1 6) = 729 := by
--   decide
--   done

-- theorem intro22generalisation (n : ℕ) : card (subset_pairs $ Finset.Icc 1 n) = (3^n - 1) / 2 + 1 := by
--   sorry
--   done
