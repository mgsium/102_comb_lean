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

universe u
variable {α : Type u}

private def swapProp (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
notation:50 lhs:51 " ~ " rhs:51 => swapProp lhs rhs

private theorem swapProp.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩

private theorem swapProp.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)

private theorem swapProp.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)

theorem swapEquiv : Equivalence $ @swapProp α :=
  ⟨swapProp.refl, swapProp.symm, swapProp.trans⟩

instance uprodSetoid (α : Type u) : Setoid (α × α) :=
  ⟨swapProp, swapEquiv⟩

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)
notation "「" a₁ ", " a₂ "」" => mk a₁ a₂

--(ha : A ⊆ S) (hb : B ⊆ S)
def union_prop (A B S : Finset ℕ) : Prop := A ∪ B = S

instance decUnion_prop (S : Finset ℕ) : DecidablePred (uncurry union_prop · S) := by
  unfold uncurry union_prop
  intro ⟨A,B⟩
  simp only
  exact decEq (A ∪ B) S
  done

--「」
lemma swap_eq (a b : Finset ℕ) : 「a, b」 = 「b, a」 := by
  refine Quot.sound ?_
  unfold Setoid.r
  unfold uprodSetoid
  simp only
  unfold swapProp
  right
  trivial
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

instance psetSetoid (P : Finset ℕ × Finset ℕ) : Setoid P :=
   ⟨swapProp, swapEquiv⟩

def subset_upairs (P : Finset $ Finset ℕ × Finset ℕ) : (Finset $ UProd $ Finset ℕ) :=
  Quotient psetSetoid
  done

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
