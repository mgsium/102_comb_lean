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

notation:50 lhs:51 " ⊻ " rhs:51 => lhs ↔ ¬rhs


lemma ree (A B S : Finset ℕ) (ha : A ⊆ S) (hb : B ⊆ S) : union_prop A B S ↔
  ∀ s ∈ S, ((s ∈ A ∧ s ∉ B) ⊻ (s ∉ A ∧ s ∈ B)) ⊻ (s ∈ A ∧ s ∈ B)
  := by
  unfold union_prop
  constructor
  . intro h s g
    have h' : s ∈ A ∨ s ∈ B := by
      rw [← h] at g
      simp only [mem_union] at g
      exact g
    cases h' <;> simp_all
  . intro h
    ext r
    simp only [mem_union]
    constructor
    . tauto
    . intro g
      have h' := h r g
      tauto
  done

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

#check (singleton 2 : Finset ℕ)

#eval (singleton (2, 3) : Finset (ℕ × ℕ))

-- def Conf (n : ℕ) := Finset (Fin n × Fin 3)

-- structure Conf (n : ℕ) where
--   val : Finset (Fin n × Fin 3)
--   pf  : card (filter (fun x ↦ x.2 = 2) val) ≤ card (filter (fun x ↦ x.2 = 1) val)

#eval filter (fun (x : ℕ × ℕ) => x.2 = 2) (singleton (2, 3))

def one_gt_two {n : ℕ} (S : Finset $ Fin n × Fin 3) :=
  card (filter (fun x ↦ x.2 = 2) S) ≤ card (filter (fun x ↦ x.2 = 1) S)

-- Cardinality of fintype (filter?)
-- example (n : ℕ) : Fintype.card (Conf n) = (3^n - 1)/2 + 1 := by

--   done

-- Cardinality of universal set
-- example (n : ℕ) : card (filter one_gt_two (@univ (Conf n) _)) = (3^n - 1)/2 + 1 := by

--   done

theorem intro22generalisation (n : ℕ)
  : card (subset_pairs $ Finset.Icc 1 n) = (3^n - 1) / 2 + 1 := by
  sorry
  done
