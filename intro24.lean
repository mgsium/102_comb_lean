import Mathlib.Tactic

open Set
open Nat

/-!
# Intro 24 (pp.34-35) | [MOSP 1997]

> Let A and B be disjoint sets whose union is the set of natural numbers.
> Show that for every natural number n, there exist distinct a,b>n such that
> {a, b, a+b} ⊆ A or {a, b, a+b} ⊆ B.
-/

-- need to work with the set of naturals in this question, not type.
def set_ℕ : Set ℕ := {n | n:ℕ}

def disjoint_nat_union (A B : Set ℕ) : Prop :=
  (A ∩ B = ∅) ∧ (A ∪ B = set_ℕ)

theorem intro24 (n a b: ℕ) (A B : Set ℕ) (h : disjoint_nat_union A B):
  ∀n, ∃ a b, a≠b ∧ a>n ∧ b>n
  ∧ ({a, b, a+b} ⊆ A ∨ {a, b, a+b} ⊆ B) := by
  by_cases h₀ : Set.Finite A
  . by_cases g : ¬Set.Nonempty A
    . intro n
      use n+1
      use n+2
      simp
      rw [not_nonempty_iff_eq_empty.mp g] at h
      unfold disjoint_nat_union at h
      simp at h
      rw [h]
      unfold set_ℕ
      simp
    . intro n
      let m := Finset.max' $ Set.Finite.toFinset h₀
      simp at m
      simp at g
      let m' := m g
      by_cases h₁ : n≥m'
      . use n+1
        use n+2
        simp
        unfold disjoint_nat_union at h
        have h₂ : ∀i, i≥m' → i∈B := by
          simp
          sorry
        have h₃ : (n+1)≥m' := by exact le_step h₁
        have h₄ : (n+2)≥m' := by exact le_step h₃
        have h₅ : (n+1)+(n+2)≥m' := by exact le_add_left h₄
        have e : {n+1, n+2, n+1 + n+2} ⊆ B := by
          refine insert_subset (h₂ (n + 1) h₃) ?_
          refine insert_subset (h₂ (n + 2) h₄) ?_
          exact singleton_subset_iff.mpr (h₂ (n + 1 + n + 2) h₅)
        exact Or.inr e
      . sorry
      sorry
  . sorry
  done
