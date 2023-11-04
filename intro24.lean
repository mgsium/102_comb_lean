import Mathlib.Tactic

open Set
open Nat


def set_ℕ : Set ℕ := {n | n:ℕ}

def disjoint_nat_union (A B : Set ℕ) : Prop :=
  (A ∩ B = ∅) ∧ (A ∪ B = set_ℕ)

theorem intro24 (n a b: ℕ) (A B : Set ℕ) (h : disjoint_nat_union A B):
  ∀n, ∃ a b, a≠b ∧ a>n ∧ b>n
  ∧ ({a, b, a+b} ⊆ A ∨ {a, b, a+b} ⊆ B) := by
  by_cases h₀ : Set.Finite A
  . by_cases g : A=∅
    . intro n
      let a' := n+1
      let b' := n+2
      use a'
      use b'
      simp
      rw [g] at h
      unfold disjoint_nat_union at h
      simp at h
      unfold set_ℕ at h
      rw [h]
      simp
    . let m := Finset.max' $ Set.Finite.toFinset h₀
      let A' := Set.Finite.toFinset h₀
      sorry
  . sorry
  done


lemma ree : ¬(({1,2,3}:Set ℕ) ⊆ ∅) := by
  refine Nonempty.not_subset_empty ?_
  simp
  done
