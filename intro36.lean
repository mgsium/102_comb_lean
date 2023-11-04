import Mathlib.Tactic

open List
open Set
open Nat


lemma perm_list (n : ℕ) : ∃X, X.length = n ∧ List.toFinset X = Finset.range n := by
  use List.range n
  constructor
  . simp
  . refine (Finset.ext ?h.a).symm
    intro x
    simp
  done

theorem intro36 (n : ℕ) (X : List ℕ) (h₀ : X.length = n)
  (h₁ : List.toFinset X = Finset.range n) :
  ∃X, ∀i j, i≠j ∧ i<j ∧ j<n → (∀k, i≤k ∧ k≤j → (X[i]! + X[j]!)/2) := by
  sorry
  done



/-
theorem intro36 : ∀n, ∃X, X.length = n ∧ List.toFinset X = Finset.range n
  ∧ (∀i j, i≠j ∧ i<n ∧ j<n → ∀k, j≤k ∧ k≤i
  → X[k]! ≠ (X[i]!+X[j]!/2)) := by
  intro n
  constructor
  constructor
  .
  . sorry
  . simp
  . refine (Finset.ext ?h.a).symm
    intro x
    simp
  done
-/
