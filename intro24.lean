import Mathlib.Tactic

open Set
open Nat

def disjoint_nat_union (A B : Set ℕ) : Prop :=
  (A ∩ B = ∅) ∧ (A ∪ B = ℕ)

theorem intro24 (n a b: ℕ) (A B : Set ℕ) :
  disjoint_nat_union A B
  → ∀n, ∃ a b, a>n ∧ b>n
  ∧ ({a, b, a+b} ⊆ A ∨ {a, b, a+b} ⊆ B) := by
  sorry
  done
