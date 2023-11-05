import Mathlib.Tactic

open Set
open Nat

/-!
# Intro 24 (pp.34) | [MOSP 1997]

Let A and B be disjoint sets whose union is the set of natural numbers.
Show that for every natural number n, there exist distinct a,b>n such that
{a, b, a+b} ⊆ A or {a, b, a+b} ⊆ B.
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
      have f : A=∅ := by exact not_nonempty_iff_eq_empty.mp g
      let a' := n+1
      let b' := n+2
      use a'
      use b'
      simp
      rw [f] at h
      unfold disjoint_nat_union at h
      simp at h
      rw [h]
      unfold set_ℕ
      simp
    . intro n
      let m := Finset.max' $ Set.Finite.toFinset h₀
      --let A' := Set.Finite.toFinset h₀
      simp at m
      sorry
  . sorry
  done




lemma ree : ¬(({1,2,3}:Set ℕ) ⊆ ∅) := by
  refine Nonempty.not_subset_empty ?_
  simp
  done
