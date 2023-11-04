

import Mathlib.Tactic

/-
# Problem Statement

> "A set of positive numbers has the _triangle property_ if it has three
> distinct elements that are the lengths of the sides of a triangle whose area
> is positive. Consider sets {4,5,6,...,n} of consecutive positive integers, all
> of whose ten-element subsets have the triangle property. What is the largest
> possible value of n?"

-/



open Finset
open Nat
open List

def tri_ineq (a b c : ℕ) : Bool :=
  a + b > c

def tri_prop (X : Finset ℕ) : Bool :=
  ∃ a b c : X, a≠b ∧ b≠c ∧ c≠a
  ∧ tri_ineq a b c
  ∧ tri_ineq b c a
  ∧ tri_ineq c a b

def range_from_to (a b : ℕ) : Finset ℕ :=
  (Finset.range (b)) \ (Finset.range (a))

def four_to_n (n : ℕ) : Finset ℕ :=
  range_from_to 4 (n+1)

lemma four_to_n_subset {n : ℕ} : four_to_n n ⊆ four_to_n (n+1) := by
  unfold four_to_n range_from_to
  intro x h
  simp at *
  constructor <;> linarith
  done

-- n; {4,5,6,...,n}
-- c; cardinality of subsets
def all_c_subsets_satisfy_tri_prop (c n : ℕ) : Prop :=
  ∀(X:Finset ℕ), (X ⊆ four_to_n n) ∧ (card X = c) → tri_prop X

theorem intro23_254counterexample
  : ¬all_c_subsets_satisfy_tri_prop 10 254 := by
  let Y : Finset ℕ := {4, 5, 9, 14, 23, 37, 60, 97, 157, 254}
  have h₁ : Y ⊆ four_to_n 254 := by
    unfold four_to_n
    simp
  have h₂ : card Y = 10 := by rfl
  have h₃ : ¬tri_prop Y := by exact Bool.not_iff_not.mp rfl
  unfold all_c_subsets_satisfy_tri_prop
  push_neg
  use Y
  done

lemma counterexample_upwards (c k : ℕ)
  : ¬all_c_subsets_satisfy_tri_prop c k
  → ¬all_c_subsets_satisfy_tri_prop c (k+1) := by
  unfold all_c_subsets_satisfy_tri_prop
  push_neg
  choose Y h
  use Y
  repeat (any_goals constructor)
  . apply Finset.Subset.trans h.1.1
    exact four_to_n_subset
  . exact h.1.2
  . exact h.2
  done

theorem intro23_upper_bound (n : ℕ)
  : n ≥ 254 → ¬all_c_subsets_satisfy_tri_prop 10 n := by
  simp
  intro g
  induction' n with d hd
  . contradiction
  . by_cases 254 = succ d
    . rw [← h]
      exact intro23_254counterexample
    . have : d ≥ 254 := lt_succ.mp $ Nat.lt_of_le_of_ne g h
      apply (counterexample_upwards 10 d)
      exact hd this
  done










lemma exists_solution : ∃n, all_c_subsets_satisfy_tri_prop 10 n := by
  unfold all_c_subsets_satisfy_tri_prop
  have h : ¬(∀X, (X ⊆ four_to_n 0 ∧ card X = 10)) := by
    simp
    use ∅
    simp
  use 0
  by_contra g
  simp at g
  done

#eval Nat.find exists_solution

lemma name (X : List ℕ) : ¬tri_prop X.toFinset ∧ card X.toFinset = 10
  → min {n | ¬all_c_subsets_satisfy_tri_prop 10 n} ≥ 254 := by
  sorry
  done

theorem intro23_lower_bound (n : ℕ) (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ : ℕ)
  : n ≤ 253 → all_c_subsets_satisfy_tri_prop 10 n := by
  contrapose
  push_neg
  intro h
  unfold all_c_subsets_satisfy_tri_prop at h
  simp at h
  let (X : List ℕ) := [a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀]-- (a_1,a_10 ∈ [N])
  have h₃ : ¬tri_prop X.toFinset := by sorry
  have c₀ : card X.toFinset = 10 := by sorry
  wlog h₂ : List.Sorted Nat.lt X
  sorry
  sorry
  done

/-
let (x : Finset ℕ) := {a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀}
wlog h₀ : a₁<a₂ ∧ a₂<a₃ ∧ a₃<a₄ ∧ a₄<a₅ ∧ a₅<a₆
        ∧ a₆<a₇ ∧ a₇<a₈ ∧ a₈<a₉ ∧ a₉<a₁₀
-/
