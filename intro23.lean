import Mathlib.Tactic

open List
open Set
open Finset
open Nat

set_option maxHeartbeats 200000

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

-- n; {4,5,6,...,n}
-- c; cardinality of subsets
def all_c_subsets (c n : ℕ) : Finset (Finset ℕ) :=
  filter (λ X => card X = c) (four_to_n n).powerset

def tri_prop_c_subsets (n c : ℕ) : Finset (Finset ℕ) :=
  filter (λ X => (tri_prop X) ∧ (card X = c)) (four_to_n n).powerset

#eval tri_prop_c_subsets 7 3
#eval tri_prop_c_subsets 12 3

#eval all_c_subsets 2 5
#eval all_c_subsets 2 8

lemma four_to_n_subset {n : ℕ} : four_to_n n ⊆ four_to_n (n+1) := by
  unfold four_to_n
  intro x h
  simp at *
  constructor
  . linarith
  . exact h.right
  done

lemma c_subset (c n : ℕ) : (all_c_subsets c n) ⊆ (all_c_subsets c (n+1)):= by
  unfold all_c_subsets
  intro x
  simp
  intro h h₁
  constructor
  . exact Finset.Subset.trans h (four_to_n_subset)
  . exact h₁
  done

def all_c_subsets_satisfy_tri_prop (c n : ℕ) : Prop :=
  ∀(X:Finset ℕ), (X ⊆ four_to_n n) ∧ (card X = c) → tri_prop X

theorem intro23_254counterexample :
  ¬all_c_subsets_satisfy_tri_prop 10 254 := by
  let Y : Finset ℕ := {4, 5, 9, 14, 23, 37, 60, 97, 157, 254}
  have h₁ : Y ⊆ four_to_n 254 := by
    unfold four_to_n
    simp
  have h₂ : card Y = 10 := by rfl
  have h₃ : ¬tri_prop Y := by sorry --exact Bool.not_iff_not.mp rfl
  unfold all_c_subsets_satisfy_tri_prop
  push_neg
  use Y
  done

lemma counterexample_upwards (c k : ℕ) :
    ¬all_c_subsets_satisfy_tri_prop c k
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

lemma geq_254_no_tri_prop {n : ℕ} : n ≥ 254 → ¬all_c_subsets_satisfy_tri_prop 10 n := by
  intro h
  induction' n with d hd
  . contradiction
  . sorry
  done

def all_c_subsets_satisfy_tri_prop' (c n : ℕ) : Bool
  := all_c_subsets c n = tri_prop_c_subsets c n

def n_set : Set ℕ := {i:ℕ | all_c_subsets_satisfy_tri_prop 10 i}

theorem intro23 (n : ℕ) : n≥254 → n∉n_set := by
  unfold n_set
  simp
  intro h
  match n with
  | 254 => exact intro23_254counterexample
  | k+1 => apply (counterexample_upwards 10 k); sorry
  done
