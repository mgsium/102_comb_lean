import Mathlib.Tactic

open List
open Set
open Finset
open Nat

def tri_ineq (a b c : ℕ) : Bool :=
  a + b > c

lemma tri_ineq_symm (a b c : ℕ) : tri_ineq a b c = tri_ineq b a c := by
  unfold tri_ineq
  rw [add_comm]
  done

def tri_prop (X : Finset ℕ) : Bool :=
  ∃ a b c : X, a≠b ∧ b≠c ∧ c≠a
  ∧ tri_ineq a b c
  ∧ tri_ineq b c a
  ∧ tri_ineq c a b

def four_to_n (n : ℕ) : Finset ℕ :=
  (Finset.range (n+1)) \ {0,1,2,3}
  -- {i : ℕ | 4≤i ∧ i≤n}'(by linarith)

def finset_max (S : Finset ℕ) : ℕ :=
  match Finset.max S with
  | some a => a
  | none => 0

-- n; {4,5,6,...,n}
-- c; cardinality of subsets
def all_c_subsets (c n : ℕ) : Finset (Finset ℕ) :=
  filter (card · = c) (four_to_n n).powerset

def tri_prop_c_subsets (n c : ℕ) : Finset (Finset ℕ) :=
  filter (fun X => (tri_prop X) ∧ (card X = c)) (four_to_n n).powerset

#eval tri_prop_c_subsets 7 3
#eval tri_prop_c_subsets 12 3

#eval all_c_subsets 2 5
#eval all_c_subsets 2 8

lemma four_to_n_subset (n : ℕ) : four_to_n n ⊆ four_to_n (n+1) := by
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
  . exact Finset.Subset.trans h (four_to_n_subset n)
  . exact h₁
  done

lemma counterexample_upwards (c k : ℕ) :
    (all_c_subsets 10  k   ) ≠ (tri_prop_c_subsets 10  k   )
  → (all_c_subsets 10 (k+1)) ≠ (tri_prop_c_subsets 10 (k+1))
  := by
  contrapose
  push_neg
  intro h
  --rw [Finset.ext]
  sorry
  done

def all_c_subsets_satisfy_tri_prop (c n : ℕ) : Bool :=
  (all_c_subsets c n) = (tri_prop_c_subsets c n)

-- {4, 5, 9, 14, 23, 37, 60, 97, 157, 254} does not satisfy tri_prop
theorem intro23_254counterexample (X : Finset ℕ) :
  ¬all_c_subsets_satisfy_tri_prop 10 254 := by
  by_contra h
  unfold all_c_subsets_satisfy_tri_prop at h
  sorry
  done

--theorem intro23 (n : ℕ) (X : Finset ℕ)
--  : Finset.max {i | (all_c_subsets 10 n h₀) = (tri_prop_c_subsets 10 n h₀)} = 253 := by
--  done
