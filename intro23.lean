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

def four_to_n (n : ℕ) (h : n ≥ 4) : Finset ℕ :=
  (Finset.range (n+1)) \ {0,1,2,3}
  -- {i : ℕ | 4≤i ∧ i≤n}'(by linarith)

def finset_max (S : Finset ℕ) : ℕ :=
  match Finset.max S with
  | some a => a
  | none => 0

-- n; {4,5,6,...,n}
-- c; cardinality of subsets
def tri_prop_c_subsets (n c : ℕ) (h₀ : n≥4) : Finset (Finset ℕ) :=
  filter (fun X => (tri_prop X) ∧ (card X = c)) (four_to_n n h₀).powerset

def all_c_subsets (n c : ℕ) (h₀ : n≥4) : Finset (Finset ℕ) :=
  filter (fun X => card X = c) (four_to_n n h₀).powerset

#eval tri_prop_c_subsets 15 3 (by norm_num)

theorem intro23 (n : ℕ) (h₀ : n≥4) (X : Finset ℕ)
  : Finset.max {i | (tri_prop_c_subsets n 10 h₀) = (all_c_subsets n 10 h₀)} = 253 := by
  sorry
  done

--theorem intro23_254counterexample :
