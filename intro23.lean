import Mathlib.Tactic


open Set
open Finset
open Nat

def tri_ineq (a b c : ℕ) : Bool :=
  a + b < c

lemma tri_ineq_symm (a b c : ℕ) : tri_ineq a b c = tri_ineq b a c := by
  unfold tri_ineq
  rw [add_comm]
  done

def tri_prop (X : Finset ℕ) : Bool :=
  ∃ a b c : X,
   (tri_ineq a b c
  ∧ tri_ineq b c a
  ∧ tri_ineq c a b)


def range_set (n : ℕ) (h : n ≥ 4) : Finset ℕ :=
  (Finset.range n) \ {0,1,2,3}
  -- {i : ℕ | 4≤i ∧ i≤n}'(by linarith)


theorem intro23 (n : ℕ) (h₀ : n≥4) (X : Finset ℕ)
  : List.maximum {n : (∀X, X⊆range_set n h₀ ∧ card X = 10 ∧ tri_prop X)} = 253
  := by

  done
