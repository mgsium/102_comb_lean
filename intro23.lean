import Mathlib.Tactic

/-!
# Intro 23 (p.34) | [AIME 2001]

A set of positive numbers has the _triangle property_ if it has three
distinct elements that are the lengths of the sides of a triangle whose area
is positive. Consider sets {4,5,6,...,n} of consecutive positive integers, all
of whose ten-element subsets have the triangle property. What is the largest
possible value of n?

-/

open Finset Nat List

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup

def tri_ineq (a b c : ℕ) : Prop :=
  a + b > c

-- a, b, and c satisfy tri_ineq in all permutations
def tri_prop (X : Finset ℕ) : Prop :=
  ∃ a b c : X, a≠b ∧ b≠c ∧ c≠a
  ∧ tri_ineq a b c
  ∧ tri_ineq b c a
  ∧ tri_ineq c a b

-- n; {4,5,6,...,n}
-- c; cardinality of subsets
def all_c_subsets_satisfy_tri_prop (c n : ℕ) : Prop :=
  ∀(X : Finset ℕ), (X ⊆ Icc 4 n) ∧ (card X = c) → tri_prop X

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

-- [4,n] ⊆ [4,n+1]
lemma four_to_n_subset {n : ℕ} : Icc 4 n ⊆ Icc 4 (n+1) := by
  intro x h
  simp only [gt_iff_lt, mem_Icc] at *
  constructor <;> linarith
  done

-- Not all 10-element subsets satisfy tri_prop for n = 254.
lemma intro23_254counterexample
    : ¬all_c_subsets_satisfy_tri_prop 10 254 := by
  let Y : Finset ℕ := {4, 5, 9, 14, 23, 37, 60, 97, 157, 254}
  have h₁ : Y ⊆ Icc 4 254 := by
    simp_all only [mem_insert, Finset.mem_singleton, gt_iff_lt]
  have h₂ : card Y = 10 := by rfl
  have h₃ : ¬tri_prop Y := by exact Bool.not_iff_not.mp rfl
  unfold all_c_subsets_satisfy_tri_prop
  push_neg
  use Y
  done

-- A counterexample for n = k is also a counterexample for n = k + 1.
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

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro23 (n : ℕ)
    : n ≥ 254 → ¬all_c_subsets_satisfy_tri_prop 10 n := by
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
