import Mathlib

open Finset Nat

--[IMO Shortlist 1994] A subset M of {1,2,3,...,15} does not contain three elements whose product is a perfect square. Determine the maximum number of elements in M.

/-
Solution: (Adapted from: 102 Combinatorial Problems by T. Andreescu, Z. Feng):

For a set M, let |M| denote the number of elements in M. A set M is termed 'good' if it is a subset of S = {1, 2, 3, ... , 15}
and doesn't contain three elements whose product forms a perfect square. The objective is to find the maximum size of M,
where M is good. If m represents this maximum, a triple of numbers {i, j, k}, 1 ≤ i < j < k ≤ 15, is called 'bad'
if the product ijk is a perfect square.

Initially, prove m < 11. Given the disjoint bad triples B1 = {1, 4, 9}, B2 = {2, 6, 12}, B3 = {3, 5, 15}, and B4 = {7, 8, 14},
if |M| is 12, all three numbers in at least one of these triples are in M. Consequently, M is not good if |M| ≥ 12, which leads
to the conclusion that m < 11.

If m equals 11, then for a good set M with |M| being 11, M is the set difference S - {a1, a2, a3, a4},
where each ai belongs to a corresponding Bi, for i in {1, 2, 3, 4}. Given this, 10 is an element of M. Since 10 belongs to M
and considering the bad triples B1, B4, B5, and B6, where 10 is the only recurring element, M equals S - {b1, b4, b5, b6}.
The numbers 1, 4, and 9 are absent from M. Given the presence of two separate bad triples {2, 3, 6} and {7, 8, 14},
to ensure M remains good, it's necessary to remove a minimum of two additional numbers. This means |M| is less than 10,
which contradicts the earlier assumption that |M| equals 11. Thus, the assumption is incorrect and m is less than 10.

Upon closer examination, the set {1, 4, 5, 6, 7, 10, 11, 12, 13, 14} meets the problem's criteria.
Therefore, 10 isℤ) (h₀ : n ≥ 4) the upper limit for the number of elements in M.
-/

instance : DecidablePred (@IsSquare ℕ _) :=
  fun m => decidable_of_iff' (Nat.sqrt m * Nat.sqrt m = m) <| by
    simp_rw [←Nat.exists_mul_self m, IsSquare, eq_comm]

-- set_option maxRecDepth 10000
-- set_option maxHeartbeats 1000000




def set1 : Finset ℕ := {1, 4, 9}
def set2 : Finset ℕ := {2, 6, 12}
def set3 : Finset ℕ := {3, 5, 15}
def set4 : Finset ℕ := {7, 8, 14}



example : set1 ∩ set2 = ∅  := by
  simp [set1, set2]
  done

-- example : Disjoint set1 set2 := by
--   unfold Disjoint
--   intro x hx
--   simp at *
--   intro h
--   apply Set.subset_inter h hx
--   done

example : Disjoint set1 set2 ∧ Disjoint set1 set3 ∧ Disjoint set1 set4 ∧ Disjoint set2 set3 ∧ Disjoint set2 set4 ∧ Disjoint set3 set4 := by
  simp [set1, set2, set3, set4]
  done



def my_set : Finset ℕ := erase (range 16) 0


def is_bad (i j k : ℕ) : Prop :=
  IsSquare (i * j * k : ℕ) ∧ i ∈ my_set ∧ j ∈ my_set ∧ k ∈ my_set

def no_three_square_product (s : Finset ℕ) : Prop :=
  ∀ x y z : s, x ≠ y ∧ y ≠ z ∧ z ≠ x → ¬IsSquare (x * y * z : ℕ)

instance : DecidablePred no_three_square_product := fun _ => Fintype.decidableForallFintype

-- def is_bad (s : Finset ℕ) (h : s ⊆ my_set) (h1: s.card = 3) : Prop :=
--   ¬ no_three_square_product s


instance (x : my_set) : OfNat my_set x := by
  simp [my_set]
  sorry
  done

theorem no_bad_triplet_with_5 : ∀ j k : my_set, ¬ is_bad 5 j k := by
  simp [no_three_square_product]
  unfold is_bad
  intro j k
  simp [my_set]
  have j = 10 ∨ k = 10 := by
    exact j
    sorry
  sorry
  done

example : is_bad 1:my_set  4  9  := by
  simp [is_bad]
  done



-- lemma two : ¬∃

theorem main : no_three_square_product {1, 4, 5, 6, 7, 10, 11, 12, 13, 14} := by
  sorry
  done


theorem small_elementss :
  ∃ s : Finset ℕ, s ⊆ my_set ∧ no_three_square_product s := by
    use {2, 3, 4, 5}
    simp
    done

-- theorem ten_elements :
--   ∃ s : Finset ℕ, s ⊆ my_set ∧ no_three_square_product s ∧ s.card = 10 := by
--     use {1, 4, 5, 6, 7, 10, 11, 12, 13, 14}
--     simp
--     unfold no_three_square_product
--     by_cases h1 :
--     done

theorem max_elements_with_condition :
  ∀ s : Finset ℕ, s ⊆ my_set → (no_three_square_product s → max s.card = 10) := by
    sorry
    done
