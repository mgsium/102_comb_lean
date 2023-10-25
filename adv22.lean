import Mathlib

open Finset Nat

--[IMO Shortlist 1994] A subset M of {1,2,3,...,15} does not contain three elements whose product is a perfect square. Determine the maximum number of elements in M.


instance : DecidablePred (@IsSquare ℕ _) :=
  fun m => decidable_of_iff' (Nat.sqrt m * Nat.sqrt m = m) <| by
    simp_rw [←Nat.exists_mul_self m, IsSquare, eq_comm]

-- set_option maxRecDepth 10000
-- set_option maxHeartbeats 1000000


-- def is_bad (i j k : ℕ) : Prop :=
--   is_perfect_square (i * j * k)


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



def my_set : Finset ℕ := range 16 \ singleton 0

def no_three_square_product (s : Finset ℕ) : Prop :=
  ∀ x y z : s, x ≠ y ∧ y ≠ z ∧ z ≠ x → ¬IsSquare (x * y * z : ℕ)

instance : DecidablePred no_three_square_product := fun _ => Fintype.decidableForallFintype

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
