import Mathlib

open Finset Nat

--[IMO Shortlist 1994] A subset M of {1,2,3,...,15} does not contain three elements whose product is a perfect square. Determine the maximum number of elements in M.

def is_perfect_square (n : ℕ) : Prop :=
  ∃ m : ℕ, m^2 = n

def is_bad (i j k : ℕ) : Prop :=
  is_perfect_square (i * j * k)

example : is_bad 2 3 6 := by
  use 6
  norm_num
  done

def set1 : Set ℕ := {1, 4, 9}
def set2 : Set ℕ := {2, 6, 12}
def set3 : Set ℕ := {3, 5, 15}
def set4 : Set ℕ := {7, 8, 14}

theorem disjoint_sets (a b : Set ℕ) (h : Disjoint a b) : ∀ x, x ∈ a → x ∉ b := by

  intro x hx
  sorry
  done



example : Disjoint set1 set2 := by
  unfold Disjoint
  intro x hx
  simp at *
  intro h
  apply?
  sorry
  done

example : Disjoint set1 set2 ∧ Disjoint set1 set3 ∧ Disjoint set1 set4 ∧ Disjoint set2 set3 ∧ Disjoint set2 set4 ∧ Disjoint set3 set4 := by
  simp [set1, set2, set3, set4]
  sorry
  done

-- if k=15, in general we can take ceil(√k)-1 instead of 3
example {n : ℕ} : n ^ 2 ≠ 15 := by
  have hn := le_or_lt n 3
  obtain hn' | hn' := hn
  · apply @Nat.ne_of_lt
    calc
      n ^ 2 ≤ 3 ^ 2 := by rel [hn']
      _ < 15 := by norm_num
  · have h₁ : n ≥ 4 := hn'
    norm_num at hn'
    symm; apply @Nat.ne_of_lt
    calc
      n^2 ≥ 4^2 := by rel [h₁]
      _ > 15 := by norm_num
    done


def my_set : Finset ℕ := range 16 \ singleton 0

def no_three_square_product (s : Finset ℕ) : Prop :=
  ∀ x y z : s, x ≠ y ∧ y ≠ z ∧ z ≠ x → ¬is_perfect_square (x * y * z)

theorem small_elements :
  ∃ s : Finset ℕ, s ⊆ my_set ∧ no_three_square_product s := by
    use {2, 3, 4, 5}
    simp
    unfold no_three_square_product
    simp
    norm_num
    sorry
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
