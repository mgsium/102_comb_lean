import Mathlib

open Finset Nat 

def is_perfect_square (n : ℕ) : Prop :=
  ∃ m : ℕ, m^2 = n

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
    use {2, 4, 5}
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
