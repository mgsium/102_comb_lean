import Mathlib.Tactic

variable (n : ℕ)

open Nat
open BigOperators
open Finset

-- def n : ℕ := 11

def my_set : Finset ℕ := range (1+(n-1)/2) \ singleton 0

lemma aux1 : ∑ k in range (n+1), choose n k = 2^n := by
  exact sum_range_choose n
  done

def my_set2 : Finset ℕ := range n \ singleton 0

lemma aux1' : ∑ k in my_set2 n, choose n k = 2^n-2 := by
    sorry
    done

lemma aux2 (h:n > 1)(h': Odd n): 2 * ∑ k in my_set n, choose n k = 2^n-2 := by
  simp [my_set]
  sorry
  done


-- #eval ∑ k in my_set, choose n k
-- #eval 2^(n-1)-1

def binomial_coefficients_set (n : ℕ) : Finset ℕ :=
(range ((n - 1) / 2)).map ⟨λ k => Nat.choose n (k + 1), by sorry⟩

#eval binomial_coefficients_set 13

def odd_binomials_finset (n : ℕ) : Finset ℕ :=
filter (λ k => Odd (Nat.choose n k)) (range ((n + 1) / 2) \ singleton 0)

#eval odd_binomials_finset 7

theorem odd_number_of_odd_numbers {n : ℕ} (h : Odd n) :
  Odd (card (odd_binomials_finset n)) := by
  sorry
  done


#check sum_filter_add_sum_filter_not

theorem odd_filter (set' : Finset ℕ) :
   ∑ k in set', k = ∑ k in (set'.filter (λ x => Odd x)), k
   +  ∑ k in (set'.filter (λ x => ¬ Odd x)), k   := by
   exact (sum_filter_add_sum_filter_not set' (fun x => Odd x) fun x => x).symm
   done

#check even_add

lemma odd_sum (set' : Finset ℕ) (h: ¬Odd (card (filter (fun x => Odd x) set'))):
 Even (∑ k in filter (fun x => Odd x) set', k) := by
  simp
  sorry
  done

lemma evensss_sum (X : Finset ℕ )(h: ∀ x ∈ X, Even x): Even (∑ k in X, k) := by
  unfold Even
  sorry
  done


lemma even_sum (set' : Finset ℕ): Even (∑ k in filter (fun x => ¬Odd x) set', k) := by
  simp
  unfold Even
  sorry
  done

theorem general_odd {n : ℕ} (set' : Finset ℕ) (h : Odd (∑ k in set', k)) :
  Odd (card (set'.filter (λ x => Odd x))) := by
  contrapose h
  rw [odd_filter]
  sorry
  done
