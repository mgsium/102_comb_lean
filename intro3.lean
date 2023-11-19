import Mathlib.Tactic

/-!
# Intro 3 (pp. 18) | [Revista Matematica Timişoara]
Let n be an odd integer greater than 1. Prove that the sequence [(n choose 1) ,..., (n choose (n-1)/2)] contains an odd number of odd numbers.

## Solution
The sum of the numbers in the given sequence equals 2^(n-1)-1, which is odd; hence, the result follows.
-/

open Nat
open BigOperators
open Finset

variable (n : ℕ)
-- we first show that the sum of the given sequence is 2^(n-1)-1

lemma split_sum (h: 1 < n): ∑ k in Ico 0 (n+1), choose n k
  = choose n 0 + ∑ k in Ico 1 n, choose n k + choose n n := by
  rw [sum_eq_sum_Ico_succ_bot, sum_Ico_succ_top]
  norm_num
  rfl
  all_goals linarith
  done

lemma aux1 (h: 1 < n): ∑ k in Ico 1 n, choose n k + 2 = 2^n  := by
  rw [← sum_range_choose n, ← Ico_zero_eq_range]
  simp_rw [split_sum n h]
  norm_num
  exact add_comm _ _
  done

lemma sub_right (k m : ℕ) (h: k + 2 = m): m - 2 = k := by
  rw [Nat.sub_eq_of_eq_add]
  rw [h]
  done

lemma aux1' (h: 1 < n): 2^n - 2 = ∑ k in Ico 1 n, choose n k := by
  exact sub_right _ (2^n) (aux1 n h)
  done

lemma aux1'_2 (h: 1 < n): (∑ k in Ico 1 n, choose n k)/2 = (2^n-2)/2 := by
  rw [aux1' n h]
  done

def my_set : Finset ℕ := Ico 1 ((n+1)/ 2)

lemma binom_symm (h: 1 < n): ∑ k in Ico 1 n, choose n k
  = 2 * ∑ k in my_set n, choose n k := by
  unfold my_set
  have g :  (n+1) / 2 ≤ n := by
    apply Nat.div_le_of_le_mul
    linarith
    done
  rw [← sum_Ico_consecutive _ _ g]
  · extract_goal
    sorry
  · have h''' : 0 < 2 := by linarith
    have h': 2 ≤ n+1 := by linarith
    refine (Nat.le_div_iff_mul_le ?k0).mpr h'
    norm_num
    done
  done

lemma binom_symm_2 (h: 1 < n): ∑ k in my_set n, choose n k
  =  (∑ k in Ico 1 n, choose n k)/2 := by
  rw [Nat.div_eq_of_eq_mul_right (by norm_num) (by exact binom_symm _ h)]
  done

lemma aux4': (2^n-2)/2 = 2^(n-1)-1 := by
  have aux4: 2^n-2 = 2*(2^(n-1)-1) := by
    cases' n with d
    · simp
    · simp
      rw [Nat.pow_succ', Nat.mul_sub_left_distrib]
    done
  rw [Nat.div_eq_of_eq_mul_right (by norm_num) (by exact aux4)]
  done

lemma aux5 (h: 1 < n): ∑ k in my_set n, choose n k = 2^(n-1)-1 := by
  rw [binom_symm_2 n h, aux1'_2 n h, aux4' n]
  done

-- we prove that 2^(n-1)-1 is always odd for n > 1.

lemma pow_prop1 (m: ℕ)(h: 0 < m) : 2^m = 2^(m-1) * 2 := by
  cases' m with d
  · contradiction
  · simp
    rw [Nat.pow_succ', mul_comm]
    done
  done

lemma pow_prop2 (m: ℕ)(h: 1 < m) : 2^(m-1) = 2^(m-2) * 2 := by
  cases' m with d
  · contradiction
  · simp
    exact pow_prop1 d (by linarith)
    done
  done

lemma nat_sub (k : ℕ)(h₁ : k > 1) :
  k - 1 = k - 2 + 1 := by
  cases' k with d
  · contradiction
  · simp
    exact Nat.eq_add_of_sub_eq (by linarith) rfl
    done

lemma power_odd (h: 1 < n): Odd (2^(n-1) - 1) := by
  use 2^(n-2)-1
  have h₁ : 1 < 2 * 2 ^ (n - 2) := by
    have h₂ : 1 ≤ 2^(n-2) := by exact one_le_two_pow (n - 2)
    linarith
    done
  rw [pow_prop2 n h, Nat.mul_sub_left_distrib, mul_comm]
  norm_num
  rw [nat_sub _ h₁]
  done

lemma sum_odd (h: 1 < n): Odd (∑ k in my_set n, choose n k) := by
  rw [aux5 n h]
  exact power_odd n h
  done

-- if the sum of the elements of a finset is odd, then the finset contains an odd number of odd numbers.

theorem odd_filter (set' : Finset ℕ) :
   ∑ k in set', k = ∑ k in (set'.filter Odd), k
   +  ∑ k in (set'.filter (¬ Odd ·)), k := by
   exact (sum_filter_add_sum_filter_not set' _ _).symm
   done

def even_sum_finset (X: Finset ℕ) : Prop :=
  (∀ x ∈ X, Even x) → Even (∑ k in X, k)

lemma even_sum (X : Finset ℕ): even_sum_finset X := by
  have empty : even_sum_finset ∅ := by
    simp only [even_sum_finset]
    done
  refine @Finset.induction ℕ even_sum_finset _ empty ?_ X
  intro a X' h g
  unfold even_sum_finset at *
  rw [sum_insert h, even_add]
  simp_all only [mem_insert, or_true, implies_true]
  done

lemma one_leq_odd (x : ℕ) (h' : Odd x) : 1 ≤ x := by
    unfold Odd at h'
    cases' h' with r hr
    linarith
    done

lemma sum_minus_dist (X : Finset ℕ) (h: ∀ x ∈ X, x ≥ 1) :
    ∑ x in X, (x - 1) = ∑ x in X, x - ∑ x in X, 1 := by
  rw [eq_tsub_iff_add_eq_of_le (sum_le_sum h)]
  · rw [←sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    exact Nat.sub_add_cancel (h x hx)
  done

def sum_odds_finset (X: Finset ℕ): Prop :=
  (Even $ card X) ∧ (∀ x ∈ X, Odd x) → Even (∑ k in X, k)

lemma sum_odds (X : Finset ℕ) : sum_odds_finset X := by
  unfold sum_odds_finset Even
  simp_rw [←mul_two]
  intro h
  rcases h with ⟨⟨r, hr⟩, h'⟩
  use ((∑ k in X, (k-1) / 2) + r)
  rw [right_distrib, sum_mul]
  have h'': ∀ (x : ℕ), x ∈ X → x ≥ 1 := by
    intros x hx
    specialize h' x hx
    exact one_leq_odd x h'
    done
  have h: ∑ x in X, (x - 1) / 2 * 2 = ∑ x in X, (x - 1) := by
    apply sum_congr rfl
    intro x hx
    have h₁ : 2 ∣ (x - 1) := by
      specialize h' x hx
      apply even_iff_two_dvd.mp
      specialize h'' x hx
      cases' h' with r hr
      rw [hr]
      norm_num
      done
    exact Nat.div_mul_cancel h₁
    done
  rw [h, sum_minus_dist X, ← card_eq_sum_ones X, hr]
  apply Nat.eq_add_of_sub_eq _ rfl
  · rw [← hr, card_eq_sum_ones X]
    exact sum_le_sum h''
    done
  exact h''
  done

lemma filter_odd_sum (set' : Finset ℕ) (h: ¬Odd (card (filter Odd set'))):
 Even (∑ k in (set'.filter Odd), k) := by
  rw [even_iff_not_odd.symm] at h
  let odd_set := filter Odd set'
  have h' : ∀ x ∈ odd_set, Odd x := by
    intros x hx
    simp at hx
    obtain ⟨_,h2⟩ := hx
    rw [odd_iff_not_even]
    exact h2
  apply (sum_odds odd_set ⟨h, h'⟩)
  done

lemma filter_even_sum (set' : Finset ℕ):
  Even (∑ k in filter (¬ Odd ·) set', k) := by
  let even_set := filter (¬ Odd ·) set'
  have h : ∀ x ∈ even_set, Even x := by
    intros x hx
    simp at hx
    exact hx.2
  apply (even_sum even_set h)
  done

theorem odd_number_of_odd_numbers (set' : Finset ℕ) (h : Odd (∑ k in set', k)) :
  Odd (card (set'.filter Odd)) := by
  contrapose h
  rw [odd_iff_not_even, not_not, odd_filter]
  apply Even.add (filter_odd_sum set' h) (filter_even_sum set')
  done


-- we finally prove the main result

-- def my_set : Finset ℕ := Ico 1 (Nat.div (n+1) 2)

def binomial_set (n : ℕ) : Finset ℕ :=
  (my_set n).image (Nat.choose n ·)

#eval binomial_set 7

theorem intro3 {n : ℕ} (h : Odd n) (h': 1 < n) :
  Odd (card ((binomial_set n).filter Odd)) := by
  have h1 : Odd (∑ k in my_set n, Nat.choose n k) := by
    exact sum_odd n h'
  have h2 : Odd (∑ k in image (fun x ↦ Nat.choose n x) (my_set n), k) := by
    unfold my_set at *
    sorry
  unfold binomial_set
  apply odd_number_of_odd_numbers (binomial_set n) h2
  done
