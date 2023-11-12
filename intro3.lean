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

lemma aux1 : ∑ k in range (n+1), choose n k = 2^n := by
  exact sum_range_choose n
  done

def my_set2 : Finset ℕ := Icc 1 (n-1)

lemma hello (h: 1 < n): ∑ k in Ico 0 (n+1), choose n k = choose n 0  + ∑ k in Ico 1 n, choose n k + choose n n := by
  rw [sum_eq_sum_Ico_succ_bot]
  rw [sum_Ico_succ_top (by linarith)]
  norm_num
  exact rfl
  linarith
  done

example (k:ℕ): Ico 0 k = range k := by
  simp only [Ico_zero_eq_range]
  done

lemma aux1' (h: 1 < n): ∑ k in Ico 1 n, choose n k + 2 = 2^n  := by
  rw [← sum_range_choose n, ← Ico_zero_eq_range]
  simp_rw [hello n h]
  norm_num
  exact add_comm _ _
  done

def my_set : Finset ℕ := range (1+(n-1)/2) \ singleton 0


#check choose_symm
def my_set9 : Finset ℕ := Ico 1 (Nat.div (n+1) 2)

lemma binom_symm (h: 1 < n): 2 * ∑ k in my_set9 n, choose n k
  = ∑ k in Ico 1 n, choose n k := by
  unfold my_set9
  symm
  have g : Nat.div (n+1) 2 ≤ n := by
    sorry
    done
  rw [← sum_Ico_consecutive _ _ g]
  . sorry
  · sorry
  done

-- we prove that 2^(n-1)-1 is always odd for n > 1.

theorem Nat.pow_sucq' {m: ℚ}{n : ℕ} : m ^ succ n = m * m ^ n := by
    exact rfl
    done

lemma pow_prop (m: ℕ)(h: m > 1) : (2:ℚ)^m = 2^(m-1) * 2 := by
  cases' m with d
  · contradiction
  · simp
    rw [Nat.pow_sucq', mul_comm]
    done
  done

lemma power_odd (h: n > 1): Odd (2^n - (1:ℚ)) := by
  use 2^(n-1) - 1
  ring_nf
  norm_num
  exact pow_prop n h
  done

-- #eval ∑ k in my_set, choose n k
-- #eval 2^(n-1)-1

def binomial_coefficients_set (n : ℕ) : Finset ℕ :=
(range ((n - 1) / 2)).map ⟨λ k => Nat.choose n (k + 1), by sorry⟩

#eval binomial_coefficients_set 13

def odd_binomials_finset (n : ℕ) : Finset ℕ :=
filter (λ k => Odd (Nat.choose n k)) (range ((n + 1) / 2) \ singleton 0)

#eval odd_binomials_finset 7

-- if the sum of the elements of a set is odd, then the set contains an odd number of odd numbers.

theorem odd_number_of_odd_numbers {n : ℕ} (h : Odd n) :
  Odd (card (odd_binomials_finset n)) := by
  sorry
  done

theorem odd_filter (set' : Finset ℕ) :
   ∑ k in set', k = ∑ k in (set'.filter Odd), k
   +  ∑ k in (set'.filter (λ x => ¬ Odd x)), k   := by
   exact (sum_filter_add_sum_filter_not set' (fun x => Odd x) fun x => x).symm
   done

lemma odd_sum {n : ℕ} (X : Finset ℕ) (h': card X = 2*n): Even (∑ k in X, k) := by
  unfold Even
  induction' n with d hd
  .simp [card_eq_zero.mp h']
   use 0
   rfl
  . sorry
  done

lemma filter_odd_sum (set' : Finset ℕ) (h: ¬Odd (card (filter Odd set'))):
 Even (∑ k in filter (fun x => Odd x) set', k) := by
  rw [even_iff_not_odd.symm] at h
  sorry
  -- simp at h
  -- exact h
  done

lemma even_sum {n : ℕ} (X : Finset ℕ) (h': card X = n)(h: ∀ x ∈ X, Even x):
  Even (∑ k in X, k) := by
  unfold Even
  induction' n with d hd
  .simp [card_eq_zero.mp h']
   use 0
   rfl
  . obtain ⟨x, hx⟩ : ∃ x, x ∈ X := card_pos.mp (h'.symm ▸ succ_pos d)
    let X' := erase X x
    have hX' : card X' = d := (card_erase_of_mem hx).trans (congrArg pred h')
    have h'' : Even (∑ k in X', k) := sorry
    obtain ⟨k, hk⟩ := h x hx
    have h''' : Even (k + ∑ k in X', k) := by
      have he: Even k := by sorry
      apply Even.add he h''
    sorry
    done
  done

lemma filter_even_sum (set' : Finset ℕ):
  Even (∑ k in filter (fun x => ¬Odd x) set', k) := by
  let even_set := filter (fun x => ¬Odd x) set'
  have h : ∀ x ∈ even_set, Even x := by
    intros x hx
    simp at hx
    obtain ⟨_,h2⟩ := hx
    exact h2
  apply (even_sum even_set rfl h)
  done

theorem general_odd (set' : Finset ℕ) (h : Odd (∑ k in set', k)) :
  Odd (card (set'.filter (λ x => Odd x))) := by
  contrapose h
  simp
  rw [odd_filter]
  have h1: Even (∑ k in filter (fun x => ¬Odd x) set', k)
    := by exact filter_even_sum set'
  have h2: Even (∑ k in filter (fun x => Odd x) set', k)
    := by exact filter_odd_sum set' h
  apply Even.add h2 h1
  done
