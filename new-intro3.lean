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

--extras

-- theorem odd_n_plus_one_div_two (n : ℚ) (h : Odd n) : ∃ m : ℕ, (n + 1) / 2 = m := by
--   unfold Odd at h
--   rcases h with ⟨d, hd⟩

--   done

variable (n : ℕ)
-- we first show that the sum of the given sequence is 2^(n-1)-1

lemma split_sum (h: 1 < n): ∑ k in Ico 0 (n+1), choose n k = choose n 0  + ∑ k in Ico 1 n, choose n k + choose n n := by
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

#check choose_symm


-- lemma nat_is_nat (n:ℕ)(h: Odd n): ((n+1)/ (2:ℚ)) ∈ ℕ := by
--   sorry
--   done

def my_set : Finset ℕ := Ico 1 (Nat.div (n+1) 2)

lemma binom_symm (h: 1 < n): ∑ k in Ico 1 n, choose n k = (2:ℚ) * ∑ k in my_set n, choose n k  := by
  unfold my_set
  have g : Nat.div (n+1) 2 ≤ n := by
    sorry
    done
  rw [← sum_Ico_consecutive _ _ g]
  . sorry
  · sorry
  done

#check Nat.div_eq_of_eq_mul_right

lemma binom_symm_2 (h: 1 < n): ∑ k in my_set n, choose n k
  =  (∑ k in Ico 1 n, choose n k)/2 := by
  have h₁ : 0 < 2 := by norm_num
  have h₂ : ∑ k in Ico 1 n, choose n k = 2 * ∑ k in my_set n, choose n k
    := by sorry -- exact binom_symm
  rw [Nat.div_eq_of_eq_mul_right h₁ h₂]
  done

lemma aux3 (h: 1 < n): (∑ k in Ico 1 n, choose n k)/2
  =  (2^n-2)/2 := by
  sorry
  done

lemma aux4 (h: 1 < n): (2^n-2)/2 = 2^(n-1)-1 := by
  induction' n with d hd
  . norm_num
  . sorry
  done

lemma aux5 (h: 1 < n): ∑ k in my_set n, choose n k = 2^(n-1)-(1:ℚ) := by
  sorry
  done

-- we prove that 2^(n-1)-1 is always odd for n > 1.

theorem Nat.pow_sucq' {m: ℚ}{n : ℕ} : m ^ succ n = m * m ^ n := by
    rfl
    done

lemma pow_prop (m: ℕ)(h: m > 1) : (2:ℚ)^(m-1) = 2^(m-2) * 2 := by
  cases' m with d
  · contradiction
  · simp
    sorry
    --rw [Nat.pow_sucq', mul_comm]
    done
  done

#check Nat.div

lemma power_odd (h: 1 < n): Odd (2^(n-1) - (1:ℚ)) := by
  use 2^(n-2)-1
  ring_nf
  norm_num
  exact pow_prop n h
  done

lemma sum_odd (h: 1 < n): Odd (∑ k in my_set n, choose n k + (0:ℚ)) := by
  rw [aux5 n h]
  norm_num
  exact power_odd n h
  done

-- if the sum of the elements of a finset is odd, then the finset contains an odd number of odd numbers.

#check Finset.card_insert_of_not_mem

universe u_2

#check Odd.add_odd

theorem odd_add_one {α : Type u_2} [Semiring α] {m : α} (h: Odd m)
  : Even (m + 1) := Odd.add_odd h odd_one

theorem odd_iff_even_add_one {m : ℕ}
  : Odd m ↔ Even (m + 1) := by
    constructor
    . exact odd_add_one
    . contrapose
      rw [← even_iff_not_odd, ← odd_iff_not_even]
      exact Even.add_one
    done

theorem odd_filter (set' : Finset ℕ) :
   ∑ k in set', k = ∑ k in (set'.filter Odd), k
   +  ∑ k in (set'.filter (¬ Odd ·)), k := by
   exact (sum_filter_add_sum_filter_not set' _ _).symm
   done

def even_sum_finset (X: Finset ℕ) : Prop :=
  (∀ x ∈ X, Even x) → Even (∑ k in X, k)

lemma even_sum (X : Finset ℕ) :even_sum_finset X := by
  have empty : even_sum_finset ∅ := by
    simp only [even_sum_finset]
    done
  refine @Finset.induction ℕ even_sum_finset _ empty ?_ X
  intro a X' h g
  unfold even_sum_finset at *
  intro h'
  rw [sum_insert h, even_add]
  have even_a : Even a := by
    simp only [h', mem_insert, true_or]
    done
  constructor
  . intro _
    apply g
    intro x hₓ
    apply h'
    simp [mem_insert, hₓ]
  . rw [imp_iff_not_or]
    simp [even_a]
  done

def odd_sum_finset (X: Finset ℕ): Prop :=
  (Even $ card X) ∧ (∀ x ∈ X, Odd x) → Even (∑ k in X, k)

lemma even_sum_of_odd (X : Finset ℕ) : odd_sum_finset X := by
  unfold odd_sum_finset Even Odd
  intro h

  -- have empty : odd_sum_finset ∅ := by
  --   simp only [odd_sum_finset]
  --   done

  -- refine @Finset.induction ℕ odd_sum_finset _ empty ?_ X
  -- intro a X' h g
  -- unfold odd_sum_finset at *
  -- intro h'

  -- by_contra h'
  -- push_neg at h'

  -- have odd_card_X' : Odd (card X') := by
  --   have ⟨hₗ, _⟩ := h'.1
  --   rw [card_insert_of_not_mem h] at hₗ
  --   exact odd_iff_even_add_one.mpr hₗ
  --   done



  -- by_cases h': Even (card X')
  -- . rw [Finset.card_insert_of_not_mem h, imp_iff_not_or, not_and_or]
  --   left; left
  --   simp only [even_iff_not_odd, not_not, Even.add_one h']
  -- . rw [sum_insert h, even_add]
  --   intro h''
  --   by_contra
  --   have odd_card_X' : Odd (card X') := by
  --     rw [odd_iff_not_even]
  --     exact h'
  --     done

    -- constructor
    -- . rw [imp_iff_not_or]
    --   left
    --   rw [even_iff_not_odd, not_not]
    --   apply h''.2
    --   simp_rw [mem_insert]
    --   left
    --   trivial
    -- . contradiction

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
  apply (odd_sum odd_set h h')
  exact n

lemma filter_even_sum (set' : Finset ℕ):
  Even (∑ k in filter (¬ Odd ·) set', k) := by
  let even_set := filter (¬ Odd ·) set'
  have h : ∀ x ∈ even_set, Even x := by
    intros x hx
    simp at hx
    obtain ⟨_,h2⟩ := hx
    exact h2
  apply (even_sum even_set rfl h)
  done

theorem odd_number_of_odd_numbers (set' : Finset ℕ) (h : Odd (∑ k in set', k)) :
  Odd (card (set'.filter Odd)) := by
  contrapose h
  simp
  rw [odd_filter]
  have h1: Even (∑ k in filter (¬ Odd ·) set', k)
    := by exact filter_even_sum set'
  -- even odds + even evens = even
  have h2: Even (∑ k in filter (Odd ·) set', k)
    := by exact filter_odd_sum set'
  apply Even.add h2 h1
  done
