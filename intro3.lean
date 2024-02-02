import Mathlib.Tactic
import Common

/-!
# Intro 3 (pp. 18) | [Revista Matematica Timişoara]
Let n be an odd integer greater than 1. Prove that the sequence
[(n choose 1) ,..., (n choose (n-1)/2)] contains an odd number of odd numbers.

## Solution
The sum of the numbers in the given sequence equals 2^(n-1)-1, which is always
odd for n > 1. The sum being odd is sufficient to conclude that the sequence
contains an odd number of odd numbers.
-/

open Finset BigOperators

variable (n : ℕ)

def half_n_set : Finset ℕ := Ico 1 ((n + 1) / 2)

def binomial_set (n : ℕ) : Finset ℕ := (half_n_set n).image (Nat.choose n ·)

--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

open Nat

-- f k < f (k+1) on Ico a b implies f is strictly monotone on Icc a b
-- this lemma will be in Mathlib in future (thanks Gareth for temporary proof)
lemma strictMono_s_of_lt_succ {a b : ℕ}{f : ℕ → ℕ}
    (hf : ∀ k ∈ Set.Ico a b, f k < f k.succ) : StrictMonoOn f (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · revert hf
    refine le_induction ?_ ?_ _ hab
    · simp only [Set.Icc_self, Set.strictMonoOn_singleton, implies_true]
    · intro n hn h h' x hx y hy hxy
      specialize h (fun k hk ↦ h' k
        (by simp [Set.mem_Ico.mp hk, lt_trans, lt_succ, le_of_lt]))
      by_cases hy' : y = n + 1
      · subst hy'
        replace hxy := lt_succ.mp hxy
        apply lt_of_le_of_lt ?_ (h' n ?_)
        · apply h.monotoneOn ?_ (Set.right_mem_Icc.mpr hn) hxy
          exact Set.mem_Icc.mpr ⟨(Set.mem_Icc.mp hx).left, hxy⟩
        · simp only [hn, Set.mem_Ico, lt_succ_self, and_true]
      · have hy : y ∈ Set.Icc a n := by
          rw [Set.mem_Icc] at hy ⊢
          exact ⟨hy.left, lt_succ.mp <| lt_of_le_of_ne hy.right hy'⟩
        have hx : x ∈ Set.Icc a n := by
          rw [Set.mem_Icc] at hx ⊢
          constructor
          . exact hx.left
          . apply le_of_lt <| lt_of_lt_of_le hxy _
            exact (Set.mem_Icc.mp hy).right
        exact h hx hy hxy
  · rw [Set.Icc_eq_empty_of_lt (lt_of_not_ge hab)]
    exact fun _ h ↦ h.elim

-- le version of choose_lt_succ_of_le_half_left in mathlib
lemma choose_lt_succ_of_le_half_left {r n : ℕ} (h : r + 1 ≤ n / 2) :
    Nat.choose n r < Nat.choose n (r + 1) := by
  refine' lt_of_mul_lt_mul_right _ (Nat.zero_le (n - r))
  rw [← Nat.choose_succ_right_eq]
  apply Nat.mul_lt_mul_of_pos_left _ (choose_pos <| le_trans h (div_le_self n 2))
  · rw [lt_tsub_iff_left, ← add_assoc, ← mul_two]
    have := Nat.mul_le_of_le_div 2 _ _ h
    rwa [add_mul, one_mul] at this

-- we first show that the sum of the given sequence is 2^(n-1)-1

lemma split_sum (h: 1 < n): ∑ k in Ico 0 (n+1), choose n k
    = choose n 0 + ∑ k in Ico 1 n, choose n k + choose n n := by
  rw [sum_eq_sum_Ico_succ_bot, sum_Ico_succ_top]
  all_goals linarith

lemma sum_shift (h: 1 < n): ∑ k in Ico 1 n, choose n k + 2 = 2^n := by
  rw [← sum_range_choose n, ← Ico_zero_eq_range]
  simp_rw [split_sum n h]
  norm_num
  exact add_comm _ _

lemma sum_div2 (h: 1 < n): (∑ k in Ico 1 n, choose n k) / 2 = (2^n-2) / 2 := by
  have h' : 2^n - 2 = ∑ k in Ico 1 n, choose n k := by
    exact Nat.sub_eq_of_eq_add (sum_shift n h).symm
  rw [h']

-- start of lemmas needed for binom_symm_bij

lemma half_succ_le_sub_of_ge_one (x : ℕ) (h1 : 1 ≤ x) (h2: x ≤ n)
    (h3 : x < (n + 1) / 2) : (n + 1) / 2 ≤ n - x := by
  rw [le_tsub_iff_left h2]
  have h := (lt_iff_le_pred (by linarith)).mp h3
  apply le_trans (Nat.add_le_add_right h _)
  rw [← Nat.sub_add_comm (by linarith), ← mul_two]
  apply le_trans (Nat.sub_le_sub_right (Nat.div_mul_le_self _ _) 1) (le_refl _)

lemma sub_lt_succ_half_of_lt (x : ℕ)(hn: Odd n)(h': x < n)(hx : (n + 1) / 2 ≤ x)
    : n - x < (n + 1) / 2 := by
  unfold Odd at hn
  cases' hn with r hr
  rw [hr] at hx ⊢
  ring_nf at *
  simp at *
  apply Nat.sub_lt_right_of_lt_add (by linarith) (by linarith)

lemma le_of_lt_succ_half {n x : ℕ}(h : x < (n + 1) / 2) : x ≤ n := by
  have : (n + 1) / 2 ≤ (n + 1) := Nat.div_le_self (n + 1) 2
  linarith

lemma nat_sub_eq {a₁ a₂: ℕ} (a: n - a₁ = n - a₂)
    (h4: a₁ ≤ n) (h5: a₂ ≤ n) : a₁ = a₂ := by
  apply @Nat.add_left_cancel n
  apply Nat.eq_add_of_sub_eq (le_add_right h5)
  rw [← tsub_add_eq_add_tsub h5]
  exact (eq_tsub_iff_add_eq_of_le h4).mp a.symm

-- key lemma using binomial symmetry: choose n i = choose n (n - i)
lemma binom_bij (g : (n+1) / 2 ≤ n) : ∀ i ∈ Ico 1 ((n + 1) / 2), choose n i
    = choose n (n - i) := by
  intro i hi
  obtain ⟨_ , h2⟩ := mem_Ico.mp hi
  rw [choose_symm]
  linarith

-- end of lemmas needed for binom_symm_bij

-- essentially proving ∑ i Ico 1 ((n + 1) / 2), choose n i
--                   = ∑ i Ico ((n + 1) / 2) n, choose n i
theorem binom_symm_bij (n : ℕ) (h : 1 < n)(hn : Odd n) :
    ∑ i in Ico 1 ((n + 1) / 2), Nat.choose n i
    + ∑ i in Ico ((n + 1) / 2) n, Nat.choose n i
    = 2 * ∑ k in Ico 1 ((n + 1) / 2), Nat.choose n k := by
  have h': ∑ i in Ico 1 ((n + 1) / 2), Nat.choose n i
  = ∑ i in Ico ((n + 1) / 2) n, Nat.choose n i := by
    apply sum_bij (fun x _ => n - x)
    · simp_rw [mem_Ico]
      rintro x ⟨h1, h2⟩
      constructor
      · suffices : x ≤ n
        · exact half_succ_le_sub_of_ge_one n x h1 this h2
        · exact le_of_lt_succ_half h2
      · exact tsub_lt_self (by linarith) h1
    · exact binom_bij _ (Nat.div_le_of_le_mul (by linarith))
    · simp_rw [mem_Ico]
      rintro x y ⟨_ , hx2⟩ ⟨_ , hy2⟩ hxy
      exact nat_sub_eq n hxy (le_of_lt_succ_half hx2) (le_of_lt_succ_half hy2)
    · simp only [ge_iff_le, mem_Ico, exists_prop, and_imp]
      intro x hx h'
      use n - x
      repeat constructor
      · exact le_tsub_of_add_le_left h'
      · exact sub_lt_succ_half_of_lt n x hn h' hx
      · exact (Nat.sub_sub_self (by linarith)).symm
  rw [h', two_mul]
  done

lemma binom_symm (h: 1 < n) (hn: Odd n) :
    ∑ k in Ico 1 n, choose n k = 2 * ∑ k in half_n_set n, choose n k := by
  unfold half_n_set
  rw [← sum_Ico_consecutive _ _ _]
  · rw [binom_symm_bij n h hn]
  · apply (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
  · exact Nat.div_le_of_le_mul (by linarith)

lemma binom_symm_2 (h: 1 < n) (hn: Odd n) :
    ∑ k in half_n_set n, choose n k = (∑ k in Ico 1 n, choose n k) / 2 := by
  rw [Nat.div_eq_of_eq_mul_right (by norm_num) (binom_symm _ h hn)]

lemma pow_2_div_2: (2^n - 2) / 2 = 2^(n - 1) - 1 := by
  rw [Nat.div_eq_of_eq_mul_right (by norm_num) _]
  cases' n with d <;> simp
  rw [Nat.pow_succ', Nat.mul_sub_left_distrib]

theorem sum_equals_pow2 (h: 1 < n) (hn: Odd n)
    : ∑ k in half_n_set n, choose n k = 2^(n-1)-1 := by
  rw [binom_symm_2 n h hn, sum_div2 n h, pow_2_div_2 n]

-- the next aim is to show that 2^(n-1)-1 is always odd for 1 < n.

lemma pow_prop1 (m: ℕ) (h: 0 < m) : 2^m = 2^(m - 1) * 2 := by
  cases' m with d
  · contradiction
  · simp [Nat.pow_succ', mul_comm]

lemma pow_prop2 (m: ℕ) (h: 1 < m) : 2^(m - 1) = 2^(m - 2) * 2 := by
  exact pow_prop1 (m - 1) (Nat.sub_pos_of_lt h)

lemma nat_sub (k : ℕ) (h₁ : k > 1) :
  k - 1 = k - 2 + 1 := by
  cases' k with d
  · contradiction
  · simp ; exact Nat.eq_add_of_sub_eq (by linarith) rfl

-- 2^(n-1)-1 is always odd for 1 < n
lemma power_odd (h: 1 < n): Odd (2^(n - 1) - 1) := by
  use 2^(n - 2) - 1
  rw [pow_prop2 n h, Nat.mul_sub_left_distrib, mul_comm]
  rw [nat_sub _ (by linarith [one_le_two_pow (n - 2)]), mul_one]

-- sum of the elements in the given sequence is odd
lemma sum_odd (h: 1 < n)(hn: Odd n): Odd (∑ k in half_n_set n, choose n k) := by
  rw [sum_equals_pow2 n h hn] ; exact power_odd n h

-- next aim is to prove the odd_number_of_odd_numbers theorem

-- summing elements of a set = summing the odd and not odd elements of the set
lemma odd_filter (s : Finset ℕ) :
    ∑ k in s, k = ∑ k in (s.filter Odd), k
    +  ∑ k in (s.filter (¬ Odd ·)), k := by
  exact (sum_filter_add_sum_filter_not s _ _).symm

-- sum of several even numbers is always even
def even_sum_finset (X: Finset ℕ) : Prop :=
  (∀ x ∈ X, Even x) → Even (∑ k in X, k)

lemma even_sum (X : Finset ℕ): even_sum_finset X := by
  have empty : even_sum_finset ∅ := by
    simp only [even_sum_finset]
  refine @Finset.induction ℕ even_sum_finset _ empty ?_ _
  intro a X' h g
  unfold even_sum_finset at *
  rw [sum_insert h, even_add]
  simp_all only [mem_insert, or_true, implies_true]

-- the sum of the even elements in a finset is even
lemma filter_even_sum (s : Finset ℕ):
    Even (∑ k in filter (¬ Odd ·) s, k) := by
  apply even_sum (filter (¬ Odd ·) s) ; simp

-- sum of elements in set is odd --> set contains an odd number of odd numbers
theorem odd_number_of_odd_numbers (s : Finset ℕ) (h : Odd (∑ k in s, k)):
    Odd (card <| s.filter Odd) := by
  contrapose h
  rw [odd_iff_not_even, not_not, odd_filter]
  apply Even.add _ (filter_even_sum s)
  simp only [odd_iff_not_even, not_not] at h
  rw [even_iff_not_odd, Iff.not (sum_odd_odd (filter Odd s) _)]
  · exact even_iff_not_odd.mp h
  · exact fun x hx => (mem_filter.mp hx).2

-- several simple lemmas needed to prove binom_sum_range_shift

lemma le_half_double_iff_lt_succ (n r : ℕ) : n ≤ (1 + r * 2) / 2 ↔ n < r + 1 := by
  constructor <;> intro h
  · contrapose! h
    exact Nat.div_lt_of_lt_mul (by linarith)
  · rw [Nat.le_div_iff_mul_le' (by linarith)]
    linarith

lemma icc_ico (n : ℕ) (h: Odd n) : Finset.Icc 1 (n / 2)
    = Finset.Ico 1 ((n + 1) / 2) := by
  unfold Odd at h
  cases' h with r hr
  rw [hr, add_assoc, one_add_one_eq_two, add_comm, mul_comm]
  ext x ; simp [mem_Icc, mem_Ico, le_half_double_iff_lt_succ]

-- proof of following lemma uses injectivity of choose function on Icc 1 (n / 2)
lemma binom_sum_range {n : ℕ} :
    ∑ k in image (fun x => Nat.choose n x) (Icc 1 (n / 2)), k
    = ∑ k in Icc 1 (n / 2), Nat.choose n k := by
  rw [sum_image]
  apply StrictMonoOn.injOn
  simp only [mem_val, Finset.mem_Icc]
  apply strictMono_s_of_lt_succ
  exact (fun k hk ↦ choose_lt_succ_of_le_half_left (Set.mem_Ico.mp hk).right)

-- lemma needed to convert previos results to the problem statement
theorem binom_sum_range_shift {n : ℕ} (h: Odd n) :
    ∑ k in binomial_set n, k = ∑ k in half_n_set n, Nat.choose n k := by
      unfold binomial_set half_n_set
      exact icc_ico n h ▸ binom_sum_range

end useful_lemmas

--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

-- Definitional Reminder
-- def half_n_set : Finset ℕ := Ico 1 (Nat.div (n+1) 2)

theorem intro3 {n : ℕ} (h : Odd n) (h': 1 < n) :
    Odd <| card <| (binomial_set n).filter Odd := by
  have h1 : Odd (∑ k in half_n_set n, Nat.choose n k) := sum_odd n h' h
  apply odd_number_of_odd_numbers (binomial_set n) _
  rwa [← binom_sum_range_shift h] at h1
  done
