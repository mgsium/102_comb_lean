import Mathlib.Tactic

/-!
# Intro 3 (pp. 18) | [Revista Matematica Timişoara]
Let n be an odd integer greater than 1. Prove that the sequence
[(n choose 1) ,..., (n choose (n-1)/2)] contains an odd number of odd numbers.

## Solution
The sum of the numbers in the given sequence equals 2^(n-1)-1, which is odd;
 hence, the result follows.
-/

open Nat BigOperators Finset

variable (n : ℕ)

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

def my_set : Finset ℕ := Ico 1 ((n+1) / 2)

-- preliminary lemmas needed for binom_symm_bij

lemma ineq1 (x : ℕ) (h1 : 1 ≤ x) (h2: x ≤ n) (h3 : x < (n + 1) / 2) :
    (n + 1) / 2 ≤ n - x := by
  rw [le_tsub_iff_left h2]
  have h := (lt_iff_le_pred (by linarith)).mp h3
  apply le_trans (Nat.add_le_add_right h _)
  rw [←Nat.sub_add_comm (by linarith), ←mul_two]
  apply le_trans (Nat.sub_le_sub_right (Nat.div_mul_le_self _ _) 1) (le_refl _)

lemma ineq2 (x : ℕ)(hn: Odd n)(h': x < n)(hx : (n + 1) / 2 ≤ x)
    : n - x < (n + 1) / 2 := by
  unfold Odd at hn
  cases' hn with r hr
  rw [hr] at hx ⊢
  ring_nf at *
  simp [add_comm, succ_eq_add_one] at *
  apply Nat.sub_lt_right_of_lt_add (by linarith) (by linarith)

lemma ineq3 {n a₁ : ℕ}(right : a₁ < (n + 1) / 2) : a₁ ≤ n := by
  have : (n + 1) / 2 ≤ (n + 1) := Nat.div_le_self (n + 1) 2
  linarith

lemma nat_sub_eq {a₁ a₂: ℕ} (a: n - a₁ = n - a₂)
    (h4: a₁ ≤ n) (h5: a₂ ≤ n) : a₁ = a₂ := by
  apply @Nat.add_left_cancel n
  apply Nat.eq_add_of_sub_eq (le_add_right h5)
  rw [← tsub_add_eq_add_tsub h5]
  exact (eq_tsub_iff_add_eq_of_le h4).mp a.symm

-- end of preliminary lemmas

theorem binom_symm_bij (n : ℕ) (h : 1 < n)(hn : Odd n) :
    ∑ i in Ico 1 ((n + 1) / 2), Nat.choose n i
    + ∑ i in Ico ((n + 1) / 2) n, Nat.choose n i
    = 2 * ∑ k in Ico 1 ((n + 1) / 2), Nat.choose n k := by
  have h₂ (g : (n+1) / 2 ≤ n) : ∀ i ∈ Ico 1 ((n + 1) / 2), choose n i
  = choose n (n - i) := by
    intro i hi
    obtain ⟨_ , h2⟩ := mem_Ico.mp hi
    rw [choose_symm]
    linarith
  have h': ∑ i in Ico 1 ((n + 1) / 2), Nat.choose n i
  = ∑ i in Ico ((n + 1) / 2) n, Nat.choose n i := by
    apply sum_bij (fun x _ => n - x)
    · intro x hx
      rw [mem_Ico] at *
      rcases hx with ⟨h1, h2⟩
      constructor
      · suffices : x ≤ n
        · exact ineq1 n x h1 this h2
        · exact ineq3 h2
      · refine tsub_lt_self (by linarith) h1
    · apply h₂
      apply Nat.div_le_of_le_mul (by linarith)
    · intro x y hx hy hxy
      rw [mem_Ico] at hx hy
      rcases hx with ⟨_ , hx2⟩
      rcases hy with ⟨_ , hy2⟩
      exact nat_sub_eq n hxy (ineq3 hx2) (ineq3 hy2)
    · simp only [ge_iff_le, mem_Ico, exists_prop, and_imp]
      intro x hx h'
      use n-x
      constructor
      · constructor
        · exact le_tsub_of_add_le_left h'
        · exact ineq2 n x hn h' hx
      · symm
        apply Nat.sub_sub_self (by linarith)
  rw [h']
  ring

lemma binom_symm (h: 1 < n)(hn: Odd n): ∑ k in Ico 1 n, choose n k
    = 2 * ∑ k in my_set n, choose n k := by
  unfold my_set
  have g : (n+1) / 2 ≤ n := by
    apply Nat.div_le_of_le_mul (by linarith)
  rw [← sum_Ico_consecutive _ _ g]
  · rw [binom_symm_bij n h hn]
  · refine (Nat.le_div_iff_mul_le ?k0).mpr (by linarith)
    norm_num

lemma binom_symm_2 (h: 1 < n)(hn: Odd n): ∑ k in my_set n, choose n k
    = (∑ k in Ico 1 n, choose n k) / 2 := by
  rw [Nat.div_eq_of_eq_mul_right (by norm_num) (binom_symm _ h hn)]

lemma pow_2_div_2: (2^n-2) / 2 = 2^(n-1)-1 := by
  have h: 2^n-2 = 2 * (2^(n-1)-1) := by
    cases' n with d <;>
      simp
    rw [Nat.pow_succ', Nat.mul_sub_left_distrib]
  rw [Nat.div_eq_of_eq_mul_right (by norm_num) h]

theorem sum_equals_pow2 (h: 1 < n)(hn: Odd n)
    : ∑ k in my_set n, choose n k = 2^(n-1)-1 := by
  rw [binom_symm_2 n h hn, sum_div2 n h, pow_2_div_2 n]

-- we prove that 2^(n-1)-1 is always odd for n > 1.

lemma pow_prop1 (m: ℕ)(h: 0 < m) : 2^m = 2^(m-1) * 2 := by
  cases' m with d
  · contradiction
  · simp
    rw [Nat.pow_succ', mul_comm]

lemma pow_prop2 (m: ℕ) (h: 1 < m) : 2^(m-1) = 2^(m-2) * 2 := by
  cases' m with d
  · contradiction
  · simp
    exact pow_prop1 d (by linarith)

lemma nat_sub (k : ℕ) (h₁ : k > 1) :
  k - 1 = k - 2 + 1 := by
  cases' k with d
  · contradiction
  · simp
    exact Nat.eq_add_of_sub_eq (by linarith) rfl

lemma power_odd (h: 1 < n): Odd (2^(n-1) - 1) := by
  use 2^(n-2)-1
  have h₂ : 1 ≤ 2^(n-2) := one_le_two_pow (n - 2)
  have h₁ : 1 < 2 * 2 ^ (n - 2) := by linarith
  rw [pow_prop2 n h, Nat.mul_sub_left_distrib, mul_comm]
  norm_num
  rw [nat_sub _ h₁]

lemma sum_odd (h: 1 < n)(hn: Odd n): Odd (∑ k in my_set n, choose n k) := by
  rw [sum_equals_pow2 n h hn]
  exact power_odd n h

-- if the sum of the elements of a finset is odd,
-- then the finset contains an odd number of odd numbers.

lemma odd_filter (s : Finset ℕ) :
    ∑ k in s, k = ∑ k in (s.filter Odd), k
    +  ∑ k in (s.filter (¬ Odd ·)), k := by
  exact (sum_filter_add_sum_filter_not s _ _).symm

def even_sum_finset (X: Finset ℕ) : Prop :=
  (∀ x ∈ X, Even x) → Even (∑ k in X, k)

lemma even_sum (X : Finset ℕ): even_sum_finset X := by
  have empty : even_sum_finset ∅ := by
    simp only [even_sum_finset]
  refine @Finset.induction ℕ even_sum_finset _ empty ?_ X
  intro a X' h g
  unfold even_sum_finset at *
  rw [sum_insert h, even_add]
  simp_all only [mem_insert, or_true, implies_true]

lemma one_leq_odd (x : ℕ) (h' : Odd x) : 1 ≤ x := by
    unfold Odd at h'
    cases' h' with r hr
    linarith

lemma sum_minus (X : Finset ℕ) (h: ∀ x ∈ X, x ≥ 1) :
    ∑ x in X, (x - 1) = ∑ x in X, x - ∑ x in X, 1 := by
  rw [eq_tsub_iff_add_eq_of_le (sum_le_sum h)]
  · rw [←sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    exact Nat.sub_add_cancel (h x hx)

lemma sum_odds (X : Finset ℕ) (h: Even X.card) (h': ∀ x ∈ X, Odd x)
    : Even (∑ k in X, k) := by
  unfold Even at *
  simp_rw [←mul_two]
  cases' h with r hr
  use ((∑ k in X, (k-1) / 2) + r)
  rw [right_distrib, sum_mul]
  have h'': ∀ (x : ℕ), x ∈ X → x ≥ 1 := by
    intros x hx
    specialize h' x hx
    exact one_leq_odd x h'
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
    exact Nat.div_mul_cancel h₁
  rw [h, sum_minus X h'', ← card_eq_sum_ones X, hr, ← two_mul, mul_comm]
  apply Nat.eq_add_of_sub_eq _ rfl
  rw [← two_mul, mul_comm] at hr
  rw [← hr, card_eq_sum_ones X]
  exact sum_le_sum h''

lemma filter_odd_sum (s : Finset ℕ) (h: ¬Odd (card <| filter Odd s)):
    Even (∑ k in (s.filter Odd), k) := by
  rw [even_iff_not_odd.symm] at h
  let odd_set := filter Odd s
  have h' : ∀ x ∈ odd_set, Odd x := by
    intros x hx
    simp at hx
    obtain ⟨_,h2⟩ := hx
    rw [odd_iff_not_even]
    exact h2
  apply (sum_odds odd_set h h')

lemma filter_even_sum (s : Finset ℕ):
    Even (∑ k in filter (¬ Odd ·) s, k) := by
  let even_set := filter (¬ Odd ·) s
  have h : ∀ x ∈ even_set, Even x := by
    intros x hx
    simp at hx
    exact hx.2
  apply (even_sum even_set h)

theorem odd_number_of_odd_numbers (s : Finset ℕ) (h : Odd (∑ k in s, k)):
    Odd (card <| s.filter Odd) := by
  contrapose h
  rw [odd_iff_not_even, not_not, odd_filter]
  apply Even.add (filter_odd_sum s h) (filter_even_sum s)

-- we finally prove the main result

-- def my_set : Finset ℕ := Ico 1 (Nat.div (n+1) 2)

def binomial_set (n : ℕ) : Finset ℕ := (my_set n).image (Nat.choose n ·)

theorem intro3 {n : ℕ} (h : Odd n) (h': 1 < n) :
    Odd <| card <| (binomial_set n).filter Odd := by
  have h1 : Odd (∑ k in my_set n, Nat.choose n k) := by
    exact sum_odd n h' h
  have h2 : Odd (∑ k in image (fun x ↦ Nat.choose n x) (my_set n), k) := by
    unfold my_set at *
    sorry
  unfold binomial_set
  apply odd_number_of_odd_numbers (binomial_set n) h2
  done
