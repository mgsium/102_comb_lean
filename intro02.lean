import Mathlib.Tactic

/-!
# Intro 2 (pp.23-24) | [AHSME 1999]

The student lockers at Olympic High are numbered consecutively beginning with
locker number 1. The plastic digits used to number the lockers cost two cents
apiece, e.g. it costs 2 cents to label locker numbers 9; and 4 cents to label
locker numbers 10, etc. If it costs 137.94 to label all the lockers, how many
lockers are there at the school?

## Solution Sketch

We can split the sum of the digit counts over each order of magnitude; i.e.
lockers 1 to 9 cost 2 cents each; lockers 10-99 cost 4 cents; 100-999 cost 6
cents, etc., so a sum from 1 to n can be split into multiple constant sums,
which simplify into the sums of basic products.

-/

open Nat Finset BigOperators

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup

abbrev digit_count (N : ℕ) : ℕ := log 10 N + 1

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

lemma neq_leq {a b : ℕ} : (a ≤ b + 1 ∧ a ≠ b + 1) ↔ a ≤ b := by
  constructor <;> intro h
  . rw [le_iff_lt_or_eq]
    exact lt_succ_iff_lt_or_eq.mp <| Nat.lt_iff_le_and_ne.mpr h
  . constructor <;> linarith
  done

lemma neq_leq_rev {a b : ℕ} : (a ≤ b ∧ a ≠ b) ↔ a + 1 ≤ b := by
  rw [← Nat.add_le_add_iff_right 1 a b, ← succ_ne_succ]
  exact neq_leq

lemma lt_to_leq {a b : ℕ} : a < b + 1 ↔ a ≤ b := by
  constructor <;> intro h <;> linarith

lemma leq_or_eq {a b : ℕ} (h : a ≤ b ∨ a = b + 1) : a ≤ b + 1 := by
  rw [le_iff_lt_or_eq, lt_to_leq]; exact h

-- If a ≤ b, then a / c ≤ b / c for any non-zero c.
lemma div_ineq {a b : ℕ} (c : ℕ) (h₀ : c ≠ 0) : a ≤ b → a / c ≤ b / c :=
  fun h ↦ Nat.div_le_div h (by trivial) h₀

-- The interval [a,b]∪[b,c](=[a,c]) is equal to [a,b] ∪ [b+1,c] for any b ∈ [a,c].
lemma Icc_endpoint_union {a b c : ℕ} {h₁ : a ≤ b} {h₂ : b ≤ c}
    : Icc a b ∪ Icc b c = Icc a b ∪ Icc (b + 1) c := by
  ext x
  simp only [mem_union, mem_Icc]
  by_cases hb : x = b
  . simp_all only [le_refl, add_le_iff_nonpos_right]
  . rw [← neq_leq_rev]; tauto
  done

-- The interval [a,c] is equal to [a,b] ∪ [b,c] for any b ∈ [a,c].
lemma split_Icc (a b c : ℕ) {h₁ : a ≤ b} {h₂ : b ≤ c}
    : Icc a c = Icc a b ∪ Icc b c := by
  apply_fun Finset.toSet
  . rw [coe_union]
    repeat rw [coe_Icc]
    exact (Set.Icc_union_Icc_eq_Icc h₁ h₂).symm
  . exact coe_injective
  done

-- The interval [1,2001] is equal to [1,9] ∪ [10,99] ∪ [100,999] ∪ [1000,2001].
lemma split : Icc 1 2001 = Icc 1 9 ∪ Icc 10 99 ∪ Icc 100 999 ∪ Icc 1000 2001 := by
  simp [← Icc_endpoint_union, ← split_Icc]

-- If n ∈ [a,b], then n/d ∈ [a/d,b/d].
lemma div_Icc {a b d n : ℕ} (hn : n ∈ Icc a b) : (n / d) ∈ Icc (a / d) (b / d) := by
  rw [mem_Icc] at *
  exact ⟨Nat.div_le_div_right hn.1, Nat.div_le_div_right hn.2⟩

-- Numbers between 10ⁱ and 10ⁱ⁺¹ -1 have i + 1 digits
lemma count_i (x i : ℕ) (hi : 0 < i) (h : x ∈ Icc (10 ^ i) (10 ^ (i + 1) - 1))
  : digit_count x = i + 1 := by
  norm_num
  rw [mem_Icc, ← lt_iff_le_pred Fin.size_pos'] at h
  rw [Nat.log_eq_iff (Or.inl <| Nat.pos_iff_ne_zero.mp hi)]
  constructor <;> linarith

-- Numbers in [1,9], [10,99], [100,999], [1000,2001] have one, two, three, and
-- four digits, respectively.
lemma count_1 (x : ℕ) (h : x ∈ Icc 1 9) : digit_count x = 1 := by
  fin_cases h <;> trivial

lemma count_2 (x : ℕ) (h : x ∈ Icc 10 99) : digit_count x = 2 := by
  exact count_i x 1 (by norm_num) h

lemma count_3 (x : ℕ) (h : x ∈ Icc 100 999) : digit_count x = 3 := by
  exact count_i x 2 (by norm_num) h

lemma count_4 (x : ℕ) (h : x ∈ Icc 1000 2001) : digit_count x = 4 := by
  apply count_i x 3 (by norm_num) _
  norm_num at *
  constructor <;> linarith

-- Sums of digit counts can be replaced by constants over appropriate ranges.
lemma sum_1 : ∑ x in Icc 1 9, digit_count x = ∑ x in Icc 1 9, 1 :=
  Finset.sum_congr rfl count_1

lemma sum_2 : ∑ x in Icc 10 99, digit_count x = ∑ x in Icc 10 99, 2 :=
  Finset.sum_congr rfl count_2

lemma sum_3 : ∑ x in Icc 100 999, digit_count x = ∑ x in Icc 100 999, 3 :=
  Finset.sum_congr rfl count_3

lemma sum_4 : ∑ x in Icc 1000 2001, digit_count x = ∑ x in Icc 1000 2001, 4 :=
  Finset.sum_congr rfl count_4

-- The intervals [a,b] and [c,d] are disjoint if b < c.
lemma disj_Icc {a b c d : ℕ} (h: b < c) : Disjoint (Icc a b) (Icc c d) := by
  rw [disjoint_iff_inter_eq_empty]
  ext x
  simp_rw [mem_inter, mem_Icc]
  constructor <;> intro h'
  . linarith
  . simp_all only [not_mem_empty]
  done

-- digit_count n is positive for any n.
lemma digit_count_gt_zero (n : ℕ) : digit_count n > 0 := by
  norm_num [digit_count]

-- Sum of digit_count over [1,n] is less than the sum over [1,n+1].
lemma sum_step (n : ℕ) : ∑ x in Icc 1 n, 2 * digit_count x
    < ∑ x in Icc 1 (n+1), 2 * digit_count x := by
  by_cases h : n ≥ 1 <;> norm_num at h
  . rw [split_Icc 1 n (n + 1), Icc_endpoint_union, sum_union]
    . norm_num
    . exact disj_Icc (by linarith)
    all_goals linarith
  . rw [h]; trivial
  done

-- Sum of digit_count over [1,n] is less than the sum over [1,m] if n < m.
lemma sum_inc (n m : ℕ) : n < m → ∑ x in Icc 1 n, 2 * digit_count x
    < ∑ x in Icc 1 m, 2 * digit_count x := by
  induction' m with d hd <;> intro h
  . contradiction
  . by_cases h : n < d
    . linarith [hd h, sum_step d]
    . rw [(by linarith : n = d)]
      exact sum_step d
  done

-- The sum of digit_count over [1,2001] is 13794.
lemma digit_count_2001 : ∑ x in Icc 1 2001, 2 * digit_count x = 13794 := by
  rw [← @Finset.mul_sum _ _ _ _ digit_count, split]
  repeat rw [sum_union]
  . rw [sum_1, sum_2, sum_3, sum_4]
    simp_rw [Finset.sum_const, card_Icc]
  . exact Finset.sdiff_eq_self_iff_disjoint.mp (by rfl)
  repeat' simp_rw [← Icc_endpoint_union, ← split_Icc]
  all_goals exact disj_Icc (by linarith)
  done

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro2 (n : ℕ) : ∑ x in Icc 1 n, 2 * digit_count x = 13794 → n = 2001 := by
  intro h
  rw [← digit_count_2001] at h
  rcases (lt_trichotomy n 2001) with g | g | g
  . linarith [sum_inc n 2001 g]
  . exact g
  . linarith [sum_inc 2001 n g]
  done
