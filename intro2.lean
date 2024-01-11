import Mathlib.Tactic

/-!
# Intro 2 (p.2)

The student lockers at Olympic High are numbered consecutively beginning with
locker number 1. The plastic digits used to number the lockers cost two cents
apiece, e.g. it costs 2 cents to label locker numbers 1-9, 4 cents to label
locker numbers 10-99, 6 cents to label locker numbers 100-999, etc.
If it costs 137.94 to label all the lockers, how many lockers are there at the
school?

## Solution Sketch

case analysis/decide go brrr

-/

open Nat Finset BigOperators

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup

def digit_count (N : ℕ) : ℕ := log 10 N + 1

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas



@[simp]
lemma not_or_left {p q : Prop} (h : p ∨ q) (g : ¬p) : q := by tauto

@[simp]
lemma not_or_right {p q : Prop} (h : p ∨ q) (g : ¬q) : p := by tauto

lemma neq_leq {a b : ℕ} (h : a ≤ b+1) (h' : a ≠ b+1) : a ≤ b := by
  rw [le_iff_lt_or_eq] at h
  have _ : a < b + 1 := by simp_all only [or_false]
  linarith
  done

lemma neq_leq' {a b : ℕ} : (a ≤ b+1 ∧ a ≠ b+1) ↔ a ≤ b := by
  constructor <;> intro h
  . exact neq_leq h.1 h.2
  . constructor <;> linarith
  done

lemma neq_leq_rev {a b : ℕ} (h : a ≤ b) (h' : a ≠ b) : a+1 ≤ b := by
  rw [le_iff_lt_or_eq] at h
  have _ : a < b := by simp_all only [or_false]
  linarith
  done

lemma neq_leq'_rev {a b : ℕ} : (a ≤ b ∧ a ≠ b) ↔ a+1 ≤ b := by
  constructor <;> intro h
  . exact neq_leq_rev h.1 h.2
  . constructor <;> linarith
  done

lemma lt_to_leq {a b : ℕ} : a < b+1 ↔ a ≤ b := by
  constructor <;> (intro h; linarith)
  done

lemma lt_to_leq_rev {a b : ℕ} : a < b ↔ a+1 ≤ b := by
  constructor <;> (intro h; linarith)
  done

lemma leq_or_eq {a b : ℕ} (h : a ≤ b ∨ a = b+1): a ≤ b + 1 := by
  rw [le_iff_lt_or_eq]
  by_cases h' : a = b+1
  . exact Or.inr h'
  . have g : a ≤ b := by
      simp_all only [or_false]
      done
    rw [lt_to_leq]
    exact Or.inl g
  done

lemma Icc_union_singleton (a b : ℕ) {h₁ : a ≤ b} : Icc a (b+1) = Icc a b ∪ {b+1} := by
  ext x
  rw [mem_union, mem_Icc, mem_Icc]
  by_cases h : x = b+1
  . rw [← h]
    constructor <;> intro _
    . simp only [mem_singleton, or_true]
    . simp only [le_refl, and_true]
      linarith
  . constructor <;> intro h'
    . let ⟨g,g'⟩ := h'
      exact Or.inl ⟨g, neq_leq g' h⟩
    . rw [mem_singleton] at h'
      have h'' : a ≤ x ∧ x ≤ b := by
        exact not_or_right h' h
        done
      rw [@le_iff_lt_or_eq _ _ x (b+1)]
      constructor
      . exact h''.1
      . rw [lt_to_leq]
        exact Or.inl h''.2
  done

lemma singleton_union_Icc (a b : ℕ) {h₁ : a ≤ b} : Icc a b = {a} ∪ Icc (a+1) b := by
  ext x
  rw [mem_union, mem_Icc, mem_Icc]
  by_cases h : x = a
  . rw [← h]
    constructor <;> intro _
    . simp_all only [le_refl, mem_singleton, add_le_iff_nonpos_right]
    . simp_all only [mem_singleton, or_true, le_refl, and_self]
  . constructor <;> intro h'
    . let ⟨g,g'⟩ := h'
      exact Or.inr ⟨neq_leq_rev g (Ne.symm h), g'⟩
    . rw [mem_singleton] at h'
      have h'' : a + 1 ≤ x ∧ x ≤ b := by
        exact not_or_left h' h
        done
      rw [@le_iff_lt_or_eq _ _ a x]
      constructor
      . rw [lt_to_leq_rev]
        exact Or.inl h''.1
      . exact h''.2
  done

theorem Icc_endpoint_union (a b c : ℕ) {h₁ : a ≤ b} {h₂ : b ≤ c}
  : Icc a b ∪ Icc b c = Icc a b ∪ Icc (b+1) c := by
  ext x
  simp only [mem_union, mem_Icc]
  by_cases hb : x = b
  . simp_all only [le_refl, add_le_iff_nonpos_right]
  . repeat rw [← neq_leq'_rev]
    tauto
  done

theorem split_Icc (a b c : ℕ) {h₁ : a ≤ b} {h₂ : b ≤ c} : Icc a c = Icc a b ∪ Icc b c := by
  apply_fun Finset.toSet
  . rw [coe_union]
    repeat rw [coe_Icc]
    exact (Set.Icc_union_Icc_eq_Icc h₁ h₂).symm
  . exact coe_injective
  done

lemma split : Icc 1 2001 = Icc 1 9 ∪ Icc 10 99 ∪ Icc 100 999 ∪ Icc 1000 2001 := by
  rw [← Icc_endpoint_union 1 9 99, ← split_Icc]
  rw [← Icc_endpoint_union 1 99 999, ← split_Icc]
  rw [← Icc_endpoint_union 1 999 2001, ← split_Icc]
  repeat trivial
  done

lemma divIcc {a b d n : ℕ} (hn : n ∈ Icc a b) : (n/d) ∈ Icc (a/d) (b/d) := by
  rw [mem_Icc] at *
  exact ⟨Nat.div_le_div_right hn.1, Nat.div_le_div_right hn.2⟩
  done

lemma div_ineq {a b : ℕ} (c : ℕ) (h₀ : c ≠ 0) : a ≤ b → a/c ≤ b/c := by
  intro h
  exact Nat.div_le_div h (by trivial) h₀
  done

theorem count_1 (x : ℕ) (h : x ∈ Icc 1 9) : digit_count x = 1 := by
  fin_cases h
  repeat trivial
  done

theorem count_2 (x : ℕ) (h : x ∈ Icc 10 99) : digit_count x = 2 := by
  cases' x with n
  . contradiction
  . unfold digit_count
    rw [log_of_one_lt_of_le]
    repeat rw [succ.injEq]
    . simp only [log_eq_zero_iff, or_false]
      have h' : (succ n / 10) ∈ Icc (10/10) (99/10) := by
        exact divIcc h
        done
      ring_nf at h'
      simp only [mem_Icc] at h'
      exact lt_to_leq.mpr h'.2
    . trivial
    . rw [mem_Icc] at h
      exact h.1
  done

theorem count_3 (x : ℕ) (h : x ∈ Icc 100 999) : digit_count x = 3 := by
  cases' x with n
  . simp only [mem_Icc] at h -- contradiction doesn't work here for some reason???
  . unfold digit_count
    rw [log_of_one_lt_of_le, log_of_one_lt_of_le]
    repeat rw [succ.injEq]
    . simp only [log_eq_zero_iff, or_false]
      have h' : (succ n / 10 / 10) ∈ Icc (100/ 10 / 10) (999/10/10) := by
        exact divIcc $ divIcc h
        done
      simp only [mem_Icc] at h'
      ring_nf at h'
      exact lt_to_leq.mpr h'.2
    . trivial
    . rw [mem_Icc] at h
      let ⟨g,_⟩ := h
      exact div_ineq 10 (by trivial) g
    . trivial
    . rw [mem_Icc] at h
      linarith
  done

theorem count_4 (x : ℕ) (h : x ∈ Icc 1000 2001) : digit_count x = 4 := by
  cases' x with n
  . simp only [mem_Icc] at h -- contradiction doesn't work here for some reason???
  . unfold digit_count
    rw [log_of_one_lt_of_le, log_of_one_lt_of_le, log_of_one_lt_of_le]
    repeat rw [succ.injEq]
    . simp only [log_eq_zero_iff, or_false]
      have h' : (succ n/10/10/10) ∈ Icc (1000/10/10/10) (2001/10/10/10) := by
        exact divIcc (divIcc (divIcc h))
        done
      simp only [mem_Icc] at h'
      ring_nf at h'
      apply lt_to_leq.mpr _
      linarith
    . trivial
    . rw [mem_Icc] at h
      let ⟨g,_⟩ := h
      have g' : 1000/10 ≤ succ n/10 := by
        exact div_ineq 10 (by trivial) g
      exact div_ineq 10 (by trivial) g'
    . trivial
    . rw [mem_Icc] at h
      have g' : 1000/10 ≤ succ n/10 := by
        exact div_ineq 10 (by trivial) h.1
      ring_nf at g'
      linarith
    . trivial
    . rw [mem_Icc] at h
      linarith
  done

theorem sum_1 : ∑ x in Icc 1 9, digit_count x = ∑ x in Icc 1 9, 1 :=
  Finset.sum_congr (by rfl) count_1

theorem sum_2 : ∑ x in Icc 10 99, digit_count x = ∑ x in Icc 10 99, 2 :=
  Finset.sum_congr (by rfl) count_2

theorem sum_3 : ∑ x in Icc 100 999, digit_count x = ∑ x in Icc 100 999, 3 :=
  Finset.sum_congr (by rfl) count_3

theorem sum_4 : ∑ x in Icc 1000 2001, digit_count x = ∑ x in Icc 1000 2001, 4 :=
  Finset.sum_congr (by rfl) count_4

lemma disj_Icc (a b c d : ℕ) {h: b < c} : Disjoint (Icc a b) (Icc c d) := by
  rw [disjoint_iff_inter_eq_empty]
  ext x
  simp_rw [mem_inter, mem_Icc]
  constructor <;> intro h'
  . linarith
  . simp_all only [not_mem_empty]
  done

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro1 : ∑ x in Icc 1 2001, 2 * digit_count x = 13794 := by
  rw [← @Finset.mul_sum _ _ _ 2 digit_count]
  rw [split]
  repeat rw [sum_union]
  . rw [sum_1, sum_2, sum_3, sum_4]
    simp_rw [Finset.sum_const, card_Icc]
  . exact @disj_Icc _ _ _ _ (by linarith)
  . rw [← Icc_endpoint_union _ _ _, ← split_Icc]
    exact @disj_Icc _ _ _ _ (by linarith)
    all_goals trivial
  . rw [← Icc_endpoint_union _ _ _, ← split_Icc]
    rw [← Icc_endpoint_union _ _ _, ← split_Icc]
    exact @disj_Icc _ _ _ _ (by linarith)
    all_goals trivial
  done
