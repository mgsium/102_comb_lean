import Mathlib.Tactic

/-!
# Advanced 36 (p.99) | [USAMO 1997 Submission]

A finite set of (distinct) positive integers is called a DS-set if each of the
integers divides the sum of them all. Prove that every set of positive integers
is a subset of some DS-set.

## Solution



-/

open Finset Nat BigOperators

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup

def DS_set (S : Finset ℕ) : Prop := 0 ∉ S ∧ ∀s ∈ S, s ∣ S.sum id

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

lemma lt_to_leq {a b : ℕ} : a < b ↔ a + 1 ≤ b := by
  constructor <;> intro h <;> linarith

lemma ne_zero_iff_gt_zero (x : ℕ) : x ≠ 0 ↔ 0 < x := by
  simp_all only [ne_eq, gt_iff_lt]
  constructor <;> intro h
  · by_cases h : x>0
    . exact h
    . simp_all only [gt_iff_lt, not_lt, nonpos_iff_eq_zero]
  · by_contra
    simp_all
  done

lemma inIcc (S : Finset ℕ) (hz : 0 ∉ S) (he : Finset.Nonempty S)
    : S ⊆ Icc 1 (max' S he) := by
  intro x h
  simp_all only [gt_iff_lt, max'_lt_iff, lt_one_iff, mem_Icc]
  constructor
  . have g : x ≠ 0 := by
      by_contra a
      rw [a] at h
      contradiction
    rw [← lt_to_leq]
    exact (ne_zero_iff_gt_zero x).mp g
  . unfold max'
    simp_all only [id_eq, le_sup'_iff]
    apply Exists.intro
    apply And.intro
    exact h
    simp_all only [le_refl]
  done

-- @[aesop 1% unsafe apply] def pog {A} : A := sorry

lemma neq_leq {a b : ℕ} : (a ≤ b + 1 ∧ a ≠ b + 1) ↔ a ≤ b := by
  constructor <;> intro h
  . rw [le_iff_lt_or_eq]
    exact lt_succ_iff_lt_or_eq.mp <| Nat.lt_iff_le_and_ne.mpr h
  . constructor <;> linarith
  done

lemma neq_leq_rev {a b : ℕ} : (a ≤ b ∧ a ≠ b) ↔ a + 1 ≤ b := by
  rw [← Nat.add_le_add_iff_right, ← succ_ne_succ]
  exact neq_leq

lemma split_Icc (a b c : ℕ) {h₁ : a ≤ b} {h₂ : b ≤ c}
    : Icc a c = Icc a b ∪ Icc b c := by
  apply_fun Finset.toSet
  . rw [coe_union]
    repeat rw [coe_Icc]
    exact (Set.Icc_union_Icc_eq_Icc h₁ h₂).symm
  . exact coe_injective
  done

lemma Icc_endpoint_union {a b c : ℕ} {h₁ : a ≤ b} {h₂ : b ≤ c}
    : Icc a b ∪ Icc b c = Icc a b ∪ Icc (b + 1) c := by
  ext x
  simp only [mem_union, mem_Icc]
  by_cases hb : x = b
  . simp_all only [le_refl, add_le_iff_nonpos_right]
  . rw [← neq_leq_rev]; tauto
  done

lemma disj_Icc {a b c d : ℕ} (h: b < c) : Disjoint (Icc a b) (Icc c d) := by
  rw [disjoint_iff_inter_eq_empty]
  ext x
  simp_rw [mem_inter, mem_Icc]
  constructor <;> intro h'
  . linarith
  . simp_all only [not_mem_empty]
  done



lemma absorb (a b : ℕ) : a + (b * a) = (b + 1) * a := by
  nth_rw 1 [← one_mul a]
  rw [add_comm, ← add_mul b 1 a]
  done

lemma Icc_sum (n : ℕ) : (Icc 1 n).sum id = (n * (n + 1))/2 := by
  induction' n with d hd
  . trivial
  . simp_all only [gt_iff_lt, lt_one_iff, id_eq, succ_eq_add_one]
    rw [split_Icc 1 d (succ d), Icc_endpoint_union,
        sum_union (disj_Icc (by linarith)), hd, add_comm]
    simp only [Icc_self, sum_singleton]
    nth_rw 1 [← @mul_div_right (d+1) 2]
    ring_nf
    sorry
  done

lemma range_eq_Icc (n : ℕ) : range (n + 1) \ {0} = Icc 1 n := by
  ext x
  simp only [mem_sdiff, mem_range, mem_singleton, mem_Icc]
  rw [lt_succ, one_le_iff_ne_zero, And.comm]
  done

-- lemma reeee (n : ℕ) (S : Finset ℕ) {h : n > 2} (i : ℕ)
--     : S = Icc 1 n Finset.disjiUnion (Icc 2 $ n-1) (singleton (∏ j in (Icc i (n - 1)), (n - j)))
--     := by
--   sorry
--   done

lemma zero_subset_range (n : ℕ) (h : 0 < n) : {0} ⊆ range (n + 1) := by
  rw [singleton_subset_iff, mem_range]
  linarith
  done

lemma sum_zero : ∑ x in {0}, x = 0 := by exact rfl

variable (S : Finset ℤ)

lemma (n : ℕ)

def mySet (n : ℕ) : Finset ℕ :=
  Icc 1 n ∪ Finset.biUnion (Icc 2 $ n-1)
    (fun j => singleton ((n - j) * (n + 1) * ∏ i in (Icc 0 $ j - 2), (n - i)))

lemma split_prod_Icc (n : ℕ) : ∏ i in Icc 0 (n + 1)

lemma rw_prod (n j : ℕ) (hj : 1 < j) (hn : j < n) : (n - j) * (n + 1) * ∏ i in Icc 0 (j - 2), (n - i)
    = ((n + 1) * ∏ i in Icc 0 (j - 1), (n - i)) - ((n + 1) * ∏ i in Icc 0 (j - 2), (n - i)) := by

  done

lemma sum_set (n : ℕ) (h : 0 < n) : Finset.sum (mySet n) id = (n + 1)! := by
  unfold mySet
  simp only [id_eq]
  rw [sum_union, ← range_eq_Icc n, ← add_zero (∑ x in _, x)]
  nth_rw 2 [← sum_zero]
  rw [sum_sdiff (zero_subset_range n h), sum_range_id (n+1)]
  norm_num

  done

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem adv36 (X : Finset ℕ) : ∃(S : Finset ℕ), DS_set S ∧ X ⊆ S:= by
  sorry
  done
