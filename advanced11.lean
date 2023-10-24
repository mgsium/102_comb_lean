import Mathlib.Tactic

open Set
open Finset
open Nat

-- x divides an odd number of elements of B
def odd_divides (x : ℕ) (B : Finset ℕ) : Bool :=
  card (B.filter (x ∣ ·)) % 2 ≠ 0

#eval (fun x B ↦ (filter (x ∣ ·) B).card % 2 ≠ 0) 2 { 1, 2, 3, 4 }
#eval odd_divides 2 { 1, 2, 3, 4 }

example : odd_divides 2 { 1, 2, 3 } := by
  simp [odd_divides]
  done

example (i k : ℕ) (h : i ≤ k) : i - 1 ≤ k := by
  { norm_num; exact Nat.le_step h }

def calc_Xᵢ (i : ℕ) (X : Finset ℕ) : Finset ℕ :=
  List.toFinset $ List.take i $ X.sort (· ≥ ·)

lemma eq_calc_zero (X : Finset ℕ) : calc_Xᵢ 0 X = {} := by
  simp [calc_Xᵢ]
  done

lemma list_take_subset (X : List ℕ) (k : ℕ)
  : List.take k X ⊆ List.take (k + 1) X := by
  intro x h
  rw [List.take_succ]
  simp only [List.mem_append, Option.mem_toList, Option.mem_def]
  constructor
  exact h
  done

lemma finset_subset (X Y: List ℕ) (h : X ⊆ Y)
  : X.toFinset ⊆ Y.toFinset := by
  intro x h2
  simp at h2 ⊢
  exact h h2
  done

lemma calc_X_inc (X : Finset ℕ) (i : ℕ)
  : calc_Xᵢ i X ⊆ calc_Xᵢ (Nat.succ i) X := by
  simp [calc_Xᵢ, list_take_subset, finset_subset]
  done

def calc_Aᵢ (i : ℕ) (X A : Finset ℕ) : Finset ℕ :=
  A ∩ calc_Xᵢ i X

def calc_Bᵢ (i : ℕ) (X A : Finset ℕ) : Finset ℕ := match i with
  | 0 => ∅
  | k + 1 =>
    if h : X.card < k + 1 then calc_Bᵢ X.card X A else
    let xₖ := (X.sort (· ≥ ·))[k]'(by simp at *; exact h)
    let Bₖ := calc_Bᵢ k X A
    let c := Or (And (xₖ ∈ A) (odd_divides xₖ Bₖ)) (And (xₖ ∉ A) ¬(odd_divides xₖ Bₖ))
    Bₖ ∪ (if (¬ c) then { xₖ } else ∅)

#eval calc_Xᵢ 3 { 1, 2, 3 }
#eval calc_Aᵢ 1 { 1, 2, 3 } { 1, 2 }
#eval calc_Aᵢ 2 { 1, 2, 3 } { 1, 2 }
#eval calc_Aᵢ 3 { 1, 2, 3 } { 1, 2 }
#eval calc_Bᵢ 1 { 1, 2, 3 } { 1, 2 }
#eval calc_Bᵢ 2 { 1, 2, 3 } { 1, 2 }
#eval calc_Bᵢ 3 { 1, 2, 3 } { 1, 2 }

def adv_11_ith_step (X A B : Finset ℕ) (h₁ : A ⊆ X) (h₂ : B ⊆ X) (z : 0 ∉ X) (i : ℕ) :=
  let Aᵢ := calc_Aᵢ i X A
  let Bᵢ := calc_Bᵢ i X A
  let Xᵢ := calc_Xᵢ i X
  Aᵢ = { x ∈ Xᵢ | odd_divides x Bᵢ }

def const_set (i: ℕ) : Finset ℕ := match i with
  | 0 => { 0 }
  | k + 1 => const_set (k) ∪ { i }

lemma const_set_mono (i: ℕ) : const_set (i) ⊆ const_set (i + 1) := by
  sorry
  done

lemma calc_Bᵢ_mono (X A : Finset ℕ) (i : ℕ)
  : calc_Bᵢ i X A ⊆ calc_Bᵢ (i + 1) X A := by
  intro x hₓ
  unfold calc_Bᵢ
  split_ifs
  · unfold calc_Bᵢ
    split
    . simp
      unfold calc_Bᵢ at hₓ
      split at hₓ
      . contradiction
      .
    . sorry
  . simp
    apply Or.inl
    exact hₓ
  done

lemma adv_11_base (X A B: Finset ℕ) (h₁ : A ⊆ X) (h₂ : B ⊆ X) (z : 0 ∉ X)
      : adv_11_ith_step X A B h₁ h₂ z 0 := by
  simp [adv_11_ith_step, calc_Aᵢ, eq_calc_zero, Finset.inter_empty]
  done

lemma adv_11_ind (X A B: Finset ℕ) (h₁ : A ⊆ X) (h₂ : B ⊆ X) (z : 0 ∉ X) (k : ℕ)
    : adv_11_ith_step X A B h₁ h₂ z k → adv_11_ith_step X A B h₁ h₂ z (k + 1) := by
  repeat rw [adv_11_ith_step]
  intro hy
  rw [Set.Subset.antisymm_iff]

  constructor
  . -- simp [calc_Aᵢ]
    intro x hₓ
    by_cases (x ∈ calc_Aᵢ k X A)
    . have : x ∈ {x | x ∈ calc_Xᵢ k X ∧ odd_divides x B} := by { rw [← hy]; exact h }
      have : x ∈ calc_Xᵢ k X ∧ odd_divides x B := this
      constructor
      . exact Finset.mem_of_mem_inter_right hₓ
      . exact this.right
    . sorry
  . sorry
  done
