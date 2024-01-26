import Mathlib.Tactic

/-!
# Advanced 11 (p. 59) | [MOSP 1999]

Let X be a finite set of positive integers and A a subset of X.
Prove that there exists a subset B of X such that A equals the set of elements
of X which divide an odd number of elements of B.

## Solution Sketch

...

-/

open Set Finset Nat

-- x divides an odd number of elements of B
def odd_divides (x : ℕ) (B : Finset ℕ) : Bool :=
  card (B.filter (x ∣ ·)) % 2 ≠ 0

#eval (fun x B ↦ (filter (x ∣ ·) B).card % 2 ≠ 0) 2 { 1, 2, 3, 4 }
#eval odd_divides 2 { 1, 2, 3, 4 }

example : odd_divides 2 { 1, 2, 3 } := by
  simp [odd_divides]
  done

example (i k : ℕ) (h : i ≤ k) : i - 1 ≤ k := by
  { norm_num; exact le_step h }

def calc_Xᵢ (i : ℕ) (X : Finset ℕ) : Finset ℕ :=
  List.toFinset $ List.take i $ X.sort (· ≥ ·)

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
  simp [h (List.mem_dedup.mp h2)]
  done

lemma calc_X_inc (X : Finset ℕ) (i : ℕ)
  : calc_Xᵢ i X ⊆ calc_Xᵢ (i+1) X := by
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


lemma calc_Bᵢ_threshold (X A : Finset ℕ) (i: ℕ) (h: X.card < i)
  : calc_Bᵢ i X A = calc_Bᵢ (i + 1) X A := by
  unfold calc_Bᵢ
  split
  . contradiction
  . split_ifs with a b
    . rfl
    . simp at h b
      by_contra
      have : card X < card X := lt_trans h b
      exact LT.lt.false this
    . contradiction
    . contradiction
  done

lemma calc_Bᵢ_mono (X A : Finset ℕ) (i : ℕ)
  : calc_Bᵢ i X A ⊆ calc_Bᵢ (i + 1) X A := by
  by_cases (i = X.card)
  . intro x hₓ
    unfold calc_Bᵢ
    simp at *
    split_ifs
    . rw [← h]
      exact hₓ
    . simp
      exact hₓ
    . simp
      apply Or.inl
      exact hₓ
  . by_cases (i > X.card)
    . refine subset_of_eq ?_
      apply calc_Bᵢ_threshold X A i
      exact h
    . simp at h
      intro x hₓ
      unfold calc_Bᵢ
      split_ifs with a <;> simp at a
      case _ hₙ
      . by_contra
        have : i < card X := lt_of_le_of_ne h hₙ
        apply le_lt_antisymm this a
      . simp
        apply Or.inl
        exact hₓ
  done


/-
lemma calc_Bᵢ_i_geq_card_X (X A : Finset ℕ)
  : ∀i≥card X, calc_Bᵢ i X A = calc_Bᵢ (card X) X A := by
  intro i h
  induction i with
  | zero =>
    simp at h
    rw [h]
    rfl
  | succ i ih =>
    rw [← calc_Bᵢ_threshold]
    by_cases (i≥card X)
    . apply ih
      exact h
    case _ h₁
    . norm_num at h
      norm_num at h₁
      sorry
    . simp at h

    -- exact calc_Bᵢ_threshold
  done
-/


def nat_num_set (i: ℕ) : Finset ℕ := match i with
  | 0   => {0}
  | k+1 => nat_num_set (k) ∪ {i}

lemma nat_num_mono (i: ℕ) : nat_num_set (i) ⊆ nat_num_set (i + 1) := by
  match i with
  | 0 =>
    unfold nat_num_set
    simp
  | k+1 =>
    intros x h
    unfold nat_num_set
    norm_num
    apply Or.inl
    exact h
  done

def fix_five (i : ℕ) : Finset ℕ := match i with
  | 0   => {0}
  | k+1 => if k+1<5 then
    nat_num_set (k) ∪ {i}
    else nat_num_set (5)

lemma calc_Bᵢ_zero (X A : Finset ℕ)
  : calc_Bᵢ 0 X A = ∅ := rfl

lemma calc_Bᵢ_i_geq_card_X (X A : Finset ℕ) (i : ℕ) (h : i ≥ card X)
  : calc_Bᵢ i X A = calc_Bᵢ (card X) X A := by

  induction i with
  | zero =>
    norm_num at h
    rw [h]
    rfl
  | succ n ih =>

    done

def adv_11_ith_step (X A : Finset ℕ) (i : ℕ) :=
  Aᵢ = { x ∈ Xᵢ | odd_divides x Bᵢ }
  where Aᵢ := calc_Aᵢ i X A
        Bᵢ := calc_Bᵢ i X A
        Xᵢ := calc_Xᵢ i X

lemma adv_11_ind (X A B : Finset ℕ) (h₁ : A ⊆ X) (h₂ : B ⊆ X) (z : 0 ∉ X)
      : ∀i:ℕ, adv_11_ith_step X A i → adv_11_ith_step X A (i+1):= by
  intro i h
  unfold adv_11_ith_step
  apply Set.ext
  intro x
  constructor
  . sorry
  . sorry
  done

--lemma adv_11_base (X A B: Finset ℕ) (h₁ : A ⊆ X) (h₂ : B ⊆ X) (z : 0 ∉ X)
--      : adv_11_ith_step X A B h₁ h₂ z 0 := by
--  simp [adv_11_ith_step, calc_Aᵢ, eq_calc_zero, Finset.inter_empty]
--  done

/-
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
-/
