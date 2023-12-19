import Mathlib.Tactic

/-!
# Intro 4 (pp. 18) | [AMC 12 2001]
How many positive integers not exceeding 2001 are multiples of 3 or 4 but not 5?

## Solution
Let M(x) return the number of multiples of x that are ≤ 2001. Using the
inclusion-exclusion principle it is easy to see that the answer is
M(3) + M(4) - M(12) - M(15) - M(20) + M(60) = 801.
-/
open Finset Nat Function

variable {n k : ℕ}

-- f(x) = kx is injective for k > 0
lemma mult_inj (hk : 0 < k): Injective (k * ·) := by
  intro x y h
  simp only [mul_eq_mul_left_iff, or_false] at h
  exact (Or.elim h id (fun h' => (by linarith)))

-- main theorem for counting multiples
theorem num_div (hk : 0 < k) : card ((Icc 0 n).filter (k ∣ ·)) = n / k + 1 := by
  have h : (Icc 0 n).filter (k ∣ ·) = image (k * ·) (Icc 0 (n / k)) := by
    ext x
    simp only [not_lt_zero', mem_Icc, _root_.zero_le, true_and, mem_filter, mem_image]
    constructor <;> intro h
    · use x / k, Nat.div_le_div_right h.left, Nat.mul_div_cancel' h.right
    · rcases h with ⟨h₁, h₂, h₃⟩
      refine ⟨?_, Dvd.intro h₁ h₃⟩
      rwa [← h₃, mul_comm, ← Nat.le_div_iff_mul_le hk]
  rw [h, card_image_of_injective _ (mult_inj hk), card_Icc, Nat.sub_zero]

-- define multiples of 3,4,5,12,15,20,60 in terms of sets
def set3 : Finset ℕ := (Icc 0 2001).filter (3 ∣ ·)
def set4 : Finset ℕ := (Icc 0 2001).filter (4 ∣ ·)
def set5 : Finset ℕ := (Icc 0 2001).filter (5 ∣ ·)
def set12 : Finset ℕ := (Icc 0 2001).filter (12 ∣ ·)
def set15 : Finset ℕ := (Icc 0 2001).filter (15 ∣ ·)
def set20 : Finset ℕ := (Icc 0 2001).filter (20 ∣ ·)
def set60 : Finset ℕ := (Icc 0 2001).filter (60 ∣ ·)

-- counting numbers ≤ 2001 which are divisible by 3,4,5,12,15,20,60
lemma num_div_3 : card set3 = 668 := by
  rw [set3, num_div (by norm_num)] ; norm_num

lemma num_div_4 : card set4 = 501 := by
  rw [set4, num_div (by norm_num)] ; norm_num

lemma num_div_5 : card set5 = 401 := by
  rw [set5, num_div (by norm_num)] ; norm_num

lemma num_div_12 : card set12 = 167 := by
  rw [set12, num_div (by norm_num)] ; norm_num

lemma num_div_15 : card set15 = 134 := by
  rw [set15, num_div (by norm_num)] ; norm_num

lemma num_div_20 : card set20 = 101 := by
  rw [set20, num_div (by norm_num)] ; norm_num

lemma num_div_60 : card set60 = 34 := by
  rw [set60, num_div (by norm_num)] ; norm_num

-- this exists in mathlib in a newer version
lemma card_sdiff_add_card_inter (s t : Finset ℕ) :
    (s \ t).card + (s ∩ t).card = s.card := by
  rw [← card_disjoint_union (disjoint_sdiff_inter _ _), sdiff_union_inter]

-- apply inclusion-exclusion twice for a set theoretical identity needed for counting
-- this proof should really be written using calc
theorem card_union_diff (s t r : Finset ℕ) : card ((s ∪ t) \ r) +
   card (s ∩ r) + card (t ∩ r) = card (s ∪ t) + card (s ∩ t ∩ r) := by
  have h : card ((s ∪ t) \ r) + card (s ∩ r ∪ t ∩ r) = card (s ∪ t)  := by
    have h' : s ∩ r ∪ t ∩ r = (s ∪ t) ∩ r := (inter_distrib_right s t r).symm
    rw [h'] ; apply card_sdiff_add_card_inter
  rw [← h]
  have h'': (s ∩ r) ∩ (t ∩ r) = s ∩ t ∩ r := by
    ext bob ; simp only [mem_inter, mem_union, mem_sdiff] ; tauto
  have h' : card (s ∩ r) + card (t ∩ r)
      = card (s ∩ r ∪ t ∩ r) + card (s ∩ t ∩ r) := by
    rw [← h'', card_union_add_card_inter]
  linarith

-- nat subtraction version of the previous theorem
theorem card_union_diff' (s t r : Finset ℕ) : card ((s ∪ t) \ r)
    = card (s ∪ t) + card (s ∩ t ∩ r)  - card (t ∩ r) - card (s ∩ r):= by
  have h {a b c d e : ℕ}(h: a + b + c = d + e): a = d + e - c - b := by
    rw [← h] ; norm_num
  exact h (card_union_diff s t r)

-- nat subtraction version card of union
theorem card_union_add_card_inter' (s t : Finset ℕ) : card (s ∪ t)
    = card s + card t - card (s ∩ t) := by
  have h: card (s ∪ t) + card (s ∩ t) = card s + card t :=
    by exact card_union_add_card_inter s t
  exact eq_tsub_of_add_eq h

-- number of multiples of 3 and 4
lemma int_3_4 : card (set3 ∩ set4) = 167 := by
  have h: set3 ∩ set4 = set12 := by
    unfold set3 set4 set12 ; ext bob
    simp only [mem_inter, mem_filter]
    constructor ; intro h
    all_goals simp_all only [true_and]
    · rcases h with ⟨h₁, h₂⟩
      exact Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h₁.2 h₂.2
    · intro h
      have h': 3 ∣ 12 := by norm_num
      have h'': 4 ∣ 12 := by norm_num
      exact ⟨Nat.dvd_trans h' h.2, Nat.dvd_trans h'' h.2⟩
  rw [h, num_div_12]

-- number of multiples of 3 or 4
lemma uni_3_4 : card (set3 ∪ set4) = 1002 := by
  rw [card_union_add_card_inter', num_div_3, num_div_4, int_3_4]

-- number of multiples of 3 and 5
lemma int_3_5 : card (set3 ∩ set5) = 134 := by
    have h: set3 ∩ set5 = set15 := by
      unfold set3 set5 set15 ; ext bob
      simp only [mem_inter, mem_filter]
      constructor ; intro h
      all_goals simp_all only [true_and]
      · rcases h with ⟨h₁, h₂⟩
        exact Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h₁.2 h₂.2
      · intro h
        have h': 3 ∣ 15 := by norm_num
        have h'': 5 ∣ 15 := by norm_num
        exact ⟨Nat.dvd_trans h' h.2, Nat.dvd_trans h'' h.2⟩
    rw [h, num_div_15]

-- number of multiples of 4 and 5
lemma int_4_5 : card (set4 ∩ set5) = 101 := by
    have h: set4 ∩ set5 = set20 := by
      unfold set4 set5 set20 ; ext bob
      simp only [mem_inter, mem_filter]
      constructor ; intro h
      all_goals simp_all only [true_and]
      · rcases h with ⟨h₁, h₂⟩
        exact Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h₁.2 h₂.2
      · intro h
        have h': 4 ∣ 20 := by norm_num
        have h'': 5 ∣ 20 := by norm_num
        exact ⟨Nat.dvd_trans h' h.2, Nat.dvd_trans h'' h.2⟩
    rw [h, num_div_20]

-- number of multiples of 3 and 4 and 5
lemma int_3_4_5 : card (set3 ∩ set4 ∩ set5) = 34 := by
      have h: set3 ∩ set4 ∩ set5 = set60 := by
        unfold set3 set4 set5 set60 ; ext bob
        simp only [mem_inter, mem_filter]
        constructor ; all_goals simp_all only [true_and] ; intro h
        · rcases h with ⟨⟨h₁, h₂⟩, h₃⟩
          have h' : 12 ∣ bob := by
            exact Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h₁.2 h₂.2
          exact Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h₃.2 h'
        · have h': 3 ∣ 60 := by norm_num
          have h'': 4 ∣ 60 := by norm_num
          have h''': 5 ∣ 60 := by norm_num
          constructor
          · exact ⟨Nat.dvd_trans h' h.2, Nat.dvd_trans h'' h.2⟩
          · exact Nat.dvd_trans h''' h.2
      rw [h, num_div_60]

-- the same sets without zero since the problem asks for positive integers
def set3' : Finset ℕ := (Icc 1 2001).filter (3 ∣ ·)
def set4' : Finset ℕ := (Icc 1 2001).filter (4 ∣ ·)
def set5' : Finset ℕ := (Icc 1 2001).filter (5 ∣ ·)

-- in fact it doesn't matter if we include zero or not
theorem set_eq : (set3 ∪ set4) \ set5 = (set3' ∪ set4') \ set5' := by
  simp only [set3, set4, set5, set3', set4', set5', mem_filter, mem_union, mem_Icc, mem_sdiff]
  ext x ; norm_num ; constructor ; swap ; tauto
  simp_all only [Nat.isUnit_iff, OfNat.ofNat_ne_one, implies_true, and_true]
  intro a ; rcases a with ⟨⟨h₁, h₂⟩, h₃⟩
  <;> simp_all only [Nat.isUnit_iff, OfNat.ofNat_ne_one, forall_true_left, and_true]
  · left ; by_cases h: x = 0
    · subst h ; exact absurd h₃ (by norm_num)
    · push_neg at h ; exact one_le_iff_ne_zero.mpr h
  · right ; by_cases h: x = 0
    · subst h ; exact absurd h₃ (by norm_num)
    · push_neg at h ; exact one_le_iff_ne_zero.mpr h

theorem card_set_eq : card ((set3 ∪ set4) \ set5)
    = card ((set3' ∪ set4') \ set5') := by
  rw [set_eq]

theorem card_with_0 : card ((set3 ∪ set4) \ set5) = 801 := by
  rw [card_union_diff' set3 set4 set5, uni_3_4, int_3_4_5, int_3_5, int_4_5]

--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro4 : card ((set3' ∪ set4') \ set5') = 801 := by
  rw [← card_set_eq] ; exact card_with_0
  done
