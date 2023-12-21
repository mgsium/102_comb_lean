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

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------

variable {n k : ℕ}

-- f(x) = kx is injective for k > 0
lemma mult_inj (hk : 0 < k): Injective (k * ·) := by
  intro x y h
  simp only [mul_eq_mul_left_iff, or_false] at h
  exact Or.elim h id <| fun h' ↦ by linarith

-- main theorem for counting multiples
theorem num_div (hk : 0 < k) : card ((Icc 0 n).filter (k ∣ ·)) = n / k + 1 := by
  have h : (Icc 0 n).filter (k ∣ ·) = image (k * ·) (Icc 0 (n / k)) := by
    ext x
    simp only [mem_filter, mem_Icc, mem_image, Nat.zero_le, true_and]
    constructor <;> intro h
    · use x / k, Nat.div_le_div_right h.left, Nat.mul_div_cancel' h.right
    · let ⟨a, ha, ha'⟩ := h
      rw [Nat.le_div_iff_mul_le hk] at ha
      exact ⟨by linarith, Dvd.intro a ha'⟩
  rw [h, card_image_of_injective _ (mult_inj hk), card_Icc, Nat.sub_zero]

-- define multiples of 3,4,5,12,15,20,60 in terms of sets
@[simp] abbrev mult  (n : ℕ) := (Icc 0 2001).filter (n ∣ ·)
@[simp] abbrev mult' (n : ℕ) := (Icc 1 2001).filter (n ∣ ·)

lemma mult_eq_insert_mult' {n : ℕ} : mult n = insert 0 (mult' n) := by
  ext x
  simp only [mem_insert, mem_Icc, Nat.zero_le, mem_filter]
  rw [one_le_iff_ne_zero]
  by_cases h' : x ≤ 0 <;> simp_all

lemma mem_mult_iff {n m: ℕ} : m ∈ mult n ↔ n ∣ m ∧ m ≤ 2001  := by
  unfold mult; rw [mem_filter, And.comm, mem_Icc]; norm_num

lemma mul_dvd_iff {a b c: ℕ} {h : Coprime a b} : a ∣ c ∧ b ∣ c ↔ a * b ∣ c := by
  constructor <;> intro g
  . apply Coprime.mul_dvd_of_dvd_of_dvd h g.1 g.2
  . exact ⟨dvd_of_mul_right_dvd g, dvd_of_mul_left_dvd g⟩

lemma mult_mul {n m : ℕ} (h : Coprime n m) : mult n ∩ mult m = mult (n * m) := by
  ext x
  simp only [mem_inter, mem_mult_iff]
  rw [← @mul_dvd_iff _ _ _ h]; tauto

-- this exists in mathlib in a newer version
lemma card_sdiff_add_card_inter (s t : Finset ℕ) :
    (s \ t).card + (s ∩ t).card = s.card := by
  rw [← card_disjoint_union (disjoint_sdiff_inter _ _), sdiff_union_inter]

-- apply inclusion-exclusion twice for a set theoretical identity needed for counting
theorem card_union_diff (s t r : Finset ℕ) : card ((s ∪ t) \ r) +
   card (s ∩ r) + card (t ∩ r) = card (s ∪ t) + card (s ∩ t ∩ r) := by
  have h : (s ∩ r) ∩ (t ∩ r) = s ∩ t ∩ r := by ext; simp_all
  rw [← h, add_assoc, ← card_union_add_card_inter (s ∩ r) (t ∩ r)]
  rw [← add_assoc, add_comm, ← inter_distrib_right s t r]
  rw [card_sdiff_add_card_inter]
  linarith

-- nat subtraction version of the previous theorem
theorem card_union_diff' (s t r : Finset ℕ) : card ((s ∪ t) \ r)
    = card (s ∪ t) + card (s ∩ t ∩ r) - card (t ∩ r) - card (s ∩ r):= by
  rw [← card_union_diff s t r]; simp

-- nat subtraction version card of union
theorem card_union_add_card_inter' (s t : Finset ℕ)
  : card (s ∪ t) = card s + card t - card (s ∩ t) :=
    eq_tsub_of_add_eq (card_union_add_card_inter s t)

macro "count" : tactic => `(tactic|(
  rw [mult_mul (by rfl), num_div (by linarith)] ; norm_num))

-- number of multiples of 3 and 4
lemma int_3_4 : card (mult 3 ∩ mult 4) = 167 := by count

-- number of multiples of 3 and 5
lemma int_3_5 : card (mult 3 ∩ mult 5) = 134 := by count

-- number of multiples of 4 and 5
lemma int_4_5 : card (mult 4 ∩ mult 5) = 101 := by count

-- number of multiples of 3 and 4 and 5
lemma int_3_4_5 : card (mult 3 ∩ mult 4 ∩ mult 5) = 34 := by
  rw [inter_assoc, mult_mul (by rfl)] ; count

-- number of multiples of 3 or 4
lemma uni_3_4 : card (mult 3 ∪ mult 4) = 1002 := by
  rw [card_union_add_card_inter', int_3_4]
  rw [num_div (by linarith), num_div (by linarith)]
  norm_num

-- in fact it doesn't matter if we include zero or not
theorem set_eq
  : (mult 3 ∪ mult 4) \ (mult 5) = (mult' 3 ∪ mult' 4) \ (mult' 5) := by
  simp only [mult_eq_insert_mult', union_insert, insert_sdiff_insert]
  simp only [insert_union, insert_sdiff_insert]
  rw [sdiff_insert_of_not_mem]
  simp_all

theorem card_with_0 : card ((mult 3 ∪ mult 4) \ mult 5) = 801 := by
  rw [card_union_diff', uni_3_4, int_3_4_5, int_3_5, int_4_5]

--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro4 : card ((mult' 3 ∪ mult' 4) \ mult' 5) = 801 := by
  rw [← set_eq] ; exact card_with_0
