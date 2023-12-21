import Common.Common
import Mathlib.Tactic
import Mathlib.Data.ZMod.Parity

/-!
# Intro 47 (p. 44)

Each square of a 1998 × 2002 chess board contains either 0 or 1 such that the
total number of squares containing 1 is odd in each row and each column.
Prove that the number of white unit squares containing 1 is even.

## Solution Sketch

Let Rₒ be the sum of values in the 999 odd rows, and Cₑ be the sum of values in
the 1001 even columns. Let SB be the sum of black squares in even columns.
Observe that each white square appears exactly once in the sum Rₒ + Cₑ, and each
black square in an even column appears twice.

Since Cₑ is odd (sum of 999 odd numbers) and Rₒ is odd (sum of 1001 odd numbers)
, Rₒ + Cₑ - 2 * SB is even, so the sum of white squares is even.

-/

open BigOperators Finset SProd

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------

-- A chessboard is a 1998 × 2002 grid of squares
def chessboard : Type := Fin 1998 × Fin 2002
instance instDecidableEqChessboard : DecidableEq chessboard :=
  instDecidableEqProd
instance instFintypeChessboard : Fintype chessboard :=
  instFintypeProd (Fin 1998) (Fin 2002)

-- Standard chessboard coloring, starting with white
-- in the top left corner
def standard_coloring (sq : chessboard) : ZMod 2 :=
  sq.1.val + sq.2.val

def white_square (sq : chessboard) : Bool := standard_coloring sq = 0
def white_squares : Finset chessboard := filter (white_square ·) univ

def black_square (sq : chessboard) : Bool := standard_coloring sq = 1
def black_squares : Finset chessboard := filter (black_square ·) univ

-- Define a numbering of the squares
def numbering : Type := chessboard → ZMod 2

-- A given row contains an odd number of 1s
def odd_row (f : numbering) (row : Fin 1998) : Prop :=
  Odd (∑ x in univ, (f (row, x)).val)
-- A given col contains an odd number of 1s
def odd_column (f : numbering) (col : Fin 2002) : Prop :=
  Odd (∑ x in univ, (f (x, col)).val)

-- Each row and each column contain an odd number of 1s
def all_row_col_odd (f : numbering) : Prop :=
  (∀ (row : Fin 1998), odd_row f row) ∧ (∀ (col : Fin 2002), odd_column f col)

-- odd and even rows and cols
def odd_rows := filter (fun x => Odd x.val) (@univ (Fin 1998) _)
def even_rows := filter (fun x => Even x.val) (@univ (Fin 1998) _)
def odd_cols := filter (fun x => Odd x.val) (@univ (Fin 2002) _)
def even_cols := filter (fun x => Even x.val) (@univ (Fin 2002) _)

--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------

-- The coerced universal Finset for Fin n is equal to range n
lemma img_val_fin_eq (n : ℕ)
  : image (fun x => x.val) (@univ (Fin n) _) = range n := by
  ext a
  simp only [mem_image, mem_univ, true_and, mem_range]
  constructor <;> intro h
  . let ⟨x, hx⟩ := h
    rw [← hx]
    exact Fin.prop x
  . use Fin.ofNat' a (Nat.zero_lt_of_lt h)
    exact Nat.mod_eq_of_lt h
  done

lemma filter_eq' (S : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
  : filter p S = S \ filter (fun x => ¬ p x) S := by
  ext a
  simp only [mem_sdiff, mem_filter]
  tauto
  done

-- Number of odd rows is odd
lemma odd_card_odd_rows : Odd (card odd_rows) := by
  unfold odd_rows
  rw [← (@card_image_iff _ _ _ (fun x => x.val) _).mpr]
  . rw [← image_filter, img_val_fin_eq, ← sum_odd_odd' _, sum_range_id]; norm_num
  . simp only [Function.Injective.injOn, Fin.val_injective]

-- Number of even columns is odd
lemma odd_card_even_cols : Odd (card even_cols) := by
  unfold even_cols
  rw [← (@card_image_iff _ _ _ (fun x => x.val) _).mpr]
  . rw [← image_filter, img_val_fin_eq]
    rw [filter_eq' (range 2002) Even, card_sdiff (filter_subset _ _)]
    rw [Nat.odd_sub' (card_filter_le _ (¬Even ·))]
    simp only [mem_range, not_not, card_range, iff_true]
    simp_rw [← Nat.odd_iff_not_even]
    rw [← sum_odd_odd' _, sum_range_id]
    norm_num
  . simp only [Function.Injective.injOn, Fin.val_injective]

-- Sum of cells in odd rows
def Rₒ (f : numbering) := ∑ i in odd_rows , ∑ j in univ, (f ⟨i, j⟩).val
-- Sum of cells in even columns
def Cₑ (f : numbering) := ∑ j in even_cols, ∑ i in univ, (f ⟨i, j⟩).val

variable (f : numbering) (h : all_row_col_odd f)

-- a sqaure is black iff it is not white
lemma black_square_iff_not_white {sq : chessboard} :
  black_square sq ↔ ¬ white_square sq := by
  unfold black_square white_square
  simp only [decide_eq_true_eq, zmod2_eq_iff]

-- a square is white iff it is not black
lemma white_square_iff_not_black {sq : chessboard} :
  white_square sq ↔ ¬ black_square sq := by
    rw [black_square_iff_not_white, not_not]

-- a square (i, j) is white iff i and j have the same parity
lemma white_iff_parity_eq (sq : chessboard)
  : white_square sq ↔ (Odd (sq.1 : ℕ) ↔ Odd (sq.2 : ℕ)) := by
  unfold white_square standard_coloring
  simp only [decide_eq_true_eq, ← Nat.even_add']
  suffices
    : ((sq.1 + sq.2 : ℕ) : ZMod 2) = 0  ↔ (sq.1 + sq.2 : ZMod 2) = 0
  . rw [← this, ZMod.eq_zero_iff_even]
  . simp only [Nat.cast_add]
  done

-- a square (i, j) is black iff i and j don't have the same parity
lemma black_iff_parity_ne (sq : chessboard)
  : black_square sq ↔ (Odd (sq.1 : ℕ) ↔ ¬ Odd (sq.2 : ℕ)) := by
  rw [black_square_iff_not_white, white_iff_parity_eq]
  tauto

-- the finset set of white squares is equal to
-- odd_rows ×ˢ odd_cols ∪ even_rows ×ˢ even_cols
lemma white_squares_eq
  : white_squares = odd_rows ×ˢ odd_cols ∪ even_rows ×ˢ even_cols := by
  ext x
  simp_rw [white_squares, mem_filter_univ]
  unfold odd_rows odd_cols even_rows even_cols
  rw [white_iff_parity_eq, mem_union, mem_product, mem_product]
  simp_rw [mem_filter_univ, Nat.even_iff_not_odd]
  tauto
  done

-- there of two sets of disjoint equal-parity squares
lemma odd_odd_disj_even_even :
  Disjoint (odd_rows ×ˢ odd_cols) (even_rows ×ˢ even_cols) := by
  unfold odd_rows even_rows
  simp_rw [Nat.odd_iff_not_even, disjoint_iff_ne, mem_product, mem_filter_univ]
  intro a ha b hb
  by_contra h'
  rw [h'] at ha
  tauto
  done

-- The sum of all black squares in even columns
def B : Finset chessboard :=
  filter (fun s => black_square s ∧ Even s.2.val) univ
def SB (f : numbering) := ∑ s in B, (f s).val

lemma SB_eq_sum :
  SB f = ∑ i in odd_rows, ∑ j in even_cols, (f (i, j)).val
  := by
    unfold SB B
    rw [← @sum_product _ _ _ _ _ _ (fun s => (f s).val)]
    apply sum_congr _ (fun _ _ ↦ rfl)
    ext ⟨x, y⟩
    unfold odd_rows even_cols
    rw [mem_filter_univ, mem_product]
    simp_rw [mem_filter_univ]
    simp only [and_imp, Nat.odd_iff_not_even, and_congr_left_iff]
    rw [← Nat.odd_iff_not_even, black_iff_parity_ne]
    simp only [Nat.odd_iff_not_even, not_not]
    tauto
    done

-- sum of odd rows is odd
lemma odd_rows_sum_odd : Odd (Rₒ f) := by
  let f' i := ∑ j in univ, (f ⟨i, j⟩).val
  unfold Rₒ
  apply (@sum_odd_odd _ _ odd_rows f' (fun x _ ↦ h.1 x)).mpr odd_card_odd_rows

-- sum of even columns is odd
lemma even_cols_summ_odd : Odd (Cₑ f) := by
  let f' j := ∑ i in univ, (f ⟨i, j⟩).val
  unfold Cₑ
  exact (@sum_odd_odd _ _ even_cols f' (fun x _ ↦ h.2 x)).mpr odd_card_even_cols

-- sum of odd rows and even columns minus 2 * SB  is even
lemma even_r_add_c_sub_b : Even (Rₒ f + Cₑ f - 2 * SB f) := by
  rw [Nat.even_sub]
  . simp only [even_two, Even.mul_right, iff_true]
    rw [Nat.even_add, ← not_iff_not]
    repeat rw [← Nat.odd_iff_not_even]
    exact iff_of_true (odd_rows_sum_odd f h) (even_cols_summ_odd f h)
  . unfold Rₒ Cₑ
    rw [SB_eq_sum, two_mul]
    conv => rhs; rhs; rw [Finset.sum_comm]
    apply Nat.add_le_add
    . apply GCongr.sum_le_sum
      exact fun _ _ ↦ sum_le_sum_of_subset (subset_univ _)
    . apply sum_le_sum_of_subset (subset_univ _)
  done

-- (set of Rₒ ∪ set of Cₑ) ∖ B = white_squares
lemma r_union_c_minus_b_eq_white_sqaures : white_squares
  = ((odd_rows ×ˢ univ) ∪ (univ ×ˢ even_cols)) \ B := by
  ext a
  unfold B white_squares odd_rows even_cols
  simp_rw [mem_sdiff, mem_filter_univ, white_square_iff_not_black, mem_union]
  repeat rw [mem_product, mem_filter_univ]
  simp_rw [mem_univ, true_and, and_true, black_iff_parity_ne]
  rw [← Nat.even_iff_not_odd]
  tauto
  done

-- prove that sum of white_squares is
-- sum of even rows, even cols + sum of odd rows, odd col
lemma odd_even_sub_eq_sum_white : Rₒ f + Cₑ f - 2 * SB f = ∑ sq in white_squares ∩
    (((odd_rows ×ˢ univ) ∪ (univ ×ˢ even_cols)) \ B), (f sq).val := by
    rw [← r_union_c_minus_b_eq_white_sqaures, inter_self]
    unfold Rₒ Cₑ
    rw [sum_comm]
    conv => lhs; lhs; rhs; rw [sum_comm]
    repeat rw [← sum_filter_add_sum_filter_not univ (fun x => Even x.val)]
    simp_rw [← Nat.odd_iff_not_even]
    rw [← even_cols, ← odd_cols, ← even_rows, ← odd_rows, ← add_assoc]
    rw [SB_eq_sum, sum_comm, add_assoc, add_assoc, add_comm, ← add_assoc]
    rw [add_assoc, ← two_mul]
    norm_num
    rw [sum_comm]
    repeat rw [← @sum_product _ _ _ _ _ _ (fun s => (f s).val)]
    rw [white_squares_eq, ← sum_union odd_odd_disj_even_even]
    rfl
    done

--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro47 : Even (∑ sq in white_squares, (f sq).val) := by
  rw [← inter_self white_squares]
  nth_rewrite 2 [r_union_c_minus_b_eq_white_sqaures]
  rw [← odd_even_sub_eq_sum_white f]
  exact even_r_add_c_sub_b f h
  done
