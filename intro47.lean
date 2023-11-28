import Mathlib.Tactic
import Mathlib.Data.ZMod.Parity
import Common

/-!

Each square of a 1998 × 2002 chess board contains either 0 or 1 such that the
total number of squares containing 1 is odd in each row and each column.
Prove that the number of white unit squares containing 1 is even.

-/

open BigOperators Finset

-- A chessboard is a 1998 × 2002 grid of squares
def chessboard : Type := Fin 1998 × Fin 2002
instance instFintypeChessboard : Fintype chessboard :=
  instFintypeProd (Fin 1998) (Fin 2002)

-- Standard chessboard coloring, starting with white
-- in the top left corner
def standard_coloring (sq : chessboard) : ZMod 2 :=
  sq.1.val + sq.2.val
def white_square (sq : chessboard) : Bool :=
  standard_coloring sq = 0

-- Define a numbering of the squares
def numbering : Type := chessboard → ZMod 2

-- A given row contains an odd number of 1s
def odd_row (f : numbering) (row : Fin 1998) : Prop :=
  Odd (∑ x in Finset.univ, f (row, x))
-- A given col contains an odd number of 1s
def odd_column (f : numbering) (col : Fin 2002) : Prop :=
  Odd (∑ x in Finset.univ, f (x, col))

-- Each row and each column contain an odd number of 1s
def all_row_col_odd (f : numbering) : Prop :=
  (∀ (row : Fin 1998), odd_row f row) ∧ (∀ (col : Fin 2002), odd_column f col)

def Rₒ (f : numbering) := ∑ i in Finset.Icc 1 999, ∑ j in Finset.univ, f ⟨i, j⟩
def Cₑ (f : numbering) := ∑ j in Finset.Icc 1 1001, ∑ i in Finset.univ, f ⟨i, j⟩

variable (f : numbering)
variable (h : all_row_col_odd f)

-- A square (i, j) is white iff i and j have the same parity
def white_iff_parity_eq (sq : chessboard)
  : white_square sq ↔ (Odd (sq.1 : ℕ) ↔ Odd (sq.2 : ℕ)) := by
  unfold white_square standard_coloring
  simp only [decide_eq_true_eq, ← Nat.even_add']
  suffices
    : ((sq.1 + sq.2 : ℕ) : ZMod 2) = 0  ↔ (sq.1 + sq.2 : ZMod 2) = 0
  . rw [← this, ZMod.eq_zero_iff_even]
  . simp only [Nat.cast_add]
  done

-- Sum of odd rows is odd
lemma odd_rows_sum_odd : Odd (Rₒ f) := by
  sorry
  done

-- Sum of even columns is odd
lemma even_cols_summ_odd : Odd (Cₑ f) := by
  sorry
  done

theorem intro47 : Even (∑ sq in Finset.univ, f sq) := by
  sorry
  done
