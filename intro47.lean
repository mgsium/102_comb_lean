import Mathlib.Tactic

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
def standard_coloring : chessboard → ZMod 2 :=
  fun ⟨x, y⟩ ↦ x.val + y.val
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


theorem intro47 (f : numbering) { h : all_row_col_odd f }
  : Even (∑ sq in Finset.univ, f sq) := by
  sorry
  done
