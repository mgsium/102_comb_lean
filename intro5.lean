import Mathlib.Tactic
import Mathlib.Data.List.Intervals

/-!
# Intro 5 (p.3)

## Solution

-/

open Nat Finset Set List

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup


-- n ↦ index of last digit of n in string 12345...n
def myFunc : ℕ → ℕ
  | 0     => 0
  | n + 1 => (log 10 $ n + 1) + 1 + myFunc n

-- n ↦ minimum k such that myFunc k ≥ n
def myInv (n : ℕ) (h : 0 < n) :=
  Finset.max' (Finset.filter (myFunc · < n) (range n)) e + 1
  where e := by use 0; simp [h, (by ring_nf : myFunc 0 = 0)]

def at_index (n : ℕ) (h : 0 < n) : ℕ := myInv n h - n

#eval at_index 10 (by linarith)

#eval myFunc 11
#eval @myInv 12 (by linarith)

-- foldr implementation
-- def concatenate (L : List ℕ)
--     : ℕ := L.foldr (fun x y => x + 10^((log 10 x)+1) * y) 0

def concatenate : List ℕ -> ℕ
  | [] => 0
  | x :: xs => x + 10 ^ ((log 10 x) + 1) * concatenate xs

#eval concatenate [12,20]

def a_b_num (a b : ℕ) : ℕ := concatenate (List.Ico a (b+1)).reverse

def a_b_arr (a b : ℕ) : List ℕ := (digits 10 $ a_b_num a b).reverse

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro5 : (a_b_arr 1 1000)[1983]'(by sorry) = 7 := by
  sorry
  done
