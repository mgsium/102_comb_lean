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

-- foldr implementation
-- def concatenate (L : List ℕ) : ℕ := L.foldr (fun x y => x + 10^((log 10 x)+1) * y) 0

def concatenate : List ℕ -> ℕ
  | [] => 0
  | x :: xs => x + 10 ^ ((log 10 x) + 1) * concatenate xs

#eval concatenate [1,2,3,4,5].reverse

def a_b_num (a b : ℕ) : ℕ := concatenate (List.Ico a (b+1))

def a_b_arr (a b : ℕ) : List ℕ := digits 10 $ a_b_num a b

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

lemma conc_inc (n : ℕ) : (a_b_arr 1 n).length ≤ (a_b_arr 1 (n + 1)).length := by
  sorry
  done

lemma conc_length (n : ℕ) : (a_b_arr 1 n).length ≥ n := by
  sorry
  done

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro5 : (a_b_arr 1 1000)[1983]'(by sorry) = 7 := by
  sorry
  done
