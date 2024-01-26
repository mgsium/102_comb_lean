import Mathlib.Tactic
import Mathlib.Data.List.Intervals

/-!
# Intro 5 (p.3)

## Solution

-/

open Nat Finset Set

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup

-- n ↦ index of last digit of n in string 12345...n
def toIndex : ℕ → ℕ
  | 0     => 0
  | n + 1 => (log 10 (n + 1)) + 1 + toIndex n

lemma le_toIndex (n : ℕ) : n ≤ toIndex n := by
  induction' n with d hd
  . rfl
  . unfold toIndex
    linarith
  done

-- i ↦ the number the ith digit is in
def fromIndex (i : ℕ) (h : 0 < i) :=
  Finset.min' (Finset.filter (toIndex · ≥ i) (range (i+1))) e
  where e := by use i ; simp [le_toIndex i]

lemma fromIndex_eq_zero_iff (i : ℕ) (h : 0 < i) : fromIndex i h ≠ 0 := by
  by_contra h'
  unfold fromIndex at h'
  have h'' := min'_mem (Finset.filter (fun x ↦ toIndex x ≥ i) (Finset.range (i + 1)))
    (by use i ; simp [le_toIndex i])
  rw [h', mem_filter, (by rfl : toIndex 0 = 0)] at h''
  linarith
  done

-- returns the ith digit
def atIndex (i : ℕ) (h : 0 < i) : ℕ :=
  List.get (digits 10 $ fromIndex i h) (Fin.ofNat' (toIndex (fromIndex i h) - i)
  (by
  rw [digits_len]
  simp_all only [ne_eq, gt_iff_lt, add_pos_iff, log_pos_iff, and_true, or_true]
  . linarith
  . exact fromIndex_eq_zero_iff i h
  ))

-- #eval toIndex 10
-- #eval fromIndex 15 (by linarith)
-- #eval atIndex 15 (by linarith)

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------
-- #eval atIndex 1983 (by linarith)

-- #eval fromIndex 1983 (by linarith)

-- theorem intro5 : atIndex 1983 (by norm_num) = 7 := by
--   unfold atIndex

--   done

-- def myList : ℕ → List ℕ
--   | 0 => []
--   | succ n => myList n ++ (digits 10 $ succ n).reverse

-- lemma nonempty_myList (n : ℕ) (h : 0 < n) : myList n ≠ [] := by
--   unfold myList
--   split
--   . trivial
--   . simp_all only [succ_pos', digits_of_two_le_of_pos, ne_eq, List.reverse_cons, List.append_eq_nil,
--       List.reverse_eq_nil, and_false, not_false_eq_true]
--   done

-- lemma nonempty_digits (n : ℕ) (h : 0 < n) : 0 < List.length (digits 10 n) := by
--   have g : 0 ≠ n := by exact Nat.ne_of_lt h
--   rw [List.length_pos_iff_ne_nil]
--   rw [Nat.digits_ne_nil_iff_ne_zero]
--   exact g.symm
--   done

-- lemma last_digit (n : ℕ) {h : 0 < n} : List.getLast (myList n) (nonempty_myList n h)
--     = (digits 10 n)[0]'(nonempty_digits n h) := by
--   simp_all only [digits_of_two_le_of_pos, ne_eq, List.getElem_eq_get, List.length_cons, Fin.zero_eta,
--     List.get_cons_zero]
--   unfold myList
--   split
--   . trivial
--   . simp_all only [succ_pos', digits_of_two_le_of_pos, ne_eq, List.reverse_cons]

--   done

def f : ℕ → List ℕ
  | 0 => []
  | succ n => f n ++ (digits 10 $ succ n).reverse

abbrev f' (n m: ℕ) := (f m).drop (f n).length

#eval f' 697 700
#eval f 700 = f 697 ++ f' 697 700
#eval (f 700).splitAt 1983 = (f 697, f' 697 700)

-- example : (f 697).length = 1983 := by rfl

lemma split (n : ℕ) (h : 1983 ≤ (f n).length) : ((f n).splitAt 1983).1 = f 697 := by
  sorry
  done

lemma intro5 (n : ℕ) (h : 1983 ≤ (f n).length) : (f n)[1982]'h = 7 := by
  sorry
  done
