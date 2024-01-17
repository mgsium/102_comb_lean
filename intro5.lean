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
