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

-- returns the ith digit
def atIndex (i : ℕ) (h : 0 < i) : ℕ :=
  (digits 10 k)[toIndex k - i]!
  where k := fromIndex i h

#eval toIndex 10
#eval fromIndex 15 (by linarith)
#eval atIndex 15 (by linarith)

lemma valid_index (n : ℕ) {h : 0 < n} : toIndex (fromIndex n h) ≤ n := by
  unfold toIndex
  split
  . linarith
  . rename_i _ x heq
    have reeeeee : toIndex (succ x) ≤ n := by
      unfold fromIndex at heq
      apply (Finset.mem_filter.mp _).2
      . exact Finset.filter (fun x ↦ toIndex x ≤ n) (Finset.range (n + 1))
      . sorry --apply heq ▸ Finset.max'_mem
      done
    sorry
  done

-- lemma ree (n: ℕ) {h : 0 < n}
--     : n - toIndex (fromIndex n h) < length (digits 10 n) := by
--   rw [Nat.digits_len 10 n (by linarith) (by linarith)]
--   unfold toIndex
--   split <;> rename_i x heq
--   .
--   . rename_i x n_1 heq
--     simp_all only [ne_eq, ge_iff_le, gt_iff_lt]

--   done


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

-- theorem intro5 : atIndex 1983 (by norm_num) = 7 := by

--   done
