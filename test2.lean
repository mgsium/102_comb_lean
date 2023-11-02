
import Mathlib.Tactic

open Finset
open Nat


def nth_element (n : ℕ): ℕ := ((fun p => (p.2, p.1 + p.2))^[n-1] (4, 5)).1

def c_counter (c : ℕ) : Finset ℕ :=
  if c = 0 then
    ∅
  else
    c_counter (c-1) ∪ {nth_element c}


#eval c_counter 10

lemma c_counter_card {c : ℕ} : card (c_counter c) = c := by
  induction' c with d hd
  . simp
  . unfold c_counter
    simp

  done



def recursive (n : ℕ) : Finset ℕ :=
  if n = 0 then
    {0}
  else
    recursive (n-1) ∪ {n}

#eval recursive 13


theorem card_test (n : ℕ) : card (recursive n) = n := by
  apply?
  done


/-
theorem card_additive :
  ∀(S T: Finset ℕ), (S ∩ T = ∅) → (card (S ∪ T) = card S + card T) := by
  intro S T h

  done


def card_of_union (A B : Finset ℕ)
  : card (A ∪ B) = card A + card B - card (A ∩ B) := by

  done

--lemma simp_card {n : ℕ} : card (recursive n) = n := by
--  induction' n with d hd
--  . simp
--  . unfold recursive
--    sorry
--  done
-/
