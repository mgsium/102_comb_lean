import Mathlib.Tactic

/-!
# Intro 1
Mr. and Mrs. Zeta want to name their baby Zeta so that its monogram (first,
middle, and last initials) will be in alphabetical order with no letters
repeated. How nany such monograms are possible?

## Solution
The last initial is fixed at Z. If the first initial is A, then the second
initial must be one of B,C,D,...,X,Y, so there are 24 choices for the second.
If the first initial is B, then the second must be in C,D,E,...,X,Y, so there
are 23 choices for the second initial. Continuing in this way, we see that the
number of monograms is 24+23+22+...+2+1 = 300.

-/

--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

open Nat Set Finset


end useful_lemmas


--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------
open Nat Set Finset Function

def Alphabet : Type := Fin 26

instance instFintypeAlphabet : Fintype Alphabet := Fin.fintype 26
instance instDecidableEqAlphabet : DecidableEq Alphabet := instDecidableEqFin 26
instance instLTAlphabet : LT Alphabet := instLTFin
instance instFintypeAlphabetProd : Fintype (Alphabet × Alphabet) :=
  instFintypeProd Alphabet Alphabet

def ordered (a b : Alphabet) : Prop := a < b ∧ b.val < 25
instance decOrderedRel : DecidableRel ordered := by
  unfold ordered
  -- unfold DecidableRel
  exact fun _ _ ↦ And.decidable
  done

instance decOrdered : DecidablePred (uncurry ordered) :=
  fun _ ↦ instDecidableUncurryProp

def starts_with (a : Alphabet) : Finset (Alphabet × Alphabet) :=
  @filter _ (fun (p : Alphabet × Alphabet) ↦ ordered p.1 p.2 ∧ p.1 = a)
  (fun _ ↦ And.decidable) univ

lemma starts_with_disjoint : PairwiseDisjoint (Finset.univ).toSet starts_with := by
  unfold PairwiseDisjoint Set.Pairwise onFun starts_with
  intro x _ y _ g
  rw [Finset.disjoint_left]
  intro _ ha
  rw [mem_filter] at *
  simp_rw [Finset.mem_univ, true_and] at *
  push_neg
  intro _
  rw [ha.2]
  exact g
  done

def monograms : Finset (Alphabet × Alphabet) :=
  filter (uncurry ordered) univ

lemma set_eq : Finset.disjiUnion univ starts_with starts_with_disjoint = monograms
  := by
  ext x
  unfold monograms starts_with
  simp_rw [mem_filter, Finset.mem_univ, true_and]
  simp [uncurry_def]
  done

def between_a_25 (a : Alphabet) : Finset Alphabet :=
  filter (fun b ↦ ordered a b) univ

-- lemma card_eq (a : Alphabet) : card (starts_with a) = card (between_a_25 a) := by

--   done

def set_bijection (a : Alphabet) (i : ℕ) (h : i < 24 - a.val) :
  Alphabet × Alphabet := (a, @Fin.ofNat'' 26 NeZero.succ i)

lemma fst_eq_a (a : Alphabet) (p : (Alphabet × Alphabet))
  : p ∈ starts_with a → p.1 = a := by
  unfold starts_with
  rw [mem_filter]
  simp_rw [Finset.mem_univ, true_and]
  exact fun h ↦ h.2
  done

lemma bruh (a : Alphabet) (p : Alphabet × Alphabet) (h : p ∈ starts_with a)
  : p.2.val < 24 - a.val := by
  unfold starts_with at h
  rw [mem_filter] at h
  simp_rw [Finset.mem_univ, true_and] at h
  unfold ordered at h
  sorry
  done

lemma starts_with_card (a : Alphabet) : card (starts_with a) = 24 - a.val := by
  apply Finset.card_eq_of_bijective $ set_bijection a
  . intro p h
    use p.2.val
    use ?_
    . unfold set_bijection
      rw [Fin.ofNat_eq_val, Fin.cast_val_eq_self]
      ext <;> simp [fst_eq_a a p h]
    . exact bruh
  . sorry
  . sorry
  done


theorem intro1 : card monograms = 300 := by
  rw [← set_eq, card_disjiUnion]
  simp_rw [starts_with_card]
  done
