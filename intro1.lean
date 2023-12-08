import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic

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

open Nat Finset Function Fin

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup
def Alphabet : Type := Fin 26

instance instFintypeAlphabet : Fintype Alphabet := fintype 26
instance instDecidableEqAlphabet : DecidableEq Alphabet := instDecidableEqFin 26
instance instLTAlphabet : LT Alphabet := instLTFin
instance instFintypeAlphabetProd : Fintype (Alphabet × Alphabet) :=
  instFintypeProd Alphabet Alphabet

def ordered (a b : Alphabet) : Prop := a < b ∧ b.val < 25
instance decOrderedRel : DecidableRel ordered := by
  unfold ordered
  exact fun _ _ ↦ And.decidable
  done

instance decOrdered : DecidablePred (uncurry ordered) :=
  fun _ ↦ instDecidableUncurryProp

def starts_with (a : Alphabet) : Finset (Alphabet × Alphabet) :=
  @filter _ (fun (p : Alphabet × Alphabet) ↦ ordered p.1 p.2 ∧ p.1 = a)
  (fun _ ↦ And.decidable) univ

def monograms : Finset (Alphabet × Alphabet) :=
  filter (uncurry ordered) univ

def between_a_25 (a : Alphabet) : Finset Alphabet :=
  filter (fun b ↦ ordered a b) univ

-- starts_with a → between_a_25
def set_bijection (a : Alphabet) (p : Alphabet × Alphabet) (_ : p ∈ starts_with a) :
  Alphabet := p.2

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

example (a b c : ℕ) (h : a=b) (h' : b≠c) : a≠c := by exact Eq.trans_ne h h'

lemma starts_with_disjoint : Set.PairwiseDisjoint univ.toSet starts_with := by
  unfold Set.PairwiseDisjoint Set.Pairwise onFun starts_with
  simp_rw [disjoint_left]
  intro _ _ _ _ g _ ha
  rw [mem_filter] at *
  simp_rw [mem_univ, true_and] at *
  apply not_and_of_not_right
  exact Eq.trans_ne ha.2 g
  done

lemma set_eq : disjiUnion univ starts_with starts_with_disjoint = monograms := by
  ext x
  unfold monograms starts_with
  simp [uncurry_def]
  done

lemma fst_eq_a (a : Alphabet) (p : Alphabet × Alphabet)
  : p ∈ starts_with a → p.1 = a := by
  unfold starts_with
  rw [mem_filter]
  simp_rw [mem_univ, true_and]
  exact fun h ↦ h.2
  done

lemma icc_between_a_25 (a : Alphabet)
  : image (fun x ↦ x.val) (between_a_25 a) = Ioo a.val 25 := by
  ext b
  simp only [mem_image, gt_iff_lt, is_lt, not_true, ge_iff_le, mem_Ioo]
  unfold between_a_25
  simp_rw [mem_filter, mem_univ, true_and]
  unfold ordered
  constructor <;> intro h
  . let ⟨_, ⟨g, g'⟩⟩ := h
    rw [← g']
    simp only [val_fin_lt]
    exact g
  . use ofNat'' b --(pos a)
    simp only [ofNat_eq_val, coe_ofNat_eq_mod, mod_succ_eq_iff_lt]
    refine ⟨⟨?_, lt_of_le_of_lt (mod_le b 26) h.2⟩, (by linarith)⟩
    rw [lt_iff_val_lt_val, val_cast_of_lt (by linarith)]
    exact h.1
  done

lemma starts_with_card (a : Alphabet) : card (starts_with a) = 24 - a.val := by
  rw [@card_congr _ _ (starts_with a) (between_a_25 a) (set_bijection a)]
  . rw [← @card_image_of_injective _ _ (fun x ↦ x.val) _ _ (by simp)]
    rw [icc_between_a_25 a]
    simp only [gt_iff_lt, not_lt, ge_iff_le, Nat.card_Ioo, tsub_le_iff_right]
    exact tsub_right_comm
  . intro p hp
    unfold set_bijection between_a_25 starts_with at *
    rw [mem_filter] at *
    simp_rw [mem_univ, true_and] at *
    rw [← hp.2]
    exact hp.1
  . intro p q hp hq h
    unfold set_bijection at h
    ext
    . rw [fst_eq_a a p hp, fst_eq_a a q hq]
    . exact h
  . intro b h
    use (a,b), ?_
    . simp [set_bijection]
    . unfold starts_with
      rw [mem_filter]
      simp_rw [mem_univ, true_and, and_true]
      unfold between_a_25 at h
      simp only [mem_univ, forall_true_left, mem_filter, true_and] at h
      exact h
  done

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro1 : card monograms = 300 := by
  rw [← set_eq, card_disjiUnion]
  simp_rw [starts_with_card]
  done
