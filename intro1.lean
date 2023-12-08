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

open Nat Set Finset Function Fin

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
def set_bijection (a : Alphabet) (p : Alphabet × Alphabet) (h : p ∈ starts_with a) :
  Alphabet := p.2

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

example (a b c : ℕ) (h : a=b) (h' : b≠c) : a≠c := by exact Eq.trans_ne h h'

lemma starts_with_disjoint : PairwiseDisjoint (Finset.univ).toSet starts_with := by
  unfold PairwiseDisjoint Set.Pairwise onFun starts_with
  simp_rw [Finset.disjoint_left]
  intro _ _ _ _ g _ ha
  rw [mem_filter] at *
  simp_rw [Finset.mem_univ, true_and] at *
  apply not_and_of_not_right
  exact Eq.trans_ne ha.2 g
  done

lemma set_eq : Finset.disjiUnion univ starts_with starts_with_disjoint = monograms
  := by
  ext x
  unfold monograms starts_with
  simp_rw [mem_filter, Finset.mem_univ, true_and]
  simp [uncurry_def]
  done

lemma fst_eq_a (a : Alphabet) (p : (Alphabet × Alphabet))
  : p ∈ starts_with a → p.1 = a := by
  unfold starts_with
  rw [mem_filter]
  simp_rw [Finset.mem_univ, true_and]
  exact fun h ↦ h.2
  done

lemma icc_between_a_25 (a : Alphabet)
  : Finset.image (fun x ↦ x.val) (between_a_25 a) = Finset.Ioo a.val 25 := by
  ext b
  simp only [Finset.mem_image, gt_iff_lt, is_lt, not_true, ge_iff_le, Finset.mem_Ioo]
  unfold between_a_25
  simp_rw [mem_filter, Finset.mem_univ, true_and]
  unfold ordered
  constructor <;> intro h
  . let ⟨x, ⟨g, g'⟩⟩ := h
    rw [← g']
    simp only [val_fin_lt]
    exact g
  . use ofNat'' b --(pos a)
    simp only [ofNat_eq_val, coe_ofNat_eq_mod, mod_succ_eq_iff_lt]
    let ⟨g,g'⟩ := h
    repeat constructor
    . rw [lt_iff_val_lt_val, val_cast_of_lt (by linarith)]
      exact g
    . exact Nat.lt_of_le_of_lt (Nat.mod_le b 26) g'
    . linarith
  done

lemma starts_with_card (a : Alphabet) : card (starts_with a) = 24 - a.val := by
  rw [@Finset.card_congr _ _ (starts_with a) (between_a_25 a) (set_bijection a)]
  . rw [← @Finset.card_image_of_injective _ _ (fun x ↦ x.val) _ _ (by simp)]
    rw [icc_between_a_25 a]
    simp only [gt_iff_lt, not_lt, ge_iff_le, Nat.card_Ioo, tsub_le_iff_right]
    exact tsub_right_comm
  . intro p hp
    unfold set_bijection between_a_25
    unfold starts_with at hp
    rw [mem_filter] at *
    simp_rw [Finset.mem_univ, true_and] at *
    rw [← hp.2]
    exact hp.1
  . intro p q hp hq
    push_neg
    intro h
    unfold set_bijection at h
    ext
    . rw [fst_eq_a a p hp, fst_eq_a a q hq]
    . exact h
  . intro b h
    use (a,b)
    have h' : (a,b) ∈ starts_with a := by
      unfold starts_with
      rw [mem_filter]
      simp_rw [Finset.mem_univ, true_and, and_true]
      unfold between_a_25 at h
      simp only [Finset.mem_univ, forall_true_left, mem_filter, true_and] at h
      exact h
      done
    use h'
    unfold set_bijection
    trivial
  done

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro1 : card monograms = 300 := by
  rw [← set_eq, card_disjiUnion]
  simp_rw [starts_with_card]
  done
