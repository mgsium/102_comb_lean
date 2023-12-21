import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic

/-!
# Intro 1 (p.2)
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

abbrev Alphabet : Type := Fin 26

def ordered (a b : Alphabet) : Prop :=
  a < b ∧ b.val < 25
instance decOrderedRel : DecidableRel ordered :=
  fun _ _ ↦ And.decidable

instance decOrdered : DecidablePred (uncurry ordered) :=
  fun _ ↦ instDecidableUncurryProp

-- all ordered alphabet pairs
def monograms : Finset (Alphabet × Alphabet) :=
  filter (uncurry ordered) univ

-- all ordered alphabet pairs with a fixed first element
def monos_with (x : Alphabet) : Finset (Alphabet × Alphabet) :=
  @filter _ (fun p ↦ ordered p.1 p.2 ∧ p.1 = x) (fun _ ↦ And.decidable) univ

-- all letters which follow some fixed letter `x` in the alphabet, except 'z'
def ord_from (x : Alphabet) : Finset Alphabet :=
  filter (ordered x ·) univ

-- monos_with a → a_to_25
def monos_to_interval (a : Alphabet) (p : Alphabet × Alphabet)
  (_ : p ∈ monos_with a) : Alphabet := p.2

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas

-- For any two distinct letters `L₁` and `L₂`, `monos_with L₁` is disjoint
-- from `mono_with L₂`
lemma monos_disjoint : Set.PairwiseDisjoint univ.toSet monos_with := by
  unfold Set.PairwiseDisjoint Set.Pairwise onFun monos_with
  simp_rw [disjoint_left]
  intro _ _ _ _ g _ ha
  rw [mem_filter] at *
  simp_rw [mem_univ, true_and] at *
  apply not_and_of_not_right
  exact Eq.trans_ne ha.2 g
  done

-- The disjoint union of all the `monos_with` finsets indexed over the univeral
-- set of letters (i.e. values of type `Alphabet`) is equal to the set of monograms
lemma union_monos_with_eq_monograms
  : disjiUnion univ monos_with monos_disjoint = monograms := by
  ext; simp [monograms, monos_with, uncurry_def]

-- If a pair `p` is in `monos_with x`, the first element of `p` must equal `x`
lemma mono_first (a : Alphabet) (p : Alphabet × Alphabet)
  : p ∈ monos_with a → p.1 = a := by
  unfold monos_with
  rw [mem_filter]
  simp_rw [mem_univ, true_and]
  exact fun h ↦ h.2
  done

-- The set of values of letters in `ord_from a` is equal to the open interval
-- from `a` to 25 for any fixed letter `a`.
lemma ord_from_eq_Ioo (a : Alphabet)
  : image (fun x ↦ x.val) (ord_from a) = Ioo a.val 25 := by
  ext b
  simp only [mem_image, gt_iff_lt, is_lt, not_true, ge_iff_le, mem_Ioo]
  unfold ord_from
  simp_rw [mem_filter, mem_univ, true_and]
  unfold ordered
  constructor <;> intro h
  . let ⟨_, ⟨g, g'⟩⟩ := h
    rw [← g', val_fin_lt]
    exact g
  . use ofNat'' b
    simp only [ofNat_eq_val, coe_ofNat_eq_mod, mod_succ_eq_iff_lt]
    rw [lt_iff_val_lt_val, val_cast_of_lt (by linarith)]
    simp only [lt_of_le_of_lt (mod_le b 26) h.2, h, lt.step h.2]
  done

-- The cardinality of `monos_with a` is equal to 24 minus the value of `a`
lemma monos_card (a : Alphabet) : card (monos_with a) = 24 - a.val := by
  rw [@card_congr _ _ (monos_with a) (ord_from a) (monos_to_interval a)]
  . rw [← @card_image_of_injective _ _ (fun x ↦ x.val) _ _ (by decide)]
    rw [ord_from_eq_Ioo a]
    simp only [gt_iff_lt, not_lt, ge_iff_le, Nat.card_Ioo, tsub_le_iff_right]
    exact tsub_right_comm
  . intro p hp
    unfold monos_to_interval ord_from
    unfold monos_with at hp
    rw [mem_filter] at *
    simp_rw [mem_univ, true_and] at *
    rw [← hp.2]
    exact hp.1
  . intro p q hp hq h
    apply Prod.ext _ h
    rw [mono_first a p hp, mono_first a q hq]
  . intro b h
    unfold monos_with monos_to_interval
    simp_rw [ord_from, mem_filter, mem_univ, true_and] at h
    use (a, b)
    simp [h]
  done

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro1 : card monograms = 300 := by
  rw [← union_monos_with_eq_monograms, card_disjiUnion]
  simp_rw [monos_card]
  done
