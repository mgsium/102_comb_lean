import Mathlib.Tactic

/-!
# Intro 9 (p.3)
A drawer in a darkened room contains 100 red, 80 green, 60 blue, and 40 black
socks. The colours of the socks cannot be seen during section. What is the
smallest number of socks needed to be selected to guarantee that the selection
contains at least 10 pairs? (A pair of socks is two socks of the same colour. No
sock may be counted in more than one pair.)

## Solution

ree

-/

open Nat Finset Set BigOperators

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup

/-
We can encode a selection as

- Multiset colour, where colour is Fin 4, so the multiset cardinality is the
  size of the selection;
- a 4-tuple of naturals where each coordinate represents the number of objects
  of a given colour, so the sum of the coordinates is the size;
- a function from [n] to colour (:= Fin 4), where the image of each element is
  the colour and n is the size.

- Multisets are hard to work with, and I couldn't get pigeonhole principle to
  apply very easily.
- A selection is an integer partition, which are also hard to work with. Had
  similar problems with pigeonhole principle implementation.
- The number of socks of a given colour is the size of a preimage of a singleton
  in colour, but why do all the preimage functions in Mathlib require some
  injectivity conditions???
-/

abbrev colour := Fin 4
abbrev selection (s : ℕ) : Type := Fin s → colour

-- def count_pairs {s : ℕ} {f : selection s} : ℕ :=
--   ∑ x : colour, card (Finset.preimage {x} (selection s) hf) / 2

def myPreimage {α β : Type*} (s : Finset β) (f : α → β) (hf : Fintype α)
    [DecidablePred fun x => x ∈ f ⁻¹' ↑s] : Finset α :=
  @Set.toFinset _ (s.toSet.preimage f) (by apply Set.fintypeSubset (@Finset.univ α hf); simp)

def count_pairs {s : ℕ} {f : selection s} : ℕ :=
  ∑c : colour, card (@myPreimage (Fin s) (colour) (singleton c) f (by exact Fin.fintype s) (by sorry)) / 2

#check myPreimage

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas


end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

variable (n : ℕ) (S : selection n)

-- theorem intro9 : Multiset.card S = 23 → count_pairs S ≥ 10 := by
--   sorry
--   done
