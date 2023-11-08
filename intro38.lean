import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic

open SimpleGraph
open Finset
open Nat

/-!
# Intro 38 (pp.47-48)

There are 2n people at a party. Each person has an even number of friends at the
party. (Here, friendship is a mutual relationship.) Prove that there are two
people who have an even number of common friends at the party.

## Solution Sketch

Suppose that every pair of distinct people share an odd number of friends, and
consider the set A of friends of some person P, and let B be the set of everyone
else (excluding P). It follows that |B| is odd since |A| + |B| + 1 = 2n, and |A|
is even. Then, for

-/

noncomputable
instance {V : Finset ℕ} {G : SimpleGraph V} {v : V}
  : Fintype (SimpleGraph.neighborSet G v) :=
    Fintype.ofFinite ↑(SimpleGraph.neighborSet G v)

theorem intro38 {V : Finset ℕ} (n : ℕ) (G : SimpleGraph V)
  (h : ∀(v:V), G.degree v % 2 = 0) (c : V.card = 2 * n)
  : ∃(a b : V), ((G.neighborFinset a ∩ G.neighborFinset b).card % 2 = 0) := by
  sorry
  done
