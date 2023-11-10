import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic

open SimpleGraph
open Finset
open Nat
open BigOperators

/-!
# Intro 38 (pp.47-48)

There are 2n people at a party. Each person has an even number of friends at the
party. (Here, friendship is a mutual relationship.) Prove that there are two
people who have an even number of common friends at the party.

## Solution Sketch

Suppose that every pair of distinct people share an odd number of friends, and
consider the set A of friends of some person p, and let B be the set of everyone
else (excluding p). It follows that |B| is odd since |A| is even and A, B, and
{p} partition V. Then, for each person q in B, q is not friends with p by the
construction of B, and the number of friends of q in common with p is odd by
assumption, so q has an odd number of friends in A, and hence also has an odd
number of friends in B, since every person has an even number of friends. Now,
the sum of the number of friends in B over all q's in B is twice the number of
friends amongst people in B by Euler's handshaking lemma, contradicting that |B|
is odd.

-/

instance : Membership ℕ (Finset ℕ) := by
  exact instMembershipFinset
  done

noncomputable
instance {V : Finset ℕ} {G : SimpleGraph V} {v : V}
  : Fintype (SimpleGraph.neighborSet G v) :=
    Fintype.ofFinite ↑(SimpleGraph.neighborSet G v)


lemma V_partition (V : Finset ℕ) (G : SimpleGraph V)
  : ∀(p : V), card ((V.attach.erase p \ G.neighborFinset p) ∪
  G.neighborFinset p ∪ {p}) = card V := by
  sorry
  done

--def A_set {V : Finset ℕ} {G : SimpleGraph V} (p:V) : Finset {x // x ∈ V} := G.neighborFinset p

lemma ree (n : ℕ): n % 2 ≠ 0 ↔ n % 2 = 1 := by
  simp


theorem intro38 {V : Finset ℕ} (n : ℕ) (G : SimpleGraph V) (b : n≥1)
  (h : ∀(v:V), G.degree v % 2 = 0) (c : V.card = 2*n)
  : ∃(a b : V), (card (G.neighborFinset a ∩ G.neighborFinset b) % 2 = 0) := by
  by_contra g
  push_neg at g
  -- A := N(p)
  have h₀ : ∀(p : V), (card $ G.neighborFinset p) % 2 = 0 := h
  have h₁ : ∀(p : V), (card $ V.attach.erase p) % 2 = 1 := by
    simp
    intro a _
    rw [c, ← odd_iff]
    unfold Odd
    use n-1
    match n with
    | 0   => contradiction
    | k+1 => rw [mul_add]; simp
    done
  --B := (V ∖ {p}) ∖ A
  have h₂ : ∀(p : V), (card $ V.attach.erase p \ G.neighborFinset p) % 2 = 1 := by
    intro p
    rw [card_sdiff]
    . simp
      rw [c, ← odd_iff]
      unfold Odd
      use (degree G p)-1
      match n with
      | 0   => contradiction
      | k+1 => sorry
    . intro x
      simp
      exact fun a ↦ Adj.ne (id (adj_symm G a))
  have h₃ : ∀(p q : V), q ∈ (V.attach.erase p \ G.neighborFinset p)
    → ¬G.Adj p q := by
    simp
  have h₄ : ∀(p q : V), q ∈ (V.attach.erase p \ G.neighborFinset p)
    → card (G.neighborFinset q ∩ G.neighborFinset p) % 2 = 1 := by
    exact fun p q a ↦ (fun n ↦ (ree n).mp) (card (neighborFinset G q ∩ neighborFinset G p)) (g q p)
    done
  have h₅ : ∀(p q : V), q ∈ (V.attach.erase p \ G.neighborFinset p)
    → card (G.neighborFinset q ∩ (V.attach.erase p \ G.neighborFinset p)) % 2 = 1
    := by
    sorry
    done
  /-
  have h₆ : ∀(p : V), ∑ q in V.attach.erase p \ G.neighborFinset p,
    card(G.neighborFinset q ∩ (V.attach.erase p \ G.neighborFinset p))
    = 2 * ∑ v in V.attach.erase p \ G.neighborFinset p, card(G.neighborFinset v)
    := by
    sorry
    done
  -/
  done
