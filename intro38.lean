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
else (excluding p) i.e. the complement of the closed neighbourhood of p. It
follows that |B| is odd since |A| is even and A, B, and {p} partition V. Then,
for each person q in B, q is not friends with p by the construction of B, and
the number of friends of q in common with p is odd by assumption, so q has an
odd number of friends in A, and hence also has an odd number of friends in B,
since every person has an even number of friends. Now, the sum of the number of
friends in B over all q's in B is twice the number of friendships amongst people
in B by Euler's handshaking lemma, contradicting that |B| is odd.

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

--noncomputable
--def A_set {V : Finset ℕ} {G : SimpleGraph V} (p:V) : Finset {x // x ∈ V} := G.neighborFinset p

lemma simp_mod_two (n : ℕ): n % 2 ≠ 0 ↔ n % 2 = 1 := by
  simp

lemma ne_one_iff_eq_zero_mod_two (n : ℕ): n % 2 ≠ 1 ↔ n % 2 = 0 := by
  simp

lemma odd_pred { n : ℕ } (h : 1 ≤ n) : Odd (2 * n - 1) := by
  match n with
  | 0 => contradiction
  | k + 1 => rw [two_mul]; norm_num
  done

lemma sub_even { a b : ℕ } (ha : Odd a) (hb : Even b)
  : Odd (a - b) := by
  match a with
  | 0 => contradiction
  | k + 1 =>
  done

theorem intro38 {V : Finset ℕ} (n : ℕ) (G : SimpleGraph V) (b : n≥1)
  (h : ∀(v:V), Even (G.degree v) ) (c : V.card = 2*n)
  : ∃(a b : V), (card (G.neighborFinset a ∩ G.neighborFinset b) % 2 = 0) := by
  by_contra g
  push_neg at g
  simp_rw [ne_zero_iff_eq_one_mod_two] at g
  -- A := N(p)
  have h₀ : ∀(p : V), Even (card $ G.neighborFinset p) := h
  have h₁ : ∀(p : V), Odd (card $ V.attach.erase p) := by
    sorry
    -- simp
    -- intro a _
    -- rw [c, ← odd_iff]
    -- unfold Odd
    -- use n-1
    -- match n with
    -- | 0   => contradiction
    -- | k+1 => rw [mul_add]; simp
    done
  --B := (V ∖ {p}) ∖ A
  have h₂ : ∀(p : V), Odd (card $ V.attach.erase p \ G.neighborFinset p) := by
    intro p
    unfold Odd
    rw [card_sdiff]
    . simp only [mem_attach, card_erase_of_mem, card_attach,
      card_neighborFinset_eq_degree]
      rw [c]
      have g₂ : Even (degree G p) := h p
      unfold Even at g₂

      cases g₂ with
      | intro r k =>
        use (n - r - 1)
        rw [k]

      rw [← even_iff] at this
      unfold Even at this
      let r := Classical.choose this
      unfold Odd
      use (n - r - 1)

      exact @Odd.sub_even (odd_pred b) g₂
    . intro x
      simp only [mem_neighborFinset, mem_attach, mem_erase, and_true]
      exact Adj.ne'
  have h₃ : ∀(p q : V), q ∈ (V.attach.erase p \ G.neighborFinset p)
    → ¬G.Adj p q := by simp only [mem_sdiff, mem_neighborFinset, and_imp,
    imp_self, implies_true]
  have h₄ : ∀(p q : V), q ∈ (V.attach.erase p \ G.neighborFinset p)
    → card (G.neighborFinset q ∩ G.neighborFinset p) % 2 = 1 := by
    exact fun p q _ ↦ g q p
    done
  have h₅ : ∀(p q : V), q ∈ (V.attach.erase p \ G.neighborFinset p)
    → card (G.neighborFinset q ∩ (V.attach.erase p \ G.neighborFinset p))
    % 2 = 1 := by
    intro p q
    simp only [mem_attach, mem_sdiff, mem_erase, and_true, mem_neighborFinset]





    contrapose
    rw [not_and_or]
    push_neg
    simp_rw [ne_one_iff_eq_zero_mod_two]
    sorry
    done

  have h₆ : ∀(p : V), ∑ q in (V.attach.erase p \ G.neighborFinset p),
    card  (G.neighborFinset q ∩ (V.attach.erase p \ G.neighborFinset p))
    -- = 2 -- number of edges in subgraph (V.attach.erase p \ G.neighborFinset p)
    % 2 = 0 := by
     sorry
     done

  done
