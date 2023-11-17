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

--lemma odd_sum_odd (n : ℕ)



lemma odd_pred {n : ℕ} (h: 1 ≤ n) (g : Even n) : Odd (n - 1) := by
  match n with
  | 0   => contradiction
  | k+1 =>
    unfold Even at g
    cases g with | intro r g =>
      rw [add_tsub_cancel_right, odd_iff_not_even]
      by_contra h'
      have : Even (k+1) := by
        unfold Even
        use r
        done
      have : ¬Even (k+1) := by
        rw [← odd_iff_not_even]
        apply Even.add_odd
        . exact h'
        . trivial
        done
      contradiction
  done

lemma ne_zero_iff_eq_one_mod_two (n : ℕ): n % 2 ≠ 0 ↔ n % 2 = 1 := by
  simp

lemma ne_one_iff_eq_zero_mod_two (n : ℕ): n % 2 ≠ 1 ↔ n % 2 = 0 := by
  simp

lemma neg_two_plus_one (k : ℕ) (h₁ : k > 1) :
  k - 1 = k - 2 + 1 := by
  cases' k with d
  · contradiction
  · simp
    have h₂ : 0 < d := by linarith
    exact Nat.eq_add_of_sub_eq h₂ rfl
    done

example (A B C : Finset ℕ) (ha : B ⊆ A) (hc : C ⊆ A) : Disjoint (A∩B) (A∩C) ↔ Disjoint B C := by
  constructor
  . intro h
    rw [disjoint_iff_inter_eq_empty] at *

  . sorry
  done



universe u_1

lemma even_sdiff_even {α : Type u_1} [DecidableEq α] (A B : Finset α) (h : B ⊆ A)
  (h₁ : Even A.card) (h₂ : Even B.card) : Even (card $ A \ B) := by
  rw [card_sdiff]
  . refine Even.tsub h₁ h₂
  . exact h
  done

theorem intro38 {V : Finset ℕ} (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (b : n≥1)
  (h : ∀(v:V), Even (G.degree v) ) (c : V.card = 2*n)
  : ∃(a b : V), (card (G.neighborFinset a ∩ G.neighborFinset b) % 2 = 0) := by
  by_contra g
  push_neg at g
  simp_rw [ne_zero_iff_eq_one_mod_two] at g
  -- A := N(p)
  have V_even : Even $ card V := by
    unfold Even
    use n
    rw [← two_mul]
    exact c
  have h₀ : ∀(p : V), Even (card $ G.neighborFinset p) := h
  have h₁ : ∀(p : V), Odd (card $ V.attach.erase p) := by
    simp only [mem_attach, card_erase_of_mem, card_attach, ge_iff_le, Subtype.forall]
    intro a _
    rw [c]
    unfold Odd
    use n-1
    match n with
    | 0   => contradiction
    | k+1 => rw [mul_add]; simp
    done
  --B := (V ∖ {p}) ∖ A
  have even_lemma : ∀(p : V), Even (card $ V.attach \ G.neighborFinset p) := by
    intro p
    rw [card_sdiff]
    . simp only [card_attach]
      refine Even.tsub V_even (h p)
    . intro x
      simp only [mem_neighborFinset, mem_attach, implies_true]
  -- cardinality of B is odd
  have h₂ : ∀(p : V), Odd (card $ (V.attach \ G.neighborFinset p).erase p) := by
    intro p
    simp only [mem_sdiff, mem_attach, mem_neighborFinset, SimpleGraph.irrefl, card_erase_of_mem]
    refine odd_pred ?_ (even_lemma p)
    by_contra k
    simp only [not_le, lt_one_iff, card_eq_zero, sdiff_eq_empty_iff_subset] at k
    rw [Finset.subset_iff] at k
    have k₂: p ∈ attach V ∧ p ∉ neighborFinset G p := by
      constructor
      . simp only [mem_attach]
      . simp only [mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true]
      done
    simp_rw [imp_iff_not_or] at k
    have k₃: ¬p ∈ attach V ∨ ¬¬p ∈ neighborFinset G p := by
      simp only [not_not]
      exact @k p
      done
    rw [← not_and_or] at k₃
    contradiction
    done
  -- vertices in B are not adjacent to p
  have h₃ : ∀(p q : V), q ∈ (V.attach\ G.neighborFinset p).erase p
    → ¬G.Adj p q := by
    simp only [mem_sdiff, mem_attach, mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true,
      and_self, not_true, mem_erase, ne_eq, true_and, and_imp, imp_self, implies_true,
      Subtype.forall, forall_const]
    done
  -- degree of q in A is odd
  have h₄ : ∀(p q : V), q ∈ (V.attach \ G.neighborFinset p).erase p
    → card (G.neighborFinset q ∩ G.neighborFinset p) % 2 = 1 := by
    exact fun p q _ ↦ g q p
    -- exact fun p q a ↦ (fun n ↦ (ne_zero_iff_eq_one_mod_two n).mp) (card (neighborFinset G q ∩ neighborFinset G p)) (g q p)
    done
  have disjoint_lemma : ∀(p q : V), Disjoint
    (G.neighborFinset q ∩ G.neighborFinset p)
    (G.neighborFinset q ∩ (V.attach \ G.neighborFinset p).erase p) := by

    done
  -- degree of q in B is odd
  have h₅ : ∀(p q : V), q ∈ (V.attach \ G.neighborFinset p).erase p
    → card (G.neighborFinset q ∩ (V.attach \ G.neighborFinset p).erase p)
    % 2 = 1 := by
    intro p q
    simp only [mem_sdiff, mem_attach, mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true,
      and_self, not_true, mem_erase, ne_eq, true_and, and_imp]





    contrapose
    push_neg
    simp_rw [ne_one_iff_eq_zero_mod_two]

    done

  have h₆ : ∀(p : V), ∑ q in (V.attach.erase p \ G.neighborFinset p),
    card (G.neighborFinset q ∩ (V.attach.erase p \ G.neighborFinset p))
    -- = 2 * -- number of edges in subgraph (V.attach.erase p \ G.neighborFinset p)
    % 2 = 0 := by
     sorry
     done

  done
