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

universe u_1 u_2

lemma even_sdiff_even {α : Type u_1} [DecidableEq α] (A B : Finset α) (h : B ⊆ A)
  (h₁ : Even A.card) (h₂ : Even B.card) : Even (card $ A \ B) := by
  rw [card_sdiff]
  . refine Even.tsub h₁ h₂
  . exact h
  done

lemma odd_pred {n: ℕ} (h: 1 ≤ n) (g : Even n) : Odd (n - 1) := by
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

lemma odd_sub_even {a b : ℕ} (ha : Odd a) (hb : Even b) (h : b ≤ a)
  : Odd (a - b) := by
  exact Nat.Odd.sub_even h ha hb
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

example (A B C : Finset ℕ) (hb : B ⊆ A) (hc : C ⊆ A)
  : Disjoint (A ∩ B) (A ∩ C) ↔ Disjoint B C := by
  repeat rw [disjoint_iff_inter_eq_empty]
  rw [inter_eq_right.mpr hb, inter_eq_right.mpr hc]
  done

lemma even_iff_eq_nat_mul_two { n m : ℕ } (h : m = 2 * n) : Even m := by
  use n
  rw [← two_mul]
  exact h
  done

def closed_neighborFinset {V : Type u_1} [DecidableEq V] (G : SimpleGraph V)
  (v : V) [Fintype ↑(SimpleGraph.neighborSet G v)] : Finset V :=
    insert v (G.neighborFinset v)

lemma card_closed_neighborFinset_eq_add_one {V : Type u_1} [DecidableEq V]
  (G : SimpleGraph V) (v : V) [Fintype ↑(SimpleGraph.neighborSet G v)]
  : card (closed_neighborFinset G v) = G.degree v + 1 := by
    unfold closed_neighborFinset
    rw [card_insert_of_not_mem (not_mem_neighborFinset_self G v)]
    rw [card_neighborFinset_eq_degree]
    done

example { a b c : ℕ } (h : b + 1≤ c) (h2 : a ≤ b) : a + 1 ≤ c := by
  exact add_le_of_add_le_right h h2
  done

example { a b c : ℕ } (h : a ≤ b) (h2: b < c) : a < c := by
  exact Nat.lt_of_le_of_lt h h2
  done

-- The cardinality of a closed neighbourhood is at most the cardinality
-- of the vertex set.
theorem card_closed_nh_le_card_verts { V : Type u_2 } (G : SimpleGraph V)
  (v : V) [Fintype V] [DecidableRel G.Adj] [Nonempty V] [DecidableEq V]
  : card (closed_neighborFinset G v) ≤ Fintype.card V := by
  rw [card_closed_neighborFinset_eq_add_one]
  rw [← lt_iff_add_one_le]
  exact lt_of_le_of_lt (degree_le_maxDegree G v) (maxDegree_lt_card_verts G)
  done

-- Main Theorem
theorem intro38 {V : Finset ℕ } (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
  [nei: Nonempty V] (hdeg : ∀ (v : V), Even (G.degree v) ) (c : V.card = 2 * n)
  : ∃(a b : V), Even (card (G.neighborFinset a ∩ G.neighborFinset b)) := by
  by_contra g
  push_neg at g

  -- A := N(p)
  -- ???

  -- We have an even number of vertices
  have V_even : Even $ card V := even_iff_eq_nat_mul_two c
  have card_V_gt_zero : 0 < card V := by
    simp only [card_pos]
    exact nonempty_coe_sort.mp nei
    done

  have V_take_vertex_even : ∀ (p : V), Odd (card $ V.attach.erase p) := by
    simp only [mem_attach, card_erase_of_mem, card_attach]
    intro v
    apply odd_pred
    linarith
    exact V_even
    done

  -- B := (V ∖ {p}) ∖ A
  have V_take_open_nh_even
    : ∀(p : V), Even (card $ V.attach \ G.neighborFinset p) := by
    intro p
    rw [card_sdiff]
    . simp only [card_attach]
      refine Even.tsub V_even ?_
      rw [card_neighborFinset_eq_degree]
      exact hdeg p
    . intro x
      simp only [mem_neighborFinset, mem_attach, implies_true]
    done

  -- Closed neighborhood has even cardinality
  have closed_nh_even (p : V) : Odd (card $ closed_neighborFinset G p) := by
    rw [card_closed_neighborFinset_eq_add_one G p]
    exact Even.add_one (hdeg p)
    done

  -- Vertex set is non-empty
  have : Finset.Nonempty V := by {rw [← card_pos, c]; exact succ_mul_pos 1 b}
  have : Nonempty V := Set.Nonempty.coe_sort this

  -- cardinality of B is odd
  have V_take_closed_nh_odd
    : ∀(p : V), Odd (card $ (V.attach \ closed_neighborFinset G p)) := by
    intro p
    rw [card_sdiff, card_attach]
    apply Nat.Even.sub_odd _ V_even (closed_nh_even p)
    rw [← Fintype.subtype_card V (λ x ↦ Iff.rfl)]
    exact card_le_univ (closed_neighborFinset G p)
    unfold closed_neighborFinset
    apply insert_subset
    . exact mem_attach V p
    . rw [subset_iff]
      intro x hₓ
      exact mem_attach V x
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
    done
  have disjoint_lemma : ∀(p q : V), Disjoint
    (G.neighborFinset q ∩ G.neighborFinset p)
    (G.neighborFinset q ∩ (V.attach \ G.neighborFinset p).erase p) := by

    done

  -- degree of q in B is odd
  have h₅ : ∀(p q : V), q ∈ (V.attach \ G.neighborFinset p).erase p
    → Odd (card (G.neighborFinset q ∩ (V.attach \ G.neighborFinset p).erase p))
    := by
    intro p q
    simp only [mem_sdiff, mem_attach, mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true,
      and_self, not_true, mem_erase, ne_eq, true_and, and_imp]





    contrapose
    push_neg
    simp_rw [ne_one_iff_eq_zero_mod_two]

    done

  have h₆ : ∀(p : V), ∑ q in (V.attach.erase p \ G.neighborFinset p),
    card  (G.neighborFinset q ∩ (V.attach.erase p \ G.neighborFinset p))
    -- = 2 -- number of edges in subgraph (V.attach.erase p \ G.neighborFinset p)
    % 2 = 0 := by
     sorry
     done

  done
