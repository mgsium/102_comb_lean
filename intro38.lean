import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Card

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

universe u_1

--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------

lemma even_sdiff_even {α : Type u_1} [DecidableEq α] (A B : Finset α) (h : B ⊆ A)
  (h₁ : Even A.card) (h₂ : Even B.card) : Even (card $ A \ B) := by
  rw [card_sdiff] <;> simp only [h, Even.tsub h₁ h₂]
  done

@[simp]
lemma even_iff_eq_nat_mul_two { n : ℕ } : (∃ m, n = 2 * m) ↔ Even n := by
  simp_rw [two_mul]
  exact Iff.rfl
  done

def closed_neighborFinset {V : Type u_1} [DecidableEq V] (G : SimpleGraph V)
  (v : V) [Fintype ↑(SimpleGraph.neighborSet G v)] : Finset V :=
    insert v (G.neighborFinset v)

lemma card_closed_neighborFinset_eq_deg_add_one {V : Type u_1} [DecidableEq V]
  (G : SimpleGraph V) (v : V) [Fintype (SimpleGraph.neighborSet G v)]
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
theorem card_closed_nh_le_card_verts { V : Type u_1 } (G : SimpleGraph V)
  (v : V) [Fintype V] [DecidableRel G.Adj] [Nonempty V] [DecidableEq V]
  : card (closed_neighborFinset G v) ≤ Fintype.card V := by
  rw [card_closed_neighborFinset_eq_deg_add_one]
  rw [← lt_iff_add_one_le]
  exact lt_of_le_of_lt (degree_le_maxDegree G v) (maxDegree_lt_card_verts G)
  done

@[simp]
lemma nh_subset_closed_nh { V : Type u_1 } (G : SimpleGraph V)
  (v : V) [Fintype V] [DecidableRel G.Adj] [DecidableEq V]
  : neighborFinset G v ⊆ closed_neighborFinset G v := subset_insert _ _

@[simp]
lemma inter_sdiff_super {α : Type u_1} [DecidableEq α] (A B C : Finset α)
    (h : B ⊆ C) : B ∩ (A \ C) = ∅ := by
    rw [inter_sdiff, sdiff_eq_empty_iff_subset]
    exact subset_trans (inter_subset_left B A) h
    done

-- This is in mathlib, but my install can't find it??
@[simp]
lemma card_sdiff_add_card_inter {α : Type u_1} [DecidableEq α] (s t : Finset α) :
    (s \ t).card + (s ∩ t).card = s.card := by
  rw [← card_disjoint_union (disjoint_sdiff_inter _ _), sdiff_union_inter]

lemma one_leq_odd (x : ℕ) (h' : Odd x) : 1 ≤ x := by
    unfold Odd at h'
    cases' h' with r hr
    linarith

lemma sum_minus (X : Finset ℕ) (h: ∀ x ∈ X, x ≥ 1) :
    ∑ x in X, (x - 1) = ∑ x in X, x - ∑ x in X, 1 := by
  rw [eq_tsub_iff_add_eq_of_le (sum_le_sum h)]
  · rw [←sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    exact Nat.sub_add_cancel (h x hx)

lemma sum_odds (X : Finset ℕ) (h: Even X.card) (h': ∀ x ∈ X, Odd x)
    : Even (∑ k in X, k) := by
  unfold Even at *
  simp_rw [←mul_two]
  cases' h with r hr
  use ((∑ k in X, (k-1) / 2) + r)
  rw [right_distrib, sum_mul]
  have h'': ∀ (x : ℕ), x ∈ X → x ≥ 1 := by
    intros x hx
    specialize h' x hx
    exact one_leq_odd x h'
  have h: ∑ x in X, (x - 1) / 2 * 2 = ∑ x in X, (x - 1) := by
    apply sum_congr rfl
    intro x hx
    have h₁ : 2 ∣ (x - 1) := by
      specialize h' x hx
      apply even_iff_two_dvd.mp
      specialize h'' x hx
      cases' h' with r hr
      rw [hr]
      norm_num
    exact Nat.div_mul_cancel h₁
  rw [h, sum_minus X h'', ← card_eq_sum_ones X, hr, ← two_mul, mul_comm]
  apply Nat.eq_add_of_sub_eq _ rfl
  rw [← two_mul, mul_comm] at hr
  rw [← hr, card_eq_sum_ones X]
  exact sum_le_sum h''

def odd_elements (X : Finset ℕ) : Prop := ∀x∈X, Odd x

def sum_of_odd_prop (c : ℕ): Prop :=
  ∀(X : Finset ℕ), Odd c → X.card = c → odd_elements X → (Odd $ ∑ x in X, x)

def odd_set_card_odd_iff_sum_odd {V : Finset ℕ} (S : Finset V)
  { f : V → ℕ } :=
  (∀ x ∈ S, Odd $ f x) → (Odd (∑ s in S, f s) ↔ Odd S.card)

theorem sum_odd_odd {V : Finset ℕ} {f : V → ℕ} :
  ∀ (X: Finset V), @odd_set_card_odd_iff_sum_odd V X f := by
  apply Finset.induction
  . intro _
    rfl
  . intro x X h h' ha
    rw [sum_insert h, card_insert_of_not_mem h, odd_add, odd_add']
    have : Odd (f x) := (ha x) (mem_insert_self x X)
    simp only [true_iff, this]
    rw [← not_iff_not]
    repeat rw [← odd_iff_not_even]
    apply h'
    intro x hx
    exact (ha x) (mem_insert_of_mem hx)
  done

lemma inter_sdiff_empty_eq { A B C : Finset ℕ }
  (h : A ∩ (C \ B) = ∅ ) (h2 : B ⊆ C): A ∩ B = A ∩ C := by
  rw [← union_sdiff_of_subset h2, inter_distrib_left]
  simp only [h, union_empty]
  done

--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------
variable (V : Finset ℕ)
variable (G : SimpleGraph V)
variable (H : Subgraph G)

theorem intro38(n : ℕ) [DecidableRel G.Adj] [nei: Nonempty V]
  (hdeg : ∀ (v : V), Even (G.degree v) ) (c : V.card = 2 * n)
  : ∃(a b : V), Even (card (G.neighborFinset a ∩ G.neighborFinset b)) := by
  by_contra g
  push_neg at g

  -- A := N(p)
  let closed_nh_comp := λ v ↦ V.attach \ closed_neighborFinset G v

  -- We have an even number of vertices
  have V_even : Even V.card := by {simp_rw [← even_iff_eq_nat_mul_two]; use n}
  have card_V_gt_zero : 0 < card V := by
    simp only [card_pos]
    exact nonempty_coe_sort.mp nei
    done

  have V_take_vertex_even : ∀ (p : V), Odd (card $ V.attach.erase p) := by
    simp only [mem_attach, card_erase_of_mem, card_attach]
    intro v
    apply Nat.Even.sub_odd (by linarith) V_even odd_one
    done

  -- B := (V ∖ {p}) ∖ A
  have V_take_open_nh_even
    : ∀ (p : V), Even (card $ V.attach \ G.neighborFinset p) := by
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
    rw [card_closed_neighborFinset_eq_deg_add_one G p]
    exact Even.add_one (hdeg p)
    done

  -- Vertex set is non-empty
  have : Finset.Nonempty V := card_pos.mp card_V_gt_zero
  have : Nonempty V := Set.Nonempty.coe_sort this

  -- The cardinality of B is odd
  have V_take_closed_nh_odd
    : ∀ (p : V), Odd (card $ closed_nh_comp p) := by
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

  -- Vertices in B are not adjacent to p
  have h₃ : ∀(p q : V), q ∈ closed_nh_comp p → ¬G.Adj p q := by
    simp only [mem_sdiff, mem_attach, mem_neighborFinset, true_and]
    unfold closed_neighborFinset
    intro p q
    contrapose; simp only [not_not]
    rw [← mem_neighborFinset]
    exact mem_insert_of_mem
    done

  -- deg_A(q) is odd
  have h₄ : ∀(p q : V), q ∈ closed_nh_comp p
    → Odd (card (G.neighborFinset q ∩ neighborFinset G p))  := by
    exact fun p q _ ↦ (fun {n} ↦ odd_iff_not_even.mpr) (g q p)
    done
  -- ???


  have h₅ : ∀(p q : V), q ∈ closed_nh_comp p
    → Odd (card (G.neighborFinset q ∩ closed_neighborFinset G p)) := by
    intro p q h
    have temp : G.neighborFinset q ∩ (closed_neighborFinset G p \ {p}) = ∅ := by
      sorry
      done
    --apply inter_sdiff_empty_eq.symm ?_
    sorry
    done

  --
  have disjoint_lemma : ∀ (p q : V), Disjoint
    (G.neighborFinset q ∩ G.neighborFinset p)
    (G.neighborFinset q ∩ closed_nh_comp p) := by
    intro p q
    rw [disjoint_iff_inter_eq_empty, inter_left_comm]
    rw [inter_sdiff_super]
    exact inter_empty _
    apply subset_trans (inter_subset_right _ _)
    unfold closed_neighborFinset
    exact subset_insert _ _
    done

  have part_V_by_nh
    : ∀ (p : V), V.attach = closed_nh_comp p ∪ closed_neighborFinset G p := by
    simp only [sdiff_union_self_eq_union, left_eq_union]
    sorry --aesop_graph
    done

  have inter_eq_sdiff_comp_nh : ∀ (p q : V),
    neighborFinset G q \ closed_nh_comp p
    = neighborFinset G q ∩ closed_neighborFinset G p := by
    sorry --aesop_graph
    done

  -- example {α : Type u_1} [DecidableEq α] (s : Finset α) (t : Finset α) :
  --   s ∩ t = s \ (s \ t) := by
  --   exact (sdiff_sdiff_self_left s t).symm
  --   done

  -- deg_B(q) is odd
  have degree_in_B_odd : ∀(p q : V), q ∈ closed_nh_comp p
    → Odd (card (G.neighborFinset q ∩ closed_nh_comp p)) := by
    intro p q h
    rw [(sdiff_sdiff_self_left _ _).symm]
    rw [card_sdiff (sdiff_subset _ _)]
    apply Nat.Even.sub_odd _ (hdeg q) _
    . apply le_trans
      . exact Nat.le_add_right _ (card (neighborFinset G q ∩ closed_nh_comp p))
      . rw [card_sdiff_add_card_inter]
        exact Nat.le_refl _
    . rw [inter_eq_sdiff_comp_nh]
      exact h₅ p q h
    done

  -- The sum of the degrees of elements in B is odd
  have sum_of_B_elem_deg_odd : ∀(p : V), Odd (∑ q in closed_nh_comp p,
    (card (G.neighborFinset q ∩ closed_nh_comp p))) := by
    intro p
    rw [sum_odd_odd $ closed_nh_comp p]
    . exact V_take_closed_nh_odd p
    . intro q h
      exact degree_in_B_odd p q h
    done

  have sum_of_B_elem_deg_even : ∀(p : V),
    ¬Odd (∑ q in closed_nh_comp p, (card (G.neighborFinset q ∩ closed_nh_comp p))) := by
    intro p
    sorry
    done

  done
