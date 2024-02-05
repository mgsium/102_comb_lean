import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Order.Partition.Finpartition

open Finset Nat SimpleGraph

/-!
# Intro 6 (p. 19)
Twenty five boys and twenty five girls sit around a table. Prove that it is
always possible to find a person both of whose neighbors are girls.

## Solution
Using a variant of solution 2 given in the text, we represent the 50 children
as a graph on 50 vertices, where two children are connected if there is
exactly one other child sitting between them. It is easy to see that this is
the graph G = C_25 + C_25. A seating arrangement where no two girls are connected
corresponds to an independent set of size 25 in the this graph. But the
independence number of C_25 + C_25 is ≤ 24, so no such arrangement exists.
-/

--------------------------------------------------------------------------------
---| SETUP : GRAPH UNION |------------------------------------------------------
--------------------------------------------------------------------------------

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
variable [instDecidableGAdj : DecidableRel G.Adj]

variable {β : Type*} [Fintype β] [DecidableEq β] (H : SimpleGraph β)
variable [instDecidableHAdj : DecidableRel H.Adj]

-- Define the union of two simple graphs
def union : SimpleGraph (α ⊕ β) := fromRel rel
  where rel (u v : α ⊕ β) :=
        if h : u.isLeft ∧ v.isLeft then G.Adj (u.getLeft h.1) (v.getLeft h.2)
        else if h : u.isRight ∧ v.isRight then H.Adj (u.getRight h.1) (v.getRight h.2)
        else false

-- The adjacency relation of a graph G + H is decidable if G.Adj and H.Adj
-- are each decidable
instance instDecidableUnionRel {a b : α ⊕ β} : Decidable (union.rel G H a b) :=
  instDecidableDitePropNot

instance : DecidableRel (union G H).Adj := fun _ _ ↦ And.decidable

--------------------------------------------------------------------------------
---| SETUP : INDEPENDENT SETS |-------------------------------------------------
--------------------------------------------------------------------------------

@[simp]
abbrev isIndSet (k : ℕ) (S : Finset α) : Prop :=
  k ≤ S.card ∧ ∀ (u v : S), ¬G.Adj u v

def hasIndSet (k : ℕ) : Prop :=
  ∃ (S : Finset α), isIndSet G k S

abbrev indSets := filter (fun x => isIndSet G x.card x) univ

-- The size of a maximum independent set in a graph
def independenceNumber : ℕ := sup (indSets G) card

-- The empty set is always an independent set
lemma instNonemptyIndSets : Finset.Nonempty (indSets G) := by
  use ∅ ; simp

-- An independent set in G + H restricted to its vertices in G
-- is an independent set in G
lemma sum_iset_image_left (X : Finset (α ⊕ β)) (h : X ∈ indSets (union G H))
  : filterMap Sum.getLeft? X (by simp_all) ∈ indSets G := by
    simp only [isIndSet, le_refl, Subtype.forall, true_and, mem_univ,
      mem_filter, mem_filterMap, Sum.getLeft?_eq_some_iff, exists_eq_right]
    intro a ha b hb
    simp only [isIndSet, le_refl, Subtype.forall, true_and,mem_filter, mem_univ] at h
    have h := h _ ha _ hb
    unfold union union.rel at h
    simp only [fromRel_adj, ne_eq, Sum.inl.injEq] at h
    by_cases h' : a = b
    . rw [h'] ; exact SimpleGraph.irrefl G
    . tauto
    done

-- An independent set in G + H restricted to its vertices in H
-- is an independent set in H
lemma sum_iset_image_right (X : Finset (α ⊕ β)) (h : X ∈ indSets (union G H))
  : filterMap Sum.getRight? X (by simp_all) ∈ indSets H := by
    simp only [isIndSet, le_refl, Subtype.forall, true_and, mem_univ,
      mem_filter, mem_filterMap, Sum.getRight?_eq_some_iff, exists_eq_right]
    intro a ha b hb
    simp only [isIndSet, le_refl, Subtype.forall, true_and,mem_filter, mem_univ] at h
    have h := h _ ha _ hb
    unfold union union.rel at h
    simp only [fromRel_adj, ne_eq, Sum.inr.injEq] at h
    by_cases h' : a = b
    . rw [h'] ; exact SimpleGraph.irrefl H
    . tauto
    done

lemma card_mapFilter_getLeft?_eq_filter_isLeft (X : Finset (α ⊕ β)) :
  card (filter (Sum.isLeft ·) X) = card (filterMap Sum.getLeft? X (by simp_all)) := by
  apply card_congr (fun x hx => x.getLeft (mem_filter.mp hx).2) <;> simp_all

lemma card_mapFilter_getRight?_eq_filter_isRight (X : Finset (α ⊕ β)) :
  card (filter (Sum.isRight ·) X) = card (filterMap Sum.getRight? X (by simp_all)) := by
  apply card_congr (fun x hx => x.getRight (mem_filter.mp hx).2) <;> simp_all

-- The independence number of a union is at most the sum of the separate
-- independence numbers.
lemma independence_number_add_le
  : independenceNumber (union G H) ≤ independenceNumber G + independenceNumber H := by
  unfold independenceNumber
  have : ∃ S ∈ indSets (union G H), sup (indSets (union G H)) card = S.card := by
    apply Finset.exists_mem_eq_sup _ (instNonemptyIndSets (union G H))
  let ⟨x, h, h'⟩ := this
  rw [h', ← filter_union_filter_neg_eq (Sum.isLeft ·) x]
  simp_rw [Sum.not_isLeft]
  apply Nat.le_trans (card_union_le _ _)
  apply Nat.add_le_add
  . rw [card_mapFilter_getLeft?_eq_filter_isLeft]
    apply le_sup (sum_iset_image_left G H x h)
  . rw [card_mapFilter_getRight?_eq_filter_isRight]
    apply le_sup (sum_iset_image_right G H x h)
  done

--------------------------------------------------------------------------------
---| OTHER SETUP & INTERMEDIATE LEMMAS |----------------------------------------
--------------------------------------------------------------------------------

-- Definition of a cycle graph
@[simp]
def cycleGraph (n : ℕ) : SimpleGraph (ZMod n) := fromRel (fun u v ↦ v = u + 1)
 -- where rel (u v : ZMod n) := v = u + 1

instance {n : ℕ} : DecidableRel (cycleGraph n).Adj := fun _ _ ↦ And.decidable

-- The neighborhood of a vertex v in a 25-cycle is the two-element
-- set { v - 1, v + 1 }
lemma cycle25_neighborFinset_eq {v : ZMod 25}
  : neighborFinset (cycleGraph 25) v = { v - 1, v + 1 } := by
  ext a
  simp_rw [mem_neighborFinset, cycleGraph, fromRel_adj]
  simp only [← @sub_eq_iff_eq_add _ _ v 1 a, ne_eq, mem_singleton, mem_insert]
  rw [@eq_comm _ (v - 1) a, or_comm]
  apply and_iff_right_of_imp
  intro h
  by_contra h'
  rw [h', eq_comm, sub_eq_self] at h
  simp only [self_eq_add_right] at h

-- A 25-cycle is a 2-regular graph
lemma cycle25_deg_eq {v : ZMod 25}
  : SimpleGraph.degree (cycleGraph 25) v = 2 := by
  unfold SimpleGraph.degree
  rw [cycle25_neighborFinset_eq, card_insert_of_not_mem, card_singleton]
  rw [mem_singleton]
  ring_nf
  simp only [add_left_inj]

-- The number of edges in a 25-cycle is 25
lemma cycle25_edges
  : card (SimpleGraph.edgeFinset $ cycleGraph 25) = 25 := by
  suffices h : 2 * card (SimpleGraph.edgeFinset $ cycleGraph 25) = 50
  . have : 50 = 2 * 25 := by norm_num
    rw [this, mul_eq_mul_left_iff] at h
    norm_num at h
    exact h
  . rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
    trivial
  done

-- The incidence finsets of any two vertices in an independent set
-- are pairwise disjoint
lemma pairwise_disj_indset_incset (X : Finset α) (hx : isIndSet G X.card X)
  : Set.PairwiseDisjoint X (G.incidenceFinset ·) := by
  unfold Set.PairwiseDisjoint Function.onFun
  intro a ha b hb g
  rw [disjoint_iff_ne]
  intro z hz y hy
  simp_rw [@SimpleGraph.mem_incidenceFinset _ _ _ ?_ _ _] at hz hy
  suffices g : G.incidenceSet a ∩ G.incidenceSet b = ∅
  . by_contra g'
    rw [g'] at hz
    have g'' := Set.mem_inter hz hy
    rw [g] at g''
    exact g''
  . apply SimpleGraph.incidenceSet_inter_incidenceSet_of_not_adj _ _ g
    simp only [isIndSet, le_refl, Subtype.forall, true_and] at hx
    exact hx a ha b hb
  done

-- Counting argument :
-- * union of disjoint incidence sets in an  independent set can have
--   cardinality at most 25 (the number of edges in the graph)
-- * ... but this has cardinality 26 (disjoint union of 13 terms, where
---  each term is of cardinality 2)
lemma indep_num_25cycle_le : independenceNumber (cycleGraph 25) ≤ 12 := by
  unfold independenceNumber indSets isIndSet
  rw [Finset.sup_le_iff]
  simp_rw [mem_filter, mem_univ, true_and]
  intro X hx
  by_contra g
  simp only [not_le] at g
  let NU := disjiUnion X (SimpleGraph.incidenceFinset (cycleGraph 25) ·) ?_
  have h : card NU ≤ card (SimpleGraph.edgeFinset $ cycleGraph 25) := by
    apply card_le_of_subset
    simp_rw [SimpleGraph.incidenceFinset_eq_filter]
    simp
  have h2 : 26 ≤ card NU := by
    rw [card_disjiUnion]
    . simp_rw [card_incidenceFinset_eq_degree, cycle25_deg_eq]
      simp only [sum_const, smul_eq_mul]
      linarith
    . exact pairwise_disj_indset_incset (cycleGraph 25) X hx
    done
  rw [cycle25_edges] at h
  exact le_lt_antisymm h h2
  done

--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro6
  : independenceNumber (union (cycleGraph 25) (cycleGraph 25)) ≤ 24 := by
  apply Nat.le_trans (independence_number_add_le _ _)
  rw [← Nat.two_mul]
  exact Nat.mul_le_mul_left 2 indep_num_25cycle_le
