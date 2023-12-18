import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Partition.Finpartition

open Finset

/-!
# Intro 6 (p. 19)
Twenty five boys and twenty five girls sit around a table. Prove that it is
always possible to find a person both of whose neighbors are girls.

## Solution
...
-/

section SNGraph

abbrev SNGraph (n : ℕ) := SimpleGraph (range n)

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
variable [instDecidableGAdj : DecidableRel G.Adj]

variable {β : Type*} [Fintype β] [DecidableEq β] (H : SimpleGraph β)
variable [instDecidableHAdj : DecidableRel H.Adj]

def union {α β : Type*} [Fintype α] [Fintype β] (G : SimpleGraph α)
  (H : SimpleGraph β) : SimpleGraph (α ⊕ β) := SimpleGraph.fromRel rel
  where rel (u v : α ⊕ β) :=
        if h : u.isLeft ∧ v.isLeft then G.Adj (u.getLeft h.1) (v.getLeft h.2)
        else if h : u.isRight ∧ v.isRight then H.Adj (u.getRight h.1) (v.getRight h.2)
        else false

instance instDecidableUnionRel {a b : α ⊕ β} : Decidable (union.rel G H a b) :=
  instDecidableDitePropNot

instance instDecidableRelUnionRel : DecidableRel (union.rel G H) :=
  fun _ _ ↦ instDecidableUnionRel G H

instance instDecidableRelUnionAdj : DecidableRel (union G H).Adj := by
  unfold union SimpleGraph.fromRel
  intro a b
  simp only [ne_eq]
  apply And.decidable


@[simp]
abbrev isIndSet (k : ℕ) (S : Finset α) : Prop :=
  k ≤ S.card ∧ ∀ (u v : S), ¬G.Adj u v

def hasIndSet (k : ℕ) : Prop :=
  ∃ (S : Finset α), isIndSet G k S

abbrev indSets := filter (fun x => isIndSet G x.card x) univ

def independenceNumber : ℕ := sup (indSets G) card

lemma instNonemptyIndSets : Finset.Nonempty (indSets G) := by
  use ∅ ; simp

instance : DecidableRel (union G H).Adj := by
    unfold union SimpleGraph.fromRel
    intro a b
    simp only [ne_eq]
    refine @And.decidable _ _ _ ?_
    refine @Or.decidable _ _ ?_ ?_
    <;> exact instDecidableUnionRel G H
    done

lemma exists_iset_iff {k : ℕ} (h : 0 < k)
  : k ≤ independenceNumber G ↔ ∃ (S : Finset α), isIndSet G k S := by
  unfold independenceNumber isIndSet
  rw [Finset.le_sup_iff]
  simp_rw [mem_filter, mem_univ, true_and, isIndSet, Nat.le_refl, true_and, And.comm]
  exact h
  done

lemma subset_iset (X Y : Finset α) (h : Y ⊆ X) (h2 : X ∈ indSets G)
  : Y ∈ indSets G := by
    unfold indSets  at *
    simp only [isIndSet, le_refl, Subtype.forall,
      true_and, mem_univ, mem_filter] at *
    intro a ha b hb
    exact h2 a (h ha) b (h hb)

lemma getLeft?_inj (a a' : α ⊕ β) (b : α) (h : b ∈ Sum.getLeft? a)
  (h' : b ∈ Sum.getLeft? a') : a = a' := by
  simp only [Option.mem_def, Sum.getLeft?_eq_some_iff] at h h'
  rw [h, h']
  done

lemma getRight?_inj (a a' : α ⊕ β) (b : β) (h : b ∈ Sum.getRight? a)
  (h' : b ∈ Sum.getRight? a') : a = a' := by
  simp only [Option.mem_def, Sum.getRight?_eq_some_iff] at h h'
  rw [h, h']
  done

lemma sum_iset_image_left (X : Finset (α ⊕ β)) (h : X ∈ indSets (union G H)):
  filterMap Sum.getLeft? X getLeft?_inj ∈ indSets G := by
    simp only [isIndSet, le_refl, Subtype.forall, true_and, mem_univ,
      mem_filter, mem_filterMap, Sum.getLeft?_eq_some_iff, exists_eq_right]
    intro a ha b hb
    simp only [isIndSet, le_refl, Subtype.forall, true_and,mem_filter, mem_univ] at h
    have h := h _ ha _ hb
    unfold union union.rel at h
    simp only [SimpleGraph.fromRel_adj, ne_eq, Sum.inl.injEq] at h
    by_cases h' : a = b
    . rw [h'] ; exact SimpleGraph.irrefl G
    . tauto
    done

lemma sum_iset_image_right (X : Finset (α ⊕ β)) (h : X ∈ indSets (union G H)):
  filterMap Sum.getRight? X getRight?_inj ∈ indSets H := by
    simp only [isIndSet, le_refl, Subtype.forall, true_and, mem_univ,
      mem_filter, mem_filterMap, Sum.getRight?_eq_some_iff, exists_eq_right]
    intro a ha b hb
    simp only [isIndSet, le_refl, Subtype.forall, true_and,mem_filter, mem_univ] at h
    have h := h _ ha _ hb
    unfold union union.rel at h
    simp only [SimpleGraph.fromRel_adj, ne_eq, Sum.inr.injEq] at h
    by_cases h' : a = b
    . rw [h'] ; exact SimpleGraph.irrefl H
    . tauto
    done

lemma card_mapFilter_getLeft?_eq_filter_isLeft (X : Finset (α ⊕ β)) :
  card (filter (Sum.isLeft ·) X) = card (filterMap Sum.getLeft? X getLeft?_inj) := by
  apply card_congr (fun x hx => x.getLeft (mem_filter.mp hx).2)
  . intro a ha ; simp [mem_of_mem_filter a ha]
  . intro a ha ; simp
  . simp
  done

lemma card_mapFilter_getRight?_eq_filter_isRight (X : Finset (α ⊕ β)) :
  card (filter (Sum.isRight ·) X) = card (filterMap Sum.getRight? X getRight?_inj) := by
  apply card_congr (fun x hx => x.getRight (mem_filter.mp hx).2)
  . intro a ha ; simp [mem_of_mem_filter a ha]
  . intro a ha ; simp
  . simp
  done

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

@[simp]
def cycleGraph (n : ℕ) : SimpleGraph (range n) := SimpleGraph.fromRel rel
  where rel (u v : range n) := (u.val - v.val + 1) % n = 0

instance {n : ℕ} : DecidableRel (cycleGraph.rel n) := by
  unfold cycleGraph.rel
  intro a b
  simp only []
  exact Nat.decEq _ _
  done

instance : DecidableRel (cycleGraph 25).Adj := by
  unfold cycleGraph
  intro a b
  simp only [SimpleGraph.fromRel_adj, ne_eq]
  apply And.decidable

lemma indep_num_25cycle_le : independenceNumber (cycleGraph 25) ≤ 12 := by
  unfold independenceNumber
  unfold indSets isIndSet
  rw [Finset.sup_le_iff]
  simp_rw [mem_filter, mem_univ, le_refl, true_and]
  intro X hX
  sorry
  done

theorem intro6
  : independenceNumber (union (cycleGraph 25) (cycleGraph 25)) ≤ 24 := by
  apply Nat.le_trans (independence_number_add_le _ _)
  have : 24 = 2 * 12 := by norm_num
  rw [← Nat.two_mul, this]
  exact Nat.mul_le_mul_left 2 indep_num_25cycle_le
  done

end SNGraph
