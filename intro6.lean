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

#check SimpleGraph.mk

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

structure coPartition (k : ℕ) :=
  parts : Finset (Set α)
  ispart : Setoid.IsPartition parts.toSet
  isind : ∀ p ∈ parts, IsAntichain G.Adj p
  haskparts : parts.card = k

def coPartitionable (k : ℕ) : Prop := Nonempty (coPartition G k)

noncomputable
def independenceNumber : ℕ := sSup { n : ℕ | coPartitionable G n }

instance : DecidableRel (union G H).Adj := by
    unfold union SimpleGraph.fromRel
    intro a b
    simp only [ne_eq]
    refine @And.decidable _ _ _ ?_
    refine @Or.decidable _ _ ?_ ?_
    <;> exact instDecidableUnionRel G H
    done

lemma independence_number_add {α β : Type*} [Fintype α] [Fintype β]
  (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj]
  : independenceNumber (union G H) = independenceNumber G + independenceNumber H := by
  sorry
  done

def cycleGraph (n : ℕ) : SimpleGraph (range n) := SimpleGraph.fromRel rel
  where rel (u v : range n) := (u.val + 1) % n = v

theorem intro6 : independenceNumber (union (cycleGraph 25) (cycleGraph 25)) ≤ 24 := by
  by_contra h
  sorry
  done

end SNGraph
