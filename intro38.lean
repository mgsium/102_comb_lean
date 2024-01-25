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
variable (n : ℕ)
variable (V : Finset ℕ) (c : V.card = 2 * n)
variable (G : SimpleGraph V) [DecidableRel G.Adj] [nei: Nonempty V] (hdeg : ∀ (v : V), Even (G.degree v))
variable (H : Subgraph G)

-- A := N(p)
def closed_nh_comp := λ v ↦ V.attach \ closed_neighborFinset G v

-- We have an even number of vertices
lemma V_even : Even V.card := by {simp_rw [← even_iff_eq_nat_mul_two]; use n}
lemma card_V_gt_zero : 0 < card V := by
  simp only [Finset.card_pos]
  exact nonempty_coe_sort.mp nei
  done

lemma one_le_V : 1 ≤ V.card := by
  by_cases h : n = 0
  . rw [h] at c
    simp at c
    rw [c] at nei
    simp_all only [not_mem_empty, nonempty_subtype, exists_const]
  . push_neg at h
    rw [← one_le_iff_ne_zero] at h
    linarith
  done

lemma V_take_vertex_even : ∀ (p : V), Odd (card $ V.attach.erase p) := by
  simp only [mem_attach, card_erase_of_mem, card_attach]
  intro _
  apply Nat.Even.sub_odd (by exact one_le_V _ _ c) (V_even _ _ c) odd_one
  done

-- B := (V ∖ {p}) ∖ A
lemma V_take_open_nh_even
  : ∀ (p : V), Even (card $ V.attach \ G.neighborFinset p) := by
  intro p
  rw [card_sdiff]
  . simp only [card_attach]
    refine Even.tsub (V_even _ _ c) ?_
    rw [card_neighborFinset_eq_degree]
    exact hdeg p
  . intro x
    simp only [mem_neighborFinset, mem_attach, implies_true]
  done

-- Closed neighborhood has even cardinality
lemma closed_nh_even (p : V) : Odd (card $ closed_neighborFinset G p) := by
  rw [card_closed_neighborFinset_eq_deg_add_one G p]
  exact Even.add_one (hdeg p)
  done

-- Vertex set is non-empty
lemma nonempty_V_aux : Finset.Nonempty V := Finset.card_pos.mp (card_V_gt_zero _)
lemma nonempty_V : Nonempty V := Set.Nonempty.coe_sort (nonempty_V_aux _)

-- The cardinality of B is odd
lemma V_take_closed_nh_odd
  : ∀ (p : V), Odd (card $ closed_nh_comp _ G p) := by
  intro p
  unfold closed_nh_comp
  rw [card_sdiff, card_attach]
  apply Nat.Even.sub_odd _ (V_even _ _ c) (closed_nh_even _ _ hdeg p)
  rw [← Fintype.subtype_card V (λ x ↦ Iff.rfl)]
  exact card_le_univ (closed_neighborFinset G p)
  unfold closed_neighborFinset
  apply insert_subset
  . exact mem_attach V p
  . rw [subset_iff]
    intro x _
    exact mem_attach V x
  done

-- Vertices in B are not adjacent to p
lemma h₃ : ∀(p q : V), q ∈ closed_nh_comp _ G p → ¬G.Adj p q := by
  unfold closed_nh_comp
  simp only [mem_sdiff, mem_attach, mem_neighborFinset, true_and]
  unfold closed_neighborFinset
  intro p q
  contrapose; simp only [not_not]
  rw [← mem_neighborFinset]
  exact mem_insert_of_mem
  done

lemma disjoint_lemma : ∀ (p q : V), Disjoint
  (G.neighborFinset q ∩ G.neighborFinset p)
  (G.neighborFinset q ∩ closed_nh_comp _ G p) := by
  unfold closed_nh_comp
  intro p q
  rw [disjoint_iff_inter_eq_empty, inter_left_comm, inter_sdiff_super]
  . exact inter_empty _
  . apply subset_trans (inter_subset_right _ _)
    unfold closed_neighborFinset
    exact subset_insert _ _
  done


lemma part_V_by_nh
  : ∀ (p : V), V.attach = closed_nh_comp _ G p ∪ closed_neighborFinset G p := by
  unfold closed_nh_comp
  simp only [sdiff_union_self_eq_union, left_eq_union]
  aesop_graph
  done

lemma inter_eq_sdiff_comp_nh : ∀ (p q : V),
  neighborFinset G q \ closed_nh_comp _ G p
  = neighborFinset G q ∩ closed_neighborFinset G p := by
  unfold closed_nh_comp
  aesop_graph
  done

lemma not_in_neighborFinset (v : V) : ¬v ∈ (neighborFinset G v) := by
  simp_all only [mem_neighborFinset, SimpleGraph.irrefl]
  done

lemma insert_sdiff_disj (x : V) (X : Finset  V) (h : ¬x ∈ X)
    : (insert x X) \ {x} = X := by
  ext y
  constructor
  <;> intro h'
  <;> simp_all only [mem_insert, or_false, not_true, mem_sdiff, mem_singleton,
    or_true, true_and]
  . tauto
  . exact ne_of_mem_of_not_mem h' h
  done

-- deg_A(q) is odd
lemma odd_deg_A_q (g : ∀ (a b : { x // x ∈ V }),
    ¬Even (card (neighborFinset G a ∩ neighborFinset G b)))
    : ∀(p q : V), q ∈ closed_nh_comp _ G p
    → Odd (card (G.neighborFinset q ∩ neighborFinset G p))
  := fun p q _ ↦ (fun {_} ↦ odd_iff_not_even.mpr) (g q p)

lemma in_closed_nh_comp_iff_not_adj (p q : V) : q ∈ closed_nh_comp _ G p ↔ (¬Adj G p q ∧ p ≠ q) := by
  unfold closed_nh_comp closed_neighborFinset
  constructor <;> intro g
  . simp_all only [mem_sdiff, mem_attach, mem_insert, mem_neighborFinset, true_and, Subtype.mk.injEq]
    push_neg at *
    tauto
  . rw [← mem_neighborFinset] at g
    rw [mem_sdiff, mem_insert]
    push_neg
    simp_all only [ne_eq, mem_neighborFinset, mem_attach, not_false_eq_true, and_true,
      true_and]
    exact Ne.symm g.2
  done

lemma h₅ (g : ∀ (a b : { x // x ∈ V }),
    ¬Even (card (neighborFinset G a ∩ neighborFinset G b))) : ∀(p q : V), q ∈ closed_nh_comp _ G p
    → Odd (card (G.neighborFinset q ∩ closed_neighborFinset G p)) := by
  intro p q h
  have : G.neighborFinset q ∩ (closed_neighborFinset G p \ {p})
      = (G.neighborFinset q ∩ closed_neighborFinset G p) := by
    unfold closed_neighborFinset
    ext v
    simp only [mem_inter, mem_neighborFinset, mem_sdiff, mem_insert, mem_singleton,
      and_congr_right_iff, and_iff_left_iff_imp]
    intro g g'
    rw [in_closed_nh_comp_iff_not_adj] at h
    by_contra a
    rw [a] at g
    tauto
    done
  rw [← this]
  unfold closed_neighborFinset
  rw [insert_sdiff_disj V p (G.neighborFinset p) $ not_in_neighborFinset _ _ _]
  exact odd_deg_A_q _ _ g p q h
  done

-- deg_B(q) is odd
lemma degree_in_B_odd (g : ∀ (a b : { x // x ∈ V }),
    ¬Even (card (neighborFinset G a ∩ neighborFinset G b)))
    : ∀(p q : V), q ∈ closed_nh_comp _ G p
    → Odd (card (G.neighborFinset q ∩ closed_nh_comp _ G p)) := by
  intro p q h
  rw [(sdiff_sdiff_self_left _ _).symm]
  rw [card_sdiff (sdiff_subset _ _)]
  apply Nat.Even.sub_odd _ (hdeg q) _
  . apply le_trans
    . exact Nat.le_add_right _ (card (neighborFinset G q ∩ closed_nh_comp _ G p))
    . unfold closed_nh_comp
      rw [card_sdiff_add_card_inter]
      exact Nat.le_refl _
  . rw [inter_eq_sdiff_comp_nh]
    exact h₅ V G g p q h
  done

-- The sum of the degrees of elements in B is odd
lemma sum_of_B_elem_deg_odd (g : ∀ (a b : { x // x ∈ V }),
    ¬Even (card (neighborFinset G a ∩ neighborFinset G b))) : ∀(p : V), Odd (∑ q in closed_nh_comp _ G p,
  (card (G.neighborFinset q ∩ closed_nh_comp _ G p))) := by
  intro p
  rw [sum_odd_odd $ closed_nh_comp _ G p]
  . exact V_take_closed_nh_odd _ _ c _ hdeg p
  . intro q h
    exact degree_in_B_odd _ _ hdeg g _ _ h
  done

-- Follows from Euler's handshaking lemma applied to the subgraph induced
-- on the closed neighbourhood of p.
lemma sum_of_B_elem_deg_even : ∀(p : V),
  ¬Odd (∑ q in closed_nh_comp _ G p, (card (G.neighborFinset q ∩ closed_nh_comp _ G p))) := by
  intro p
  -- The graph api for inducing subgraphs is horrible.
  sorry
  done

theorem intro38
  : ∃(a b : V), Even (card (G.neighborFinset a ∩ G.neighborFinset b)) := by
  by_contra g
  push_neg at g

  have odd : ∀(p : V), Odd (∑ q in closed_nh_comp _ G p,
      (card (G.neighborFinset q ∩ closed_nh_comp _ G p)))
    := fun p ↦ sum_of_B_elem_deg_odd n V c G hdeg g p
  have even : ∀(p : V), ¬Odd (∑ q in closed_nh_comp _ G p,
      (card (G.neighborFinset q ∩ closed_nh_comp _ G p)))
    := fun p ↦ sum_of_B_elem_deg_even V G p
  simp_all only [odd_iff_not_even, not_not]
  apply even
  exact?
  done
