import Mathlib.Tactic

open Set Nat

/-!
# Intro 24 (pp. 34-35) | [MOSP 1997]
Let A and B be disjoint sets whose union is the set of natural numbers.
Show that for every natural number n, there exist distinct a, b > n such that
{a, b, a+b} ⊆ A or {a, b, a + b} ⊆ B.

## Solution
Suppose A is finite, with largest element m. Then, n+1, n+2, and 2n+3 = (n+1) +
(n+2) are all in B for any n ≥ m. Otherwise, if A is infinite, suppose there is
a positive integer n such that for any a,b > n, {a, b, a + b} is not a subset
or A nor of B. As A is infinite, we may choose x,y,z ∈ A such that x > y > z > n
and y - z > n. Then {x + y, y + z, z + x} ⊆ B, and y - z has no place to go.
-/

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------

variable (A B : Set ℕ) (disjAB : Disjoint A B) (unionAB : A ∪ B = univ)

-- For disjoint sets A and B, n ∈ B if and only if n ∉ A.
lemma mem_B_iff_not_mem_A {n : ℕ} : n ∈ B ↔ n ∉ A := by
  rw [← Disjoint.sdiff_eq_of_sup_eq disjAB unionAB]; simp

-- If A is finite, then there exist distinct a,b > n such that {a, b, a + b}
-- is a subset of A, or a subset of B.
lemma intro24_of_finite (n : ℕ) (h : Set.Finite A)
  : ∃ a b, n < a ∧ n < b ∧ a ≠ b ∧ ({a, b, a + b} ⊆ A ∨ {a, b, a + b} ⊆ B) := by
  let Af := @Set.toFinset _ A (Finite.fintype h)
  rw [← Disjoint.sdiff_eq_of_sup_eq disjAB unionAB]
  by_cases h' : Finset.Nonempty Af
  . let m := Af.max' h'
    use (n + m + 1), (n + m + 2)
    have h₀ : m < n + m + 1 := by linarith
    have h₁ : m < n + m + 2 := by linarith
    have h₂ : m < n + m + 1 + (n + m + 2) := by linarith
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    right
    intro a ha
    rw [mem_diff]
    simp only [mem_univ, true_and]
    rw [← @mem_toFinset _ _ (Finite.fintype h)]
    suffices g : m < a
    . exact Finset.not_mem_of_max_lt g (Finset.coe_max' h').symm
    . simp only [mem_insert_iff, mem_singleton_iff] at ha
      cases ha with
      | inl ha => simp_all
      | inr ha => cases ha <;> simp_all
  . simp only [Finset.not_nonempty_iff_eq_empty, ← toFinset_empty] at h'
    rw [Finite.toFinset_eq_empty.mp h']
    use n + 1, n + 2; simp
  done

-- If A is infinite, then there exist distinct a,b > n such that {a, b, a + b}
-- is a subset of A, or a subset of B.
lemma intro24_of_infinite (n : ℕ) (h : Set.Infinite A)
  : ∃ a b, n < a ∧ n < b ∧ a ≠ b ∧ ({a, b, a+b} ⊆ A ∨ {a, b, a+b} ⊆ B) := by
  by_contra h'
  simp only [ne_eq, not_exists] at h'
  simp only [mem_singleton_iff, and_self_left, not_and] at h'
  let ⟨z, hz, hz'⟩ := Infinite.exists_gt h n
  let ⟨y, hy, hy'⟩ := Infinite.exists_gt h (z + z)
  let ⟨x, hx, hx'⟩ := Infinite.exists_gt h y
  have ht : z < y - z := lt_sub_of_add_lt hy'
  push_neg at h'
  by_cases g : y - z ∈ A
  . let h' := (h' z (y - z) hz' (Nat.lt_trans hz' ht) (Nat.ne_of_lt ht)).1
    rw [Nat.add_sub_of_le (by linarith), not_subset] at h'
    simp_all
  . let g' := (h' (x + z) (y - z) (Nat.lt_add_left n z x hz') (Nat.lt_trans hz' ht) ?_).2
    have hxz : x + z ∉ A := by
      let h₁ := (h' x z (by linarith) (by linarith) (by linarith)).1
      rw [not_subset] at h₁; simp_all
    have hxy : x + y ∉ A := by
      let h₁ := (h' x y (by linarith) (by linarith) (by linarith)).1
      rw [not_subset] at h₁; simp_all
    . rw [add_assoc, Nat.add_sub_of_le (by linarith), not_subset] at g'
      rw [← Disjoint.sdiff_eq_of_sup_eq disjAB unionAB] at g'
      simp_all
    . symm; apply LT.lt.ne
      apply Nat.lt_of_le_of_lt (Nat.sub_le y z) (by linarith)
  done

--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem intro24 (n : ℕ)
  : ∃ a b, n < a ∧ n < b ∧ a ≠ b ∧ ({a, b, a+b} ⊆ A ∨ {a, b, a+b} ⊆ B) := by
  by_cases h : Set.Finite A
  . exact intro24_of_finite A B disjAB unionAB n h
  . exact intro24_of_infinite A B disjAB unionAB n h
  done
