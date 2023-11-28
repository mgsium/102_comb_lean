import Mathlib.Tactic

open Nat Set BigOperators

open Finset

-- in a finset of odd elements, parity of cardinality equals parity of sum
def odd_set_card_odd_iff_sum_odd (S : Finset ℕ) :=
  (∀ x ∈ S, Odd x) → (Odd (∑ s in S, s) ↔ Odd S.card)

theorem sum_odd_odd :
  ∀ (X: Finset ℕ), odd_set_card_odd_iff_sum_odd X := by
  apply Finset.induction
  . intro _; rfl
  . intro x X h h' ha
    rw [sum_insert h, card_insert_of_not_mem h, odd_add, odd_add']
    have : Odd x := (ha x) (mem_insert_self x X)
    simp only [true_iff, this]
    rw [← not_iff_not]
    repeat rw [← odd_iff_not_even]
    apply h'
    intro x hx
    exact (ha x) (mem_insert_of_mem hx)
