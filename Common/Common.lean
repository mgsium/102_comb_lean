import Mathlib.Tactic

open Nat Set BigOperators

open Finset

universe u

---| Working with Finsets |-----------------------------------------------------

-- in a finset of odd elements, parity of cardinality equals parity of sum
theorem sum_even_even { α : Type u } [DecidableEq α] (X: Finset α) { f : α → ℕ }
  : (∀ x ∈ X, Odd (f x)) → (Even (∑ s in X, f s) ↔ Even X.card) := by
  refine Finset.induction_on X (fun _ ↦ Iff.rfl) ?_
  intro a S ha hS h
  rw [sum_insert ha, card_insert_of_not_mem ha, even_add_one, Nat.even_add]
  simp only [odd_iff_not_even.mp (h a $ mem_insert_self a S), false_iff, not_iff_not]
  exact hS (fun x hx ↦ h x $ mem_insert_of_mem hx)

theorem sum_odd_odd { α : Type u } [DecidableEq α] (X: Finset α) { f : α → ℕ }
  : (∀ x ∈ X, Odd (f x)) → (Odd (∑ s in X, f s) ↔ Odd X.card) := by
  rw [← not_iff_not, ← even_iff_not_odd, ← even_iff_not_odd]
  exact fun h ↦ sum_even_even X h

-- filtered versions
lemma odd_filter (s : Finset ℕ) :
    ∑ k in s, k = ∑ k in (s.filter Odd), k
    +  ∑ k in (s.filter (Even ·)), k := by
  simp only [Nat.even_iff_not_odd]
  exact (sum_filter_add_sum_filter_not s _ _).symm

lemma filter_odd_sum { s : Finset ℕ } :
  Even (card <| filter Odd s) ↔ Even (∑ k in (s.filter Odd), k) := by
  rw [sum_even_even]
  simp only [mem_filter, and_imp, imp_self, implies_true]

lemma filter_odd_sum' { s : Finset ℕ } :
  Odd (card <| filter Odd s) ↔ Odd (∑ k in (s.filter Odd), k) := by
  simp only [Nat.odd_iff_not_even]
  exact not_iff_not.mpr filter_odd_sum

lemma even_sum (X : Finset ℕ)
  : (∀ x ∈ X, Even x) → Even (∑ k in X, k) := by
  refine Finset.induction_on X (fun _ ↦ (fun {_} ↦ Nat.even_iff.mpr) rfl) ?_
  intro a S ha hS h
  rw [sum_insert ha, Nat.even_add]
  simp_all only [Finset.mem_insert, or_true, implies_true]

lemma filter_even_sum (s : Finset ℕ)
  : Even (∑ k in filter (Even ·) s, k) := by
  apply (even_sum  _)
  simp_rw [mem_filter]
  exact fun _ ⟨_, h⟩ ↦ h

theorem sum_odd_odd' (s : Finset ℕ) :
    Odd (∑ k in s, k) ↔ Odd (card <| s.filter Odd) := by
  constructor <;> intro h
  . contrapose h
    rw [← Nat.even_iff_not_odd, odd_filter]
    rw [← Nat.even_iff_not_odd] at h
    apply Even.add (filter_odd_sum.mp h) (filter_even_sum s)
  . rw [odd_filter]
    apply Odd.add_even (filter_odd_sum'.mp h) (filter_even_sum s)

lemma mem_filter_univ {α : Type*} [Fintype α] {p : α → Prop} [DecidablePred p]
  {x : α} : x ∈ filter p univ ↔ p x := by
    simp only [Finset.mem_univ, forall_true_left, mem_filter, true_and]

---| ZMod 2 Parity |------------------------------------------------------------

lemma zmod2_eq_iff { a : ZMod 2 } : a = 1 ↔ ¬a = 0 := by
  cases' a with a ha
  interval_cases a <;> simp

lemma zmod2_parity_iff { a : ZMod 2 } : Even a ↔ a = 0 := by
  simp [even_iff_exists_bit0]

lemma zmod2_parity_iff' { a : ZMod 2 } : Odd a ↔ a = 1 := by
  simp [odd_iff_exists_bit1]
