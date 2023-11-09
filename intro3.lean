import Mathlib.Tactic

variable (n : ℕ)

open Nat
open BigOperators
open Finset

lemma aux1 : ∑ k in range (n+1), choose n k = 2^n := by
  exact sum_range_choose n
  done

def my_set2 : Finset ℕ := range n \ singleton 0

lemma aux1' : ∑ k in my_set2 n, choose n k = 2^n-2 := by
    sorry
    done

-- def n : ℕ := 11

def my_set : Finset ℕ := range (1+(n-1)/2) \ singleton 0

lemma aux2 (h:n > 1)(h': Odd n): 2 * ∑ k in my_set n, choose n k = 2^n-2 := by
  simp [my_set]
  sorry
  done


-- #eval ∑ k in my_set, choose n k
-- #eval 2^(n-1)-1

def binomial_coefficients_set (n : ℕ) : Finset ℕ :=
(range ((n - 1) / 2)).map ⟨λ k => Nat.choose n (k + 1), by sorry⟩

#eval binomial_coefficients_set 13

def odd_binomials_finset (n : ℕ) : Finset ℕ :=
filter (λ k => Odd (Nat.choose n k)) (range ((n + 1) / 2) \ singleton 0)

#eval odd_binomials_finset 7

theorem odd_number_of_odd_numbers {n : ℕ} (h : Odd n) :
  Odd (card (odd_binomials_finset n)) := by
  sorry
  done


theorem odd_filter (set' : Finset ℕ) :
   ∑ k in set', k = ∑ k in (set'.filter (λ x => Odd x)), k
   +  ∑ k in (set'.filter (λ x => ¬ Odd x)), k   := by
   exact (sum_filter_add_sum_filter_not set' (fun x => Odd x) fun x => x).symm
   done

lemma odd_sum {n : ℕ} (X : Finset ℕ) (h': card X = 2*n): Even (∑ k in X, k) := by
  unfold Even
  induction' n with d hd
  .simp [card_eq_zero.mp h']
   use 0
   rfl
  . sorry
  done

lemma filter_odd_sum (set' : Finset ℕ) (h: ¬Odd (card (filter (fun x => Odd x) set'))):
 Even (∑ k in filter (fun x => Odd x) set', k) := by
  rw [even_iff_not_odd.symm] at h
  sorry
  simp at h
  exact h
  done

lemma even_sum {n : ℕ} (X : Finset ℕ) (h': card X = n)(h: ∀ x ∈ X, Even x):
  Even (∑ k in X, k) := by
  unfold Even
  induction' n with d hd
  .simp [card_eq_zero.mp h']
   use 0
   rfl
  . obtain ⟨x, hx⟩ : ∃ x, x ∈ X := card_pos.mp (h'.symm ▸ succ_pos d)
    let X' := erase X x
    have hX' : card X' = d := (card_erase_of_mem hx).trans (congrArg pred h')
    have h'' : Even (∑ k in X', k) := sorry
    obtain ⟨k, hk⟩ := h x hx
    have h''' : Even (k + ∑ k in X', k) := by
      have he: Even x := by sorry
      apply Even.add he h''
      done
    sorry
  done

theorem test (x k: ℕ)(h: x = k + k): (Even x) := by
  rw [h] at *
  exact even_add_self k
  done

theorem extracted_1 {n : ℕ} (X : Finset ℕ) (h'_1 : card X = n) (h : ∀ (x : ℕ), x ∈ X → Even x) (d : ℕ)
  (hd : card X = d → ∃ r, ∑ k in X, k = r + r) (h' : card X = succ d) : ∃ r, ∑ k in X, k = r + r := sorry

lemma filter_even_sum (set' : Finset ℕ):
  Even (∑ k in filter (fun x => ¬Odd x) set', k) := by
  let even_set := filter (fun x => ¬Odd x) set'
  have h : ∀ x ∈ even_set, Even x := by
    intros x hx
    simp at hx
    obtain ⟨_,h2⟩ := hx
    exact h2
  apply (even_sum even_set rfl h)
  done


theorem general_odd (set' : Finset ℕ) (h : Odd (∑ k in set', k)) :
  Odd (card (set'.filter (λ x => Odd x))) := by
  contrapose h
  simp
  rw [odd_filter]
  have h1: Even (∑ k in filter (fun x => ¬Odd x) set', k)
    := by exact filter_even_sum set'
  have h2: Even (∑ k in filter (fun x => Odd x) set', k)
    := by exact filter_odd_sum set' h
  apply Even.add h2 h1
  done
