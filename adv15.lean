import Mathlib.Tactic
import Mathlib.Data.Polynomial.Basic

/-!
# Advanced 15 (pp. 61-62) | [China 1994, Wushang Shu]
Let n be a positive integer. Prove that:

∑ k in Icc 0 n, ((choose n k) * (choose (n - k) (Nat.div (n - k) 2)))
= choose (2 * n + 1) n

## Solution
...
-/

open Nat Finset BigOperators Polynomial

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------

variable {R : Type*} [Semiring R] {r : R}

noncomputable abbrev poly_plus_one_pow (n : ℕ) : R[X] := (X + C 1) ^ (2 * n)

lemma coeff1 (n : ℕ) : coeff (poly_plus_one_pow n) n = choose (2 * n) n := by
  rw [coeff_X_add_C_pow]; simp

lemma coeff2 (n : ℕ) : coeff (poly_plus_one_pow n) (n - 1) = choose (2 * n) (n - 1) := by
  rw [coeff_X_add_C_pow]; simp

lemma choose_add (n : ℕ) (h : 0 < n)
  : choose (2 * n) n + choose (2 * n) (n - 1) = choose (2 * n + 1) n := by
  let ⟨k, hk⟩ := exists_eq_add_of_le' h
  rw [hk, Nat.choose_succ_succ', Nat.add_comm]
  norm_num

lemma poly_eq (n : ℕ) : poly_plus_one_pow n = (X ^ 2 + C 2 * X + 1)^n := by
  unfold poly_plus_one_pow
  norm_num [mul_comm, pow_mul']
  ring_nf

-- lemma coeff_eq (n k : ℕ) : coeff (poly_plus_one_pow n) k = Finset.sum

--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem adv15 (n : ℕ) (h : 0 < n) : ∑ k in Icc 0 n, ((choose n k) * (choose (n - k) (Nat.div (n - k) 2)))
  = choose (2 * n + 1) n := by
  rw [← choose_add n h, ← coeff1, ← coeff2]
  sorry
  done
