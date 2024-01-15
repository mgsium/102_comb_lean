import Mathlib.Tactic

/-!
# Intro 30 (pp. 32) | [AIME 1995]
Let n = 2^31 * 3^19. How many positive integer divisors of n^2 are
less than n but do not divide n?
## Solution
We prove the more general case where n = p^r * q^s with p,q prime. Then, n^2 has
(2r + 1)(2s + 1) divisors. Of these, 2rs + r + s are less than n. After excluding
the divisors of n, we are left with exactly 2rs such divisors.
-/

open Finset Nat Function

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------

variable (n r s p q : ℕ)

def setpq (p q r s : ℕ) : Finset ℕ :=
  ((range (r + 1)).product (range (s + 1))).image (fun ij => p^(ij.1) * q^(ij.2))

-- #eval setpq 2 3 2 2 = Nat.divisors (2^2 * 3^2)

lemma bob (hp: Nat.Prime p) (hq: Nat.Prime q) (hpq: p ≠ q):
    Nat.divisors (p^r * q^s) = setpq p q r s := by
  unfold Nat.divisors setpq
  ext
  simp only [mem_image, mem_product, mem_range, exists_prop, mem_filter, mem_range, exists_prop]
  aesop
  · sorry
  · sorry
  · sorry
  · sorry

lemma card_div (hp: Nat.Prime p)(hq: Nat.Prime q)(hpq: p ≠ q):
    card (Nat.divisors (p^r * q^s)) = (r + 1) * (s + 1) := by
  rw [bob, setpq]
  · sorry
  all_goals assumption

lemma card_div_sq (hp: Nat.Prime p)(hq: Nat.Prime q)(hpq: p ≠ q)(h: n = p^r * q^s):
    card (Nat.divisors (n^2)) = (2 * r + 1) * (2 * s + 1) := by
  rw [h, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, mul_comm r 2, mul_comm s 2]
  apply card_div <;> assumption

lemma ndivs_in_nsqdivs (x : ℕ)(h: x ∣ n) : x ∈ divisors (n^2) := by
  simp
  sorry
  done

lemma card_sq_lt (hp: Nat.Prime p)(hq: Nat.Prime q)(hpq: p ≠ q)(h: n = p^r * q^s):
    card ((Nat.divisors (n^2)).filter (· < n)) = 2 * r * s + r + s := by
  sorry
  done

lemma alg_identity1 : (r+1) * (s+1) - 1 = r * s + r + s := by
  have h1 : (r+1) * (s+1) - 1  = r * s + r + s + 1 - 1 := by
    ring_nf
  simp [h1]
  done

lemma alg_identity2 : 2 * r * s + r + s - ((r+1) * (s+1) - 1) = r * s := by
  rw [alg_identity1]
  sorry
  done

lemma card_div_n_lt_n (h: ¬ n = 0) : card ((Nat.divisors n).filter (· < n))
    = card (Nat.divisors n) - 1 := by
  have h : (Nat.divisors n).filter (· < n) = (Nat.divisors n).erase n := by
    ext a
    constructor
    · simp_all only [mem_divisors, ne_eq, not_false_eq_true, and_true, not_lt,
    mem_filter, Nat.isUnit_iff, dvd_refl,and_self, mem_erase]
      intro h1
      exact Nat.ne_of_lt h1.2
    · simp_all only [mem_divisors, dvd_refl, ne_eq, not_false_eq_true, and_self,
     mem_erase, Nat.isUnit_iff, and_true, not_lt, mem_filter, true_and]
      intro h1
      rcases h1 with ⟨h1, h2⟩
      push_neg at h1 h
      sorry
  rw [h]
  apply card_erase_of_mem
  simpa
  done

--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

theorem card_div_sq_lt_not_div (hp: Nat.Prime p)(hq: Nat.Prime q)(hpq: p ≠ q)
    (h: n = p^r * q^s) :
    card ((Nat.divisors (n^2)).filter (fun x => x < n ∧ ¬(x ∣ n))) = r * s := by
  have h1 : card ((Nat.divisors (n^2)).filter (· < n)) = 2 * r * s + r + s := by
    sorry
  have h2 : card (Nat.divisors (p^r * q^s)) = (r + 1) * (s + 1) := by
    exact card_div r s p q hp hq hpq
  rw [h]
  sorry
  done
