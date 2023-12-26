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

variable {n r s p q : ℕ}

lemma card_div (hp: Nat.Prime p)(hq: Nat.Prime q)(h: n = p^r * q^s):
    card (Nat.divisors n) = (r + 1) * (s + 1) := by
  sorry
  done

lemma card_div_sq (hp: Nat.Prime p)(hq: Nat.Prime q)(h: n = p^r * q^s):
    card (Nat.divisors (n^2)) = (2 * r + 1) * (2 * s + 1) := by
  sorry
  done

def div_sq_lt (n : ℕ) : Finset ℕ := (Nat.divisors (n^2)).filter (· < n)

-- #eval card (div_nsq_lt_n (36))

lemma card_sq_lt (hp: Nat.Prime p)(hq: Nat.Prime q)(h: n = p^r * q^s):
    card (div_sq_lt (n^2)) = 2 * r * s + r + s := by
  sorry
  done

--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

def div_sq_lt_not_div (n : ℕ) : Finset ℕ :=
    (Nat.divisors (n^2)).filter (fun x => x < n ∧ ¬(x ∣ n))

-- #eval card (div_sq_lt_not_div (36))

theorem card_div_sq_lt_not_div (hp: Nat.Prime p)(hq: Nat.Prime q)(h: n = p^r * q^s):
    card (div_sq_lt_not_div (n^2)) = r * s := by
  sorry
  done
