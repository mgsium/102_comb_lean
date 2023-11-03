import Mathlib
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih

-- theorem commie (a b : ℕ)(h: a > 2) : a+b = b+a := by
--   induction_from_s a with a ha
