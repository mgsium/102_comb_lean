import Mathlib

#check Mul.mul

lemma h : 1 + 0 = 1 := rfl

example : 2 + 0 = 2 := by
  exact rfl
  done

lemma advanced22 (x y : ℕ) : x + y = y + x := by
  sorry
  done

lemma h (x y : ℕ) : x * y = y * x := by
  sorry
  done