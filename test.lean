import Mathlib.Tactic

#check Mul.mul

lemma h : 1 + 0 = 1 := rfl

example : 2 + 0 = 2 := by
  exact rfl
  done