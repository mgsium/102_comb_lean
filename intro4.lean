import Mathlib.Tactic

/-!
# Intro 4 (pp. 18) | [AMC 12 2001]
How many positive integers not exceeding 2001 are multiples of 3 or 4 but not 5?
-/

open Finset Nat Function

-- counting number of elements ≤ 2001 which are divisible by 3
def set3 : Finset ℕ := (range 2002 \ singleton 0).filter (3 ∣ ·)

def f (x : ℕ) : ℕ := 3 * x

theorem f_inj : Injective f := by
  intro x y h
  simp [f] at h
  exact h
  done

theorem num_div_3 : card set3 = 667 := by
  have h : set3 = image f (range 668 \ singleton 0) := by
    simp only [set3, f] ; ext x ; simp [mem_range]
    constructor <;> intro h
    · use x / 3
      rcases h with ⟨⟨h1,h2⟩,h3⟩
      constructor
      · constructor
        · refine Nat.div_lt_of_lt_mul (by linarith)
        · contrapose! h2
          exact eq_zero_of_dvd_of_div_eq_zero h3 h2
      · exact Nat.mul_div_cancel' h3
    · rcases h with ⟨h1,⟨⟨h2,h3⟩,h4⟩⟩
      constructor
      · constructor
        · linarith
        · by_contra h5
          rw [h5] at h4
          simp at h4
          tauto
      · exact Dvd.intro h1 h4
  rw [h, card_image_of_injective _ f_inj]
  simp only [mem_range, not_true, singleton_subset_iff, card_sdiff, card_range]
  done

--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

def my_set : Finset ℕ :=
    (range 2002 \ singleton 0).filter (fun x => (3 ∣ x ∨ 4 ∣ x) ∧ ¬ 5 ∣ x)

theorem intro4 : card my_set = 801 := by
  sorry
  done
