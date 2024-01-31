import Mathlib.Tactic

/-!
# Intro 11 (p.28)
Determine the number of ways to choose five numbers from the first eighteen
positive integers such that any two chosen numbers differ by at least 2.

## Solution
let a₁ < a₂ < a₃ < a₄ < a₅ be the five chosen numbers. Then,

  (b₁, b₂, b₃, b₄, b₅) := (a₁, a₂ - 1, a₃ - 2, a₄ - 3, a₅ - 4)

are five distinct numbers from

-/

open Nat Finset List Function

--------------------------------------------------------------------------------
---| SETUP |--------------------------------------------------------------------
--------------------------------------------------------------------------------
section setup

variable (selection : List ℕ)
variable (l : selection.length = 5)
variable (h : Sorted (· < ·) selection)

def diff : Prop := Sorted (· + 2 ≤ ·) selection

instance : DecidablePred diff := by
  unfold diff
  intro L
  exact decidableSorted L
  done

def sel_to_dist (sel : List ℕ) {l : sel.length = 5}
    (h : diff sel) : (List ℕ) :=
  [sel[0]'(by linarith),
   sel[1]'(by linarith)-1,
   sel[2]'(by linarith)-2,
   sel[3]'(by linarith)-3,
   sel[4]'(by linarith)-4]

def dist_to_sel (dist : List ℕ) (l : dist.length = 5)
    (h : Sorted (· < ·) dist) : (List ℕ) :=
  [dist[0]'(by linarith),
  dist[1]'(by linarith)+1,
  dist[2]'(by linarith)+2,
  dist[3]'(by linarith)+3,
  dist[4]'(by linarith)+4]

end setup
--------------------------------------------------------------------------------
---| USEFUL LEMMAS |------------------------------------------------------------
--------------------------------------------------------------------------------
section useful_lemmas
lemma sel_image (sel : List ℕ) {l : sel.length = 5} (h : diff sel)
    : Sorted (· < ·) $ @sel_to_dist sel l h := by
    unfold diff at h
    unfold sel_to_dist
    unfold Sorted at *
    let [a₁,a₂,a₃,a₄,a₅] := sel
    simp only [ge_iff_le, List.pairwise_cons, Bool.not_eq_true, List.mem_cons,
      List.mem_singleton, forall_eq_or_imp, forall_eq, find?_nil, not_mem_nil, IsEmpty.forall_iff,
      forall_const, and_self, and_true] at *
    simp_all only [getElem_eq_get, length_cons, length_singleton, Fin.zero_eta, get_cons_zero, Fin.mk_one,
      get_cons_cons_one, ge_iff_le, get_cons_succ]
    simp_all only [length_cons, length_singleton, ge_iff_le]
    unhygienic with_reducible aesop_destruct_products
    let ⟨a, b, c, d⟩ := left
    repeat' apply And.intro
    all_goals sorry
    done

end useful_lemmas
--------------------------------------------------------------------------------
---| MAIN THEOREM |-------------------------------------------------------------
--------------------------------------------------------------------------------

-- theorem intro11 : Multiset.card S = 23 → count_pairs S ≥ 10 := by
--   sorry
--   done
