import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Competition: JBMO
Year: 2026
Problem: 1
-/

namespace Olympiad.Problems.«JBMO».«Y2026».«P1»

theorem problem
(a b c : ℝ)
(ha : 0 < a)
(hb : 0 < b)
(hc : 0 < c)
(habc : a^2 + b^2 + c^2 ≥ 3) :
a^4 / (a^2 + 2*b + 2*c) + b^4 / (b^2 + 2*c + 2*a) + c^4 / (c^2 + 2*a + 2*b) ≥ 3/5 := by

  have h_a : a^4 + 1 ≥ 2*a^2 := by
    nlinarith [sq_nonneg (a^2 - 1)]
  have h_b : b^4 + 1 ≥ 2*b^2 := by
    nlinarith [sq_nonneg (b^2 - 1)]
  have h_c : c^4 + 1 ≥ 2*c^2 := by
    nlinarith [sq_nonneg (c^2 - 1)]

  have h_aa : 2*a ≤ a^2 + 1 := by
    nlinarith [sq_nonneg (a - 1)]
  have h_bb : 2*b ≤ b^2 + 1 := by
    nlinarith [sq_nonneg (b - 1)]
  have h_cc : 2*c ≤ c^2 + 1 := by
    nlinarith [sq_nonneg (c - 1)]

  -- each denominator is at most a^2 + b^2 + c^2 + 2
  have hden_a : a^2 + 2*b + 2*c ≤ a^2 + b^2 + c^2 + 2 := by
    linarith
  have hden_b : b^2 + 2*c + 2*a ≤ a^2 + b^2 + c^2 + 2 := by
    linarith
  have hden_c : c^2 + 2*a + 2*b ≤ a^2 + b^2 + c^2 + 2 := by
    linarith

  -- the denominators are positive
  have hpos_a : 0 < a^2 + 2*b + 2*c := by
    nlinarith [sq_nonneg a]
  have hpos_b : 0 < b^2 + 2*c + 2*a := by
    nlinarith [sq_nonneg b]
  have hpos_c : 0 < c^2 + 2*a + 2*b := by
    nlinarith [sq_nonneg c]

  -- replacing each denominator by a^2 + b^2 + c^2 + 2 decreases each term
  have ht_a : a^4 / (a^2 + 2*b + 2*c) ≥ a^4 / (a^2 + b^2 + c^2 + 2) :=
    div_le_div_of_nonneg_left (pow_nonneg ha.le 4) hpos_a hden_a
  have ht_b : b^4 / (b^2 + 2*c + 2*a) ≥ b^4 / (a^2 + b^2 + c^2 + 2) :=
    div_le_div_of_nonneg_left (pow_nonneg hb.le 4) hpos_b hden_b
  have ht_c : c^4 / (c^2 + 2*a + 2*b) ≥ c^4 / (a^2 + b^2 + c^2 + 2) :=
    div_le_div_of_nonneg_left (pow_nonneg hc.le 4) hpos_c hden_c

  -- combine the three fractions with the common denominator
  have h_sum : a^4 / (a^2 + b^2 + c^2 + 2) + b^4 / (a^2 + b^2 + c^2 + 2)
      + c^4 / (a^2 + b^2 + c^2 + 2)
      = (a^4 + b^4 + c^4) / (a^2 + b^2 + c^2 + 2) := by
    rw [add_div, add_div]

  -- sum of fourth powers is at least 2(a^2 + b^2 + c^2) - 3
  have h_four : a^4 + b^4 + c^4 ≥ 2*(a^2 + b^2 + c^2) - 3 := by
    linarith

  -- (2S - 3)/(S + 2) ≥ 3/5 is equivalent to S ≥ 3
  have h_key : (a^4 + b^4 + c^4) / (a^2 + b^2 + c^2 + 2) ≥ 3/5 := by
    have hS : 0 < a^2 + b^2 + c^2 + 2 := by linarith
    rw [ge_iff_le, le_div_iff₀ hS]
    linarith

  linarith

end Olympiad.Problems.«JBMO».«Y2026».«P1»
