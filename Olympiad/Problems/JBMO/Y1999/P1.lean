import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Competition: JBMO
Year: 1999
Problem: 1
-/

namespace Olympiad.Problems.«JBMO».«Y1999».«P1»

theorem problem_1
(a b c x y : ℝ)
(ha : a^3 + a*x + y = 0)
(hb : b^3 + b*x + y = 0)
(hc : c^3 + c*x + y = 0)
(hab : a ≠ b)
(hbc : b ≠ c)
(hca : a ≠ c) :
a + b + c = 0 := by
  -- subtract first two equations
  have hsubtract_ab : (a-b) * (a^2 + a*b + b^2 + x) = 0 := by
    calc
      (a-b) * (a^2 + a*b + b^2 + x) = (a^3 + a*x + y) - (b^3 + b*x + y) := by ring
      _ = 0 := by rw[ha, hb]; ring
  -- conclude second term is 0
  have hab0 : a^2 + a*b + b^2 + x = 0 := by
    have hne : a-b ≠ 0 := sub_ne_zero.mpr hab
    exact (mul_eq_zero.mp hsubtract_ab).resolve_left hne
  -- subtract second two equations
  have hsubtract_bc : (b-c) * (b^2 + b*c + c^2 + x) = 0 := by
    calc
      (b-c) * (b^2 + b*c + c^2 + x) = (b^3 + b*x + y) - (c^3 + c*x + y) := by ring
      _ = 0 := by rw[hb, hc]; ring
  -- conclude second term is 0
  have hbc0 : b^2 + b*c + c^2 + x = 0 := by
    have hne : b-c ≠ 0 := sub_ne_zero.mpr hbc
    exact (mul_eq_zero.mp hsubtract_bc).resolve_left hne
  --subtract the two new equaitons
  have hsubtract_final : (a-c) * (a+b+c) = 0 := by
    calc
      (a-c) * (a+b+c) = (a^2 + a*b + b^2 + x) - (b^2 + b*c + c^2 + x) := by ring
      _ = 0 := by rw[hab0, hbc0]; ring
  --conclude second term is 0 and finish the proof
  have hne : a-c ≠ 0 := sub_ne_zero.mpr hca
  exact (mul_eq_zero.mp hsubtract_final).resolve_left hne


end Olympiad.Problems.«JBMO».«Y1999».«P1»
