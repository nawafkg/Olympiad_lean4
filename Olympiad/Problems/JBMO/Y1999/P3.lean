import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum

/-!
Competition: JBMO
Year: 1999
Problem: 3
-/

namespace Olympiad.Problems.«JBMO».«Y1999».«P3»

abbrev Point := ℝ × ℝ

def squareVertices : Set Point :=
  {(0, 0), (20, 0), (20, 20), (0, 20)}

def insideSquare (p : Point) : Prop :=
  0 < p.1 ∧ p.1 < 20 ∧
  0 < p.2 ∧ p.2 < 20

noncomputable def triangleArea (a b c : Point) : ℝ :=
  |(b.1 - a.1) * (c.2 - a.2) -
    (b.2 - a.2) * (c.1 - a.1)| / 2

def givenPoints (P : Fin 1999 → Point) : Set Point :=
  squareVertices ∪ Set.range P

theorem problem
(P : Fin 1999 → Point)
(h_inside : ∀ i, insideSquare (P i))
(h_injective : Function.Injective P) :
∃ a b c : Point,
a ∈ givenPoints P ∧
b ∈ givenPoints P ∧
c ∈ givenPoints P ∧
a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
triangleArea a b c ≤ (1 : ℝ) / 10 := by
  sorry



end Olympiad.Problems.«JBMO».«Y1999».«P3»
