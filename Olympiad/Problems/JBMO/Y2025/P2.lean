import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Competition: JBMO
Year: 2025
Problem: 2
-/

namespace Olympiad.Problems.«JBMO».«Y2025».«P2»

/-- The number 20252025...2025 made of `n` blocks of the digits 2025. -/
def blocks (n : ℕ) : ℕ :=
∑ i ∈ Finset.range n, 2025 * 10 ^ (4 * i)

theorem problem (N : ℕ) :
((∃ n, 0 < n ∧ N = blocks n) ∧ (∃ x, 0 < x ∧ N = x ^ 2)) ↔
N = 2025 := by
  sorry

end Olympiad.Problems.«JBMO».«Y2025».«P2»
