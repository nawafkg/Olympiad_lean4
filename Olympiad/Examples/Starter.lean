import Init

/-!
A small development demonstration, not a competition problem.
Adding zero on the right preserves a natural number, by Lean's standard theorem.
-/

namespace Olympiad.Examples

/-- A minimal example of reusing an existing theorem. -/
theorem add_zero_demo (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n

end Olympiad.Examples
