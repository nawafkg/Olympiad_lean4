import Mathlib.Algebra.Ring.Basic
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
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Init


/-! Reusable algebra lemmas. Search Mathlib before adding new results. -/

namespace Olympiad.Utils.Algebra

-- An additive integer function is linear
lemma additive_int_linear
(f : ℤ → ℤ)
(hadd : ∀ x y : ℤ, f (x + y) = f x + f y) :
∃ k : ℤ, ∀ x : ℤ, f x = k * x := by

  have h0 : f 0 = 0 := by
    have h := hadd 0 0
    simp at h
    linarith

  refine ⟨f 1, ?_⟩
  intro x
  refine Int.inductionOn'
    (motive := fun n => f n = f 1 * n)
    x 0 ?_ ?_ ?_

  · -- n = 0
    simp [h0]

  · -- n → n + 1
    intro n _ ih
    calc
      f (n + 1) = f n + f 1 := hadd n 1
      _ = f 1 * n + f 1 := by rw [ih]
      _ = f 1 * (n + 1) := by ring

  · -- n → n - 1
    intro n _ ih
    have h : f n = f (n - 1) + f 1 := by
      simpa only [sub_add_cancel] using hadd (n - 1) 1
    calc
      f (n - 1) = f n - f 1 := by linarith
      _ = f 1 * n - f 1 := by rw [ih]
      _ = f 1 * (n - 1) := by ring

end Olympiad.Utils.Algebra
