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


/-!
Competition: IMO
Year: 2019
Problem: 1
-/

namespace Olympiad.Problems.«IMO».«Y2019».«P1»

theorem problem (f : ℤ → ℤ) :
(∀ a b : ℤ, f (2 * a) + 2 * f b = f (f (a + b))) ↔
((∀ x : ℤ, f x = 0) ∨ ∃ c : ℤ, ∀ x : ℤ, f x = 2 * x + c) := by
  constructor

  --proving the only two valid forms are f(x) = 0 and f(x) = 2x + c
  · intro hf

    --by some subtitution magic, we arrive here
    have hadd : ∀ a b : ℤ, f a + f b = f (a + b) + f 0 := by
      intro a b
      have hab := hf a b
      have h0a := hf 0 a
      have ha0 := hf a 0
      have h0ab := hf 0 (a+b)
      simp at h0a ha0 h0ab
      linarith

    let c := f 0
    let g : ℤ → ℤ := fun x => f x - c

    --g is additive
    have hg_add : ∀ a b : ℤ, g (a + b) = g a + g b := by
      intro a b
      dsimp [g]
      dsimp [c]
      have h := hadd a b
      linarith

    let k := g 1

    --here we prove g is k*x
    have hg_linear : ∀ x : ℤ, g x = k * x := by
      sorry

    --we use g to prove f is linear
    have hf_linear : ∀ x : ℤ, f x = k * x + c := by
      sorry

    --two cases, either f is 0, or not
    by_cases hzero : ∀ x : ℤ, f x = 0
    · exact Or.inl hzero

    -- when f is not 0, we find k by subtituting back into the original equation
    · right
      have hk : k = 2 := by
        sorry
      use c
      intro x
      rw [hf_linear x, hk]

  --proving that f(x) = 0 and f(x) = 2x + c satisfy the equation
  · intro h
    rcases h with hzero | hlin

    · intro a b
      simp[hzero]

    · obtain ⟨c, hf⟩ := hlin
      intro a b
      simp[hf]
      ring




end Olympiad.Problems.«IMO».«Y2019».«P1»
