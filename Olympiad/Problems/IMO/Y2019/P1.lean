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
import Olympiad.Utils.Algebra


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


    --here we prove g is k*x
    obtain ⟨k, hg_linear⟩ := Olympiad.Utils.Algebra.additive_int_linear g hg_add

    --we use g to prove f is linear
    have hf_linear : ∀ x : ℤ, f x = k * x + c := by
      dsimp [g] at hg_linear
      intro x
      have h := hg_linear x
      linarith

    --two cases, either f is 0, or not
    by_cases hzero : ∀ x : ℤ, f x = 0
    · exact Or.inl hzero

    -- when f is not 0, we find k by subtituting back into the original equation
    · right
      have hk : k = 2 := by
        have h00 := hf 0 0
        have h10 := hf 1 0
        simp only [hf_linear] at h00 h10
        have hkprod : k * (k - 2) = 0 := by
          nlinarith [h00, h10]
        rcases mul_eq_zero.mp hkprod with hk0 | hk2
        · have hc0 : c = 0 := by
            rw [hk0] at h00
            linarith
          exfalso
          apply hzero
          intro x
          simp [hf_linear, hk0, hc0]
        · linarith
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
