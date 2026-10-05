import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.GCDMonoid.Finset

/-!
Competition: JBMO
Year: 1999
Problem: 2
-/

namespace Olympiad.Problems.«JBMO».«Y1999».«P2»

def A (n : ℕ) : ℕ :=
2^(3*n) + 3^(6*n + 2) + 5^(6*n +2)

theorem problem :
(Finset.range 2000).gcd A = 7 := by

  let g := (Finset.range 2000).gcd A

  -- g divides A0 = 35
  have hg_dvd_35 : g ∣ 35 := by
    sorry

  -- g is either 1, 5, 7, or 35.
  have hg_candidates : g = 1 ∨ g = 5 ∨ g = 7 ∨ g=35 := by
    sorry

  -- 5 doesn't divide A1
  have h5_not_dvd_A1 : ¬ 5 ∣ (A 1) := by
    sorry

  -- so g can't be 5 or 35
  have hg_not_5 : g ≠ 5 := by
    sorry

  have hg_not_35 : g ≠ 35 := by
    sorry

  -- An is divisible by 7 for every n
  have h7_dvd_An : ∀ n : ℕ, 7 ∣ A n := by
    sorry

  -- 7 divides the gcd
  have h7_dvd_g : 7 ∣ g := by
    sorry

  -- 7 is the only remaining choice for g, concluding the proof
  rcases hg_candidates with h|h|h|h

  · -- g=1
    rw [h] at h7_dvd_g
    norm_num at h7_dvd_g

  · -- g=5
    rw [h] at hg_not_5
    norm_num at hg_not_5

  · -- g=7
    sorry

  · -- g=35
    rw [h] at hg_not_35
    norm_num at hg_not_35

end Olympiad.Problems.«JBMO».«Y1999».«P2»
