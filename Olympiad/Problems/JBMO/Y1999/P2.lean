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

    have hg_dvd_A0 : g ∣ A 0 := by
      dsimp [g]
      exact Finset.gcd_dvd (by norm_num)

    exact hg_dvd_A0

  -- g is either 1, 5, 7, or 35.
  have hg_candidates : g = 1 ∨ g = 5 ∨ g = 7 ∨ g=35 := by
    have hg_mem : g ∈ Nat.divisors 35 :=
    Nat.mem_divisors.mpr ⟨hg_dvd_35, by norm_num⟩

    change g ∈ ({1, 5, 7, 35} : Finset ℕ) at hg_mem
    simpa using hg_mem

  -- 5 doesn't divide A1
  have h5_not_dvd_A1 : ¬ 5 ∣ (A 1) := by
    norm_num [A]

  -- so g can't be 5 or 35
  have hg_not_5 : g ≠ 5 := by
    intro hg5
    have hg_dvd_A1 : g ∣ A 1 := by
      dsimp[g]
      exact Finset.gcd_dvd (by norm_num)
    rw[hg5] at hg_dvd_A1
    exact h5_not_dvd_A1 hg_dvd_A1

  have hg_not_35 : g ≠ 35 := by
    intro hg35
    have hg_dvd_A1 : g ∣ A 1 := by
      dsimp[g]
      exact Finset.gcd_dvd (by norm_num)
    rw[hg35] at hg_dvd_A1
    have h5_dvd_35 : 5 ∣ 35 := by
      norm_num
    have h5_dvd_A1 : 5 ∣ A 1 :=
      dvd_trans h5_dvd_35 hg_dvd_A1
    exact h5_not_dvd_A1 h5_dvd_A1


  -- An is divisible by 7 for every n
  have h7_dvd_An : ∀ n : ℕ, 7 ∣ A n := by
    intro n

    have h2 : 2 ^ 3 ≡ 1 [MOD 7] := by decide

    have h3 : 3 ^ 6 ≡ 1 [MOD 7] := by
      simpa using (Nat.ModEq.pow_card_sub_one_eq_one (p := 7) (n := 3) (by decide) (by decide))

    have h5 : 5 ^ 6 ≡ 1 [MOD 7] := by
      simpa using (Nat.ModEq.pow_card_sub_one_eq_one (p := 7) (n := 5) (by decide) (by decide))

    have h2n : 2 ^ (3 * n) ≡ 1 [MOD 7] := by
      simpa [Nat.pow_mul] using h2.pow n

    have h3n : 3 ^ (6 * n + 2) ≡ 2 [MOD 7] := by
      have h32 : 3 ^ 2 ≡ 2 [MOD 7] := by decide
      simpa [Nat.pow_add, Nat.pow_mul] using (h3.pow n).mul h32

    have h5n : 5 ^ (6 * n + 2) ≡ 4 [MOD 7] := by
      have h52 : 5 ^ 2 ≡ 4 [MOD 7] := by decide
      simpa [Nat.pow_add, Nat.pow_mul] using (h5.pow n).mul h52

    have hsum : A n ≡ 0 [MOD 7] := by
      unfold A
      exact ((h2n.add h3n).add h5n).trans (by decide)
    exact Nat.modEq_zero_iff_dvd.mp hsum


  -- 7 divides the gcd
  have h7_dvd_g : 7 ∣ g := by
    dsimp [g]
    apply Finset.dvd_gcd
    intro b hb
    exact h7_dvd_An b

  -- 7 is the only remaining choice for g, concluding the proof
  rcases hg_candidates with h|h|h|h

  · -- g=1
    rw [h] at h7_dvd_g
    norm_num at h7_dvd_g

  · -- g=5
    rw [h] at hg_not_5
    norm_num at hg_not_5

  · -- g=7
    simpa [g]

  · -- g=35
    rw [h] at hg_not_35
    norm_num at hg_not_35

end Olympiad.Problems.«JBMO».«Y1999».«P2»
