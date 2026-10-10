import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Positivity
/-! Reusable number theory lemmas. Search Mathlib before adding new results. -/

namespace Olympiad.Utils.NumberTheory

lemma odd_two_mul_sub_one (n : ℕ) (hn : 0 < n) :
    Odd (2 * n - 1) := by
  refine ⟨n - 1, ?_⟩
  omega

lemma two_pow_sub_one_odd (m : ℕ) (hm : 0 < m) : Odd (2 ^ m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [pow_succ, mul_comm]
  exact odd_two_mul_sub_one (2 ^ k) (by positivity)

end Olympiad.Utils.NumberTheory
