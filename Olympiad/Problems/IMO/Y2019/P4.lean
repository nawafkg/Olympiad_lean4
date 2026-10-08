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
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic



/-!
Competition: IMO
Year: 2019
Problem: 4
-/

namespace Olympiad.Problems.«IMO».«Y2019».«P4»

def ValidPair (k n : ℕ) : Prop :=
0 < k ∧ 0 < n ∧
k.factorial = ∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i)

theorem problem_4 (k n : ℕ) :
ValidPair k n ↔
(k = 1 ∧ n = 1) ∨ (k = 3 ∧ n = 2) := by
  constructor

  · intro h
    sorry

  · dsimp[ValidPair]
    intro h
    rcases h with h1 | h2
    · constructor
      · rw[h1.1]
        linarith
      · constructor
        · rw[h1.2]
          linarith
        · rw[h1.1, h1.2]
          decide
    · constructor
      · rw[h2.1]
        linarith
      · constructor
        · rw[h2.2]
          linarith
        · rw[h2.1, h2.2]
          decide


end Olympiad.Problems.«IMO».«Y2019».«P4»
