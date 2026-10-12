import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.ModEq

/-!
Competition: JBMO
Year: 2026
Problem: 2
-/

namespace Olympiad.Problems.«JBMO».«Y2026».«P2»

def ValidPair (a b : ℕ) : Prop :=
0 < a ∧ 0 < b ∧
a + 1 ∣ b + 2 ∧ b ∣ 2 * a ^ 2

theorem problem (a b : ℕ) :
ValidPair a b ↔
(a = 2 ∧ b = 1) ∨ (a = 3 ∧ b = 2) ∨ (a = 3 ∧ b = 18) ∨ (0 < a ∧ b = 2 * a) := by
  constructor

  · intro h
    obtain ⟨ha_pos, hb_pos, hdvd1, hdvd2⟩ := h
    sorry

  · intro h
    rcases h with ⟨rfl, rfl ⟩ | ⟨rfl, rfl ⟩ <;> dsimp[ValidPair] <;> decide

end Olympiad.Problems.«JBMO».«Y2026».«P2»
