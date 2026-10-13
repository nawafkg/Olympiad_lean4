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
    -- write b + 2 = (a + 1) * k and 2a^2 = b * d
    obtain ⟨k, hk⟩ := hdvd1
    obtain ⟨d, hd⟩ := hdvd2
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k) with hk0 | hk1 | hk2 | hk3

    · -- k = 0 is impossible since b + 2 > 0
      rw [hk0] at hk
      omega

    · -- k = 1: a = b + 1, so b divides 2
      rw [hk1] at hk
      obtain rfl : a = b + 1 := by omega
      have hb_dvd : b ∣ b * (2 * b + 4) + 2 := by
        rw [show b * (2 * b + 4) + 2 = 2 * (b + 1) ^ 2 by ring]
        exact ⟨d, hd⟩
      have hb2 : b ∣ 2 := (Nat.dvd_add_right (dvd_mul_right b _)).mp hb_dvd
      have hb_le : b ≤ 2 := Nat.le_of_dvd (by norm_num) hb2
      interval_cases b <;> simp

    · -- k = 2: b = 2a
      right; right; right
      rw [hk2] at hk
      exact ⟨ha_pos, by omega⟩

    · -- k ≥ 3: show a = 3, b = 18
      right; right; left
      have hd_pos : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · rw [h0] at hd
          have : a ^ 2 = 0 := by omega
          simp at this
          omega
        · exact h0
      -- b ≥ 3(a + 1) - 2 > 2a
      have hb_gt : 2 * a < b := by nlinarith
      -- since b * d = 2a^2 and b > 2a, d < a
      have hd_lt : d < a := by
        by_contra h
        push Not at h
        nlinarith
      -- a + 1 divides 2(d + 1)
      have hdvd : a + 1 ∣ 2 * (d + 1) := by
        obtain ⟨c, hc⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
        have h1 : (a + 1) * (d * k) = 2 * a ^ 2 + 2 * d := by
          calc (a + 1) * (d * k) = d * (b + 2) := by rw [hk]; ring
            _ = 2 * a ^ 2 + 2 * d := by rw [hd]; ring
        have h2 : 2 * a ^ 2 = (a + 1) * (2 * c) + 2 := by rw [hc]; ring
        have h3 : a + 1 ∣ (a + 1) * (2 * c) + 2 * (d + 1) := ⟨d * k, by linarith⟩
        exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h3
      -- 0 < 2(d + 1) ≤ 2a < 2(a + 1), so 2(d + 1) = a + 1
      obtain ⟨j, hj⟩ := hdvd
      have hj1 : j = 1 := by
        have hj_pos : 0 < j := by
          rcases Nat.eq_zero_or_pos j with h0 | h0
          · rw [h0] at hj
            omega
          · exact h0
        have hj_lt : j < 2 := by
          by_contra h
          push Not at h
          nlinarith
        omega
      rw [hj1] at hj
      have ha_eq : a = 2 * d + 1 := by omega
      -- b + 2 = 2(d + 1)k, so b = 2b'
      have hk' : b + 2 = 2 * ((d + 1) * k) := by rw [hk, ha_eq]; ring
      obtain ⟨b', hb'⟩ : ∃ b', b = 2 * b' := ⟨(d + 1) * k - 1, by omega⟩
      -- dividing by 2: (2d + 1)^2 = b' * d
      have hsq : (2 * d + 1) ^ 2 = b' * d := by
        rw [ha_eq, hb'] at hd
        linarith
      -- d divides (2d + 1)^2 = d(4d + 4) + 1, so d divides 1
      have hd_dvd : d ∣ d * (4 * d + 4) + 1 := ⟨b', by rw [mul_comm d b', ← hsq]; ring⟩
      have hd1 : d = 1 := Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right d _)).mp hd_dvd)
      rw [hd1] at hsq ha_eq
      exact ⟨ha_eq, by omega⟩

  · intro h
    rcases h with ⟨rfl, rfl ⟩ | ⟨rfl, rfl ⟩ | ⟨rfl, rfl ⟩ | ⟨hl, rfl ⟩
    · dsimp[ValidPair]; decide
    · dsimp[ValidPair]; decide
    · dsimp[ValidPair]; decide
    · dsimp[ValidPair]
      exact ⟨hl, by omega, ⟨2, by ring⟩, ⟨a, by ring⟩⟩

end Olympiad.Problems.«JBMO».«Y2026».«P2»
