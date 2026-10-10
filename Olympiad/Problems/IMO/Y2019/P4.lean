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
import Olympiad.Utils.NumberTheory



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
    obtain ⟨hk_pos, hn_pos, heq⟩ := h
    let T : ℕ := n * (n - 1) / 2

    -- Each factor has exactly i powers of 2
    have hfactor : ∀ i < n, (2 ^ n - 2 ^ i).factorization 2 = i := by
      intro i hi
      have hm : 0 < n - i := by omega
      have hexp : i + (n - i) = n := Nat.add_sub_of_le (by omega)
      have hidentity :
          2 ^ n - 2 ^ i = 2 ^ i * (2 ^ (n - i) - 1) := by
        rw [mul_tsub, mul_one, ← pow_add, hexp]
      have hodd : Odd (2 ^ (n - i) - 1) :=
        Olympiad.Utils.NumberTheory.two_pow_sub_one_odd (n - i) hm
      have hnotdvd : ¬ 2 ∣ 2 ^ (n - i) - 1 :=
        hodd.not_two_dvd_nat
      have hnonzero : 2 ^ (n - i) - 1 ≠ 0 := by
        have hp : 1 < 2 ^ (n - i) := by
          obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - i ≠ 0)
          rw [hj, pow_succ]
          have := pow_pos (by omega : 0 < (2 : ℕ)) j
          omega
        omega
      rw [hidentity]
      rw [Nat.factorization_mul (pow_ne_zero i (by decide)) hnonzero]
      simp only [Finsupp.add_apply]
      rw [Nat.factorization_pow_self (Nat.prime_two)]
      simp [Nat.factorization_eq_zero_of_not_dvd hnotdvd]

    -- The valuation of the product is the sum of the valuations
    have hprod_val :
        (∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i)).factorization 2 =
          ∑ i ∈ Finset.range n, i := by
      have hne : ∀ i ∈ Finset.range n, 2 ^ n - 2 ^ i ≠ 0 := by
        intro i hi
        have hlt : 2 ^ i < 2 ^ n :=
          Nat.pow_lt_pow_right (by norm_num) (Finset.mem_range.mp hi)
        omega
      rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
      exact Finset.sum_congr rfl fun i hi => hfactor i (Finset.mem_range.mp hi)

    -- The sum is n(n-1)/2
    have hsum : (∑ i ∈ Finset.range n, i) = T := by
      exact Finset.sum_range_id n

    -- find the factors of two in rhs
    have hval : (k.factorial).factorization 2 = T := by
      rw [heq, hprod_val, hsum]

    -- the factors of 2 in k! are less than k
    have hval_lt : (k.factorial).factorization 2 < k := by
      have h := Nat.emultiplicity_two_factorial_lt (by omega : k ≠ 0)
      -- k! ≠ 0, so its multiplicity is finite and equals the factorization
      have hfin : FiniteMultiplicity 2 k.factorial :=
        Nat.finiteMultiplicity_iff.mpr ⟨by decide, Nat.factorial_pos k⟩
      rw [hfin.emultiplicity_eq_multiplicity,
        Nat.multiplicity_eq_factorization Nat.prime_two] at h
      exact_mod_cast h

    -- conclude T<k
    have ht_lt_k : T < k := by
      omega

    --rhs is less than this
    have hprod_le : (∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i)) ≤ 2 ^ (n * n) := by
      calc ∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i)
          ≤ ∏ _i ∈ Finset.range n, 2 ^ n := by
            gcongr
            exact Nat.sub_le _ _
        _ = 2 ^ (n * n) := by
            rw [Finset.prod_const, Finset.card_range, ← pow_mul]

    -- for all n>=6, T! > this
    have hlarge : 6 ≤ n → 2 ^ (n * n) < T.factorial := by
      -- induction on m: going from m to m+1, the lhs gains at most a factor 16^m
      -- and the rhs gains at least (T+1)^m ≥ 16^m
      have hgen : ∀ m, 6 ≤ m → 2 ^ (m * m) < (m * (m - 1) / 2).factorial := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base => decide
        | succ m hm ih =>
          have hT_succ : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m := by
            rw [← Finset.sum_range_id, ← Finset.sum_range_id, Finset.sum_range_succ]
          have hmul : 30 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega : 5 ≤ m - 1)
          rw [hT_succ]
          set A := m * (m - 1) / 2
          have hA15 : 15 ≤ A := by omega
          calc 2 ^ ((m + 1) * (m + 1))
              ≤ 2 ^ (m * m + 4 * m) := by
                gcongr
                nlinarith
            _ = 2 ^ (m * m) * 16 ^ m := by
                rw [pow_add, pow_mul 2 4 m]
                norm_num
            _ < A.factorial * 16 ^ m := by gcongr
            _ ≤ A.factorial * (A + 1) ^ m := by
                gcongr
                omega
            _ ≤ (A + m).factorial := Nat.factorial_mul_pow_le_factorial
      intro hn
      exact hgen n hn

    -- conclude n <= 5
    have hn_le5 : n ≤ 5 := by
      by_contra h
      have hn : 6 ≤ n := by omega
      have hT_fact_le : T.factorial ≤ k.factorial := by
        apply Nat.factorial_le
        omega
      have hbound := hlarge hn
      rw [heq] at hT_fact_le
      omega


    -- bound k, then check the remaining cases by hand
    have hk_le10 : k ≤ 10 := by
      by_contra h
      have hk_ge11 : 11 ≤ k := by omega
      have hfact_ge : (11 : ℕ).factorial ≤ k.factorial :=
        Nat.factorial_le hk_ge11
      have hpow_le : 2 ^ (n * n) ≤ 2 ^ 25 := by
        apply pow_le_pow_right₀ (by omega)
        nlinarith
      have hfact_bound : 2 ^ 25 < (11 : ℕ).factorial := by decide
      rw [heq] at hfact_ge
      omega

    have hsmall :
      ∀ a : Fin 11, ∀ b : Fin 6,
      0 < a.val → 0 < b.val →
      a.val.factorial =
        (∏ i ∈ Finset.range b.val, (2 ^ b.val - 2 ^ i)) →
      (a.val = 1 ∧ b.val = 1) ∨
      (a.val = 3 ∧ b.val = 2) := by
        decide

    exact hsmall ⟨k, by omega⟩ ⟨n, by omega⟩ hk_pos hn_pos heq


  · dsimp[ValidPair]
    intro h
    rcases h with ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl⟩ <;> decide




end Olympiad.Problems.«IMO».«Y2019».«P4»
