import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Divisors
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Compiled examples for CHEATSHEET.md. Not part of the library build. -/

-- logic
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩
example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩
example (P Q R : Prop) (h : P ∨ Q) (hpr : P → R) (hqr : Q → R) : R := by
  rcases h with hp | hq
  · exact hpr hp
  · exact hqr hq
example : ∃ n : ℕ, n * n = 49 := by
  use 7
example : ∃ x : ℤ, 2 * x + 1 = 7 ∧ x > 0 := by
  refine ⟨3, ?_, ?_⟩
  · norm_num
  · norm_num
example (f : ℕ → ℕ) (h : ∃ c, ∀ x, f x = c) : f 1 = f 2 := by
  obtain ⟨c, hc⟩ := h
  rw [hc 1, hc 2]
example (x : ℝ) : x = 2 ↔ x + 1 = 3 := by
  constructor
  · intro h
    linarith
  · intro h
    linarith
example (x : ℕ) (h : x < 3) : x ≠ 5 := by
  intro h5
  omega
example (P : Prop) (hp : P) (hnp : ¬P) : 1 = 2 := by
  exfalso
  exact hnp hp
example (n : ℕ) (h : n + 1 = 0) : False := by
  omega
example (n : ℕ) : n = 0 ∨ 0 < n := by
  by_cases h : n = 0
  · left; exact h
  · right; omega
example (n : ℕ) (h : n ^ 2 < 10) : n ≤ 3 := by
  by_contra hc
  push Not at hc
  nlinarith

-- rewriting
example (a b c : ℝ) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]
example (a b : ℝ) (h : a = b) (hb : b > 0) : a > 0 := by
  rw [h]
  exact hb
example (a b : ℝ) (h : a = b) (ha : a > 0) : b > 0 := by
  rw [← h]
  exact ha
example (a b : ℝ) (h : a = b) (ha : a > 0) : b > 0 := by
  rw [h] at ha
  exact ha
example (a : ℝ) : (a + 0) * 1 = a := by
  simp
example (x : ℕ) (h : x + 0 = 5) : x = 5 := by
  simpa using h
def double (n : ℕ) : ℕ := 2 * n
example : double 3 = 6 := by
  unfold double
  rfl
example (n : ℕ) : double n = n + n := by
  simp only [double]
  ring
example (n : ℕ) : double n = n + n := by
  dsimp [double]
  omega

-- algebra closers
example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring
example (x y : ℝ) (h1 : x + y = 5) (h2 : x - y = 1) : x = 3 := by
  linarith
example (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a ^ 2 * b + 3 / a := by
  positivity
example (n m : ℕ) (h1 : n < m) (h2 : m < n + 2) : m = n + 1 := by
  omega
example : (2 : ℤ) ^ 10 - 24 = 1000 := by
  norm_num
example : ¬ 5 ∣ 2 ^ 3 + 3 ^ 8 := by
  norm_num
example : 3 ^ 6 % 7 = 1 := by
  decide
example (x : ℝ) (hx : x ≠ 0) : (x ^ 2 + x) / x = x + 1 := by
  field_simp

-- inequalities
example (a b : ℝ) (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  gcongr
example (x y : ℝ) (hy : 0 < y) (h : 3 * y ≤ 5 * x) : 3 / 5 ≤ x / y := by
  rw [le_div_iff₀ hy]
  linarith
example (a d D : ℝ) (ha : 0 ≤ a) (hd : 0 < d) (h : d ≤ D) : a / D ≤ a / d :=
  div_le_div_of_nonneg_left ha hd h
example (a : ℝ) (ha : 1 ≤ a) : a ≤ a ^ 3 := by
  calc a = a * 1 * 1 := by ring
    _ ≤ a * a * a := by gcongr
    _ = a ^ 3 := by ring

-- case analysis
example (k : ℤ) (h : k * (k - 2) = 0) : k = 0 ∨ k = 2 := by
  rcases mul_eq_zero.mp h with h0 | h2
  · left; exact h0
  · right; linarith
example (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 4) : n ^ 2 ≤ 16 := by
  interval_cases n <;> norm_num
example (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
  omega
example (a b : ℕ) (h : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) : a + b = 3 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

-- number theory
example : (6 : ℕ) ∣ 42 := by
  norm_num
example (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c :=
  dvd_trans h1 h2
example (n : ℕ) : 3 ∣ 3 * n + 6 := by
  exact ⟨n + 2, by ring⟩
example (a b : ℕ) (h : a ∣ b) : a ∣ b * 5 := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k * 5, by ring⟩
example (g : ℕ) (h : g ∣ 35) : g = 1 ∨ g = 5 ∨ g = 7 ∨ g = 35 := by
  have hg : g ∈ Nat.divisors 35 := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
  change g ∈ ({1, 5, 7, 35} : Finset ℕ) at hg
  simpa using hg
example (n : ℕ) : 2 ^ (3 * n) ≡ 1 [MOD 7] := by
  have h : 2 ^ 3 ≡ 1 [MOD 7] := by decide
  simpa [Nat.pow_mul] using h.pow n
example : 3 ^ 6 ≡ 1 [MOD 7] := by
  simpa using Nat.ModEq.pow_card_sub_one_eq_one (p := 7) (n := 3) (by decide) (by decide)
example (a b : ℕ) (ha : a ≡ 3 [MOD 7]) (hb : b ≡ 4 [MOD 7]) : 7 ∣ a + b := by
  have h : a + b ≡ 0 [MOD 7] := (ha.add hb).trans (by decide)
  exact Nat.modEq_zero_iff_dvd.mp h
example (n : ℕ) (h : n % 2 = 1) : Odd n := by
  exact Nat.odd_iff.mpr h
example (n : ℕ) (hn : 0 < n) : Odd (2 * n - 1) := by
  refine ⟨n - 1, ?_⟩
  omega
example : (Finset.range 5).gcd (fun n => 6 * n + 12) ∣ 12 := by
  have h := Finset.gcd_dvd (s := Finset.range 5) (f := fun n => 6 * n + 12) (b := 0) (by simp)
  simpa using h
example (f : ℕ → ℕ) (hf : ∀ n, 3 ∣ f n) : 3 ∣ (Finset.range 10).gcd f := by
  apply Finset.dvd_gcd
  intro n _
  exact hf n
example (n : ℕ) (h : 5 ≤ n) : n - 3 + 3 = n := by
  omega
example : (7 : ℕ) - 10 = 0 := by
  norm_num
example : (7 : ℕ) / 2 = 3 := by
  norm_num

-- induction
example (n : ℕ) : 2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring
example (n : ℕ) (hn : 4 ≤ n) : 2 ^ n ≥ n ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    nlinarith
example (f : ℤ → ℤ) (h0 : f 0 = 0) (hs : ∀ n, f (n + 1) = f n + 2) (hp : ∀ n, f (n - 1) = f n - 2) :
    ∀ x, f x = 2 * x := by
  intro x
  refine Int.inductionOn' (motive := fun n => f n = 2 * n) x 0 ?_ ?_ ?_
  · simp [h0]
  · intro n _ ih
    rw [hs, ih]
    ring
  · intro n _ ih
    rw [hp, ih]
    ring

-- sums and products
example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), (2 * i + 1) = (n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring
example (n : ℕ) : ∏ _i ∈ Finset.range n, (3 : ℕ) = 3 ^ n := by
  rw [Finset.prod_const, Finset.card_range]
example (n : ℕ) : ∑ i ∈ Finset.range n, i = n * (n - 1) / 2 :=
  Finset.sum_range_id n
example (n : ℕ) : ∏ i ∈ Finset.range n, (i + 1) ≤ ∏ _i ∈ Finset.range n, n := by
  gcongr with i hi
  have := Finset.mem_range.mp hi
  omega

-- functional equations
example (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) = f x + f y) : f 0 = 0 := by
  have h := hf 0 0
  simp at h
  linarith
example (f : ℤ → ℤ) (hf : ∀ x, f x = 2 * x + 5) : ∀ a b, f (a + b) + 5 = f a + f b := by
  intro a b
  simp only [hf]
  ring

-- casts
example (n : ℕ) (h : (n : ℝ) = 3) : n = 3 := by
  exact_mod_cast h
example (a b : ℕ) : ((a + b : ℕ) : ℝ) = (a : ℝ) + b := by
  push_cast
  ring
example (a b : ℕ) (h : b ≤ a) : ((a - b : ℕ) : ℤ) = a - b := by
  omega

-- decide on finite search
example : ∀ a : Fin 10, ∀ b : Fin 10, a.val * b.val = 12 → a.val + b.val ≥ 7 := by
  decide

-- set / let
example (a b : ℝ) (h : a + b = 2) : (a + b) ^ 2 + (a + b) = 6 := by
  set s := a + b with hs
  rw [h]
  norm_num

-- case analysis in depth (section 6)
def ValidPair (a b : ℕ) : Prop :=
0 < a ∧ 0 < b ∧
a + 1 ∣ b + 2 ∧ b ∣ 2 * a ^ 2

-- version A: bullets
example (a b : ℕ) (h : (a = 2 ∧ b = 1) ∨ (a = 3 ∧ b = 2) ∨ (a = 3 ∧ b = 18) ∨ (0 < a ∧ b = 2 * a)) :
    ValidPair a b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ha, rfl⟩
  · dsimp [ValidPair]; decide
  · dsimp [ValidPair]; decide
  · dsimp [ValidPair]; decide
  · refine ⟨ha, by omega, ⟨2, by ring⟩, ⟨a, by ring⟩⟩

-- version B: one line for the concrete cases, then the family
example (a b : ℕ) (h : (a = 2 ∧ b = 1) ∨ (a = 3 ∧ b = 2) ∨ (a = 3 ∧ b = 18) ∨ (0 < a ∧ b = 2 * a)) :
    ValidPair a b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ha, rfl⟩
  iterate 3 (dsimp [ValidPair]; decide)
  exact ⟨ha, by omega, ⟨2, by ring⟩, ⟨a, by ring⟩⟩

-- version C: peel off the family first
example (a b : ℕ) (h : (a = 2 ∧ b = 1) ∨ (a = 3 ∧ b = 2) ∨ (a = 3 ∧ b = 18) ∨ (0 < a ∧ b = 2 * a)) :
    ValidPair a b := by
  rcases h with h | h | h | ⟨ha, rfl⟩
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := h; dsimp [ValidPair]; decide)
    | exact ⟨ha, by omega, ⟨2, by ring⟩, ⟨a, by ring⟩⟩

example : ValidPair 3 18 := by unfold ValidPair; decide
example : ValidPair 3 18 := by norm_num [ValidPair]

-- obtain with or
example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  obtain rfl | rfl | rfl := h <;> norm_num
example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  omega
example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  rcases h with h1 | h2 | h3
  · rw [h1]; norm_num
  · omega
  · omega
example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  cases h with
  | inl h1 => omega
  | inr h23 =>
    cases h23 with
    | inl h2 => omega
    | inr h3 => omega
example (P Q R : Prop) (hp : P) : P ∨ Q ∨ R := by
  left; exact hp
example (P Q R : Prop) (hr : R) : P ∨ Q ∨ R := by
  right; right; exact hr
example (P Q R : Prop) (hq : Q) : P ∨ Q ∨ R := Or.inr (Or.inl hq)
example (n : ℕ) (h : n % 2 = 1) : n % 4 = 1 ∨ n % 4 = 3 := by
  omega
example (n : ℕ) (h : n < 3) : n * n < 5 := by
  interval_cases n <;> simp
example (n : ℕ) (h : n < 3) : n * n ≠ 3 := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> decide
example (x : ℤ) (h : (x - 1) * (x - 2) = 0) : x = 1 ∨ x = 2 := by
  rcases mul_eq_zero.mp h with h | h
  · left; linarith
  · right; linarith
example (n : ℕ) : Even n ∨ Odd n := by
  rcases Nat.even_or_odd n with h | h
  · exact Or.inl h
  · exact Or.inr h
example (x : ℝ) : |x| ≥ 0 := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]; exact h
  · rw [abs_of_neg h]; linarith
example (a b : ℕ) : a ≤ b ∨ b < a := by
  rcases Nat.lt_or_ge b a with h | h
  · right; exact h
  · left; exact h
example (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left; ring_nf; omega
  · right; ring_nf; omega
example (n : ℕ) (hn : 0 < n) : n = 1 ∨ 2 ≤ n := by
  rcases n with _ | _ | m
  · omega
  · left; rfl
  · right; omega
example (a b : ℕ) (h : a = 1 ∧ b = 2 ∨ a = 2 ∧ b = 1) : a * b = 2 := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  all_goals subst ha hb; rfl
example (P Q : Prop) (h : P ∨ Q) (hp : ¬P) : Q := by
  rcases h with h | h
  · exact absurd h hp
  · exact h
example (P Q : Prop) (h : P ∨ Q) (hp : ¬P) : Q := h.resolve_left hp
example (n : ℕ) (h : n ≤ 2) : n = 0 ∨ n = 1 ∨ n = 2 := by
  interval_cases n <;> simp
example (n : ℕ) : n = 0 ∨ n ≠ 0 := by
  rcases em (n = 0) with h | h
  · exact Or.inl h
  · exact Or.inr h
example (n : ℕ) (h : n ≤ 2) : n = 0 ∨ n = 1 ∨ n = 2 := by
  interval_cases n
  · left; rfl
  · right; left; rfl
  · right; right; rfl
example (n : ℕ) : n * (n + 1) % 2 = 0 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega
