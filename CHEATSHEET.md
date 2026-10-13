# Lean 4 Olympiad Cheatsheet

A working reference for this repo (Lean `v4.34.1`, Mathlib `v4.34.1`).
Every example in sections 2–12 is also in `Olympiad/Examples/Cheatsheet.lean`, which
compiles, so you can open it and inspect any goal state.

---

## 1. Workflow

| Task | How |
| --- | --- |
| New problem file | `python3 scripts/new_problem.py JBMO 2026 3` |
| Check one file | `lake env lean Olympiad/Problems/JBMO/Y2026/P1.lean` |
| Build the library | `lake build` (only files imported from `Olympiad.lean`) |
| Placeholder proof | `sorry` (a warning; `warningAsError = true` makes it fail in `lake build`) |
| Look up a lemma's type | `#check Nat.mem_divisors` |
| Evaluate a computation | `#eval (Finset.range 5).sum id` |
| Let Lean search | `exact?`, `apply?`, `rw?`, `hint` (then paste the suggestion) |
| Leave a hole for later | `refine ⟨3, ?_⟩` — every `?_` becomes a new goal |

**File skeleton**

```lean
import Mathlib.Basic.Real.Basic        -- ℝ (Mathlib.Data.Real.Basic is deprecated here)
import Mathlib.Tactic.Linarith         -- linarith, nlinarith
import Mathlib.Tactic.Ring             -- ring, ring_nf
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.ModEq          -- a ≡ b [MOD n]
import Mathlib.NumberTheory.Divisors   -- Nat.divisors
import Mathlib.FieldTheory.Finite.Basic  -- Fermat's little theorem
import Mathlib.Algebra.GCDMonoid.Finset  -- Finset.gcd
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic  -- ∑, ∏

namespace Olympiad.Problems.«JBMO».«Y2026».«P1»

theorem problem ... := by
  sorry

end Olympiad.Problems.«JBMO».«Y2026».«P1»
```

An "unknown tactic" error almost always means a missing import.

**Typing symbols** (type then space): `\R` ℝ, `\N` ℕ, `\Z` ℤ, `\le` ≤, `\ge` ≥, `\ne` ≠,
`\mid` ∣ (divides — not the keyboard `|`), `\and` ∧, `\or` ∨, `\iff` ↔, `\to` →,
`\forall` ∀, `\exists` ∃, `\neg` ¬, `\<` ⟨, `\>` ⟩, `\sum` ∑, `\prod` ∏, `\in` ∈, `\.` ·.

---

## 2. What to do with each kind of goal

### Goal shape → first move

| Goal looks like | Use |
| --- | --- |
| `∀ x, P x` or `P → Q` | `intro x` / `intro h` |
| `P ∧ Q` | `constructor` or `exact ⟨hp, hq⟩` |
| `P ∨ Q` | `left` / `right` |
| `P ↔ Q` | `constructor`, then prove both `→` |
| `∃ x, P x` | `use 7` or `refine ⟨7, ?_⟩` |
| `¬P` or `a ≠ b` | `intro h` (now prove `False`) |
| `False` | `exact hnp hp`, `contradiction`, `omega`, `linarith`, `norm_num at h` |
| anything, by contradiction | `by_contra h` |
| anything, want to prove `False` instead | `exfalso` |
| `a = b` | `rfl`, `ring`, `simp`, `linarith`, `omega`, `norm_num`, `rw [...]` |
| `a ≤ b`, `a < b` | `linarith`, `nlinarith`, `omega`, `positivity`, `gcongr`, `calc` |
| `a ∣ b` | `norm_num`, `exact ⟨k, by ring⟩`, `dvd_trans` |
| `a ≡ b [MOD n]` | `decide` (numbers), `.pow`, `.add`, `.mul`, `.trans` |
| statement about a finite range | `interval_cases`, `decide`, `omega` |

### Hypothesis shape → how to use it

| Hypothesis | Use |
| --- | --- |
| `h : P ∧ Q` | `obtain ⟨hp, hq⟩ := h` |
| `h : P ∨ Q` | `rcases h with hp \| hq` |
| `h : ∃ x, P x` | `obtain ⟨x, hx⟩ := h` |
| `h : ∀ x, P x` | `have h3 := h 3` or `specialize h 3` |
| `h : P → Q` and `hp : P` | `exact h hp` or `apply h` |
| `h : P ↔ Q` | `h.mp hp : Q`, `h.mpr hq : P`, or `rw [h]` |
| `h : a = b` | `rw [h]`, `rw [← h]`, `rw [h] at h2`, `subst` |
| `h : x = 3` (x a variable) | in patterns write `rfl` to substitute x away |
| `h : a * b = 0` | `rcases mul_eq_zero.mp h with h \| h` |
| `h : a ∣ b` | `obtain ⟨k, hk⟩ := h` (gives `b = a * k`) |

### Logic examples

```lean
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

example (n : ℕ) : n = 0 ∨ 0 < n := by
  by_cases h : n = 0
  · left; exact h
  · right; omega

example (n : ℕ) (h : n ^ 2 < 10) : n ≤ 3 := by
  by_contra hc
  push Not at hc        -- turns ¬(n ≤ 3) into 3 < n  (push_neg is deprecated)
  nlinarith
```

**Structuring**: `have name : stmt := by ...` proves an intermediate fact; `·` focuses
on one goal; `tac1 <;> tac2` runs `tac2` on every goal produced by `tac1`.

---

## 3. Rewriting and simplifying

| Tactic | What it does |
| --- | --- |
| `rw [h]` | replace LHS of `h` by RHS in the goal (`h` is an `=` or `↔`) |
| `rw [← h]` | replace RHS by LHS |
| `rw [h] at h2` | rewrite inside a hypothesis |
| `rw [h1, h2, h3]` | several in sequence; closes the goal with `rfl` if possible |
| `simp` | simplify with all `@[simp]` lemmas; may close the goal |
| `simp only [a, b]` | simplify using only these lemmas / definitions (predictable) |
| `simp at h` | simplify a hypothesis |
| `simp [hf]` | simp plus your hypothesis `hf` as a rewrite rule |
| `simpa using h` | simp both goal and `h`, then close with `h` |
| `unfold f` / `dsimp [f]` | expand a definition |
| `change e` / `change e at h` | replace by something definitionally equal |
| `show e` | same as `change`, for documenting the goal |
| `set s := e with hs` | name a subexpression everywhere |
| `let g := fun x => ...` | introduce a local definition |
| `norm_num` / `norm_num at h` | evaluate numeric expressions |
| `ring_nf` | normalize polynomial expressions (also `at h`) |
| `field_simp` | clear denominators (needs `≠ 0` facts in context) |
| `push_cast` | move casts `↑` inward |

```lean
example (a b c : ℝ) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

example (a b : ℝ) (h : a = b) (ha : a > 0) : b > 0 := by
  rw [← h]
  exact ha

example (a b : ℝ) (h : a = b) (ha : a > 0) : b > 0 := by
  rw [h] at ha
  exact ha

example (x : ℕ) (h : x + 0 = 5) : x = 5 := by
  simpa using h

def double (n : ℕ) : ℕ := 2 * n

example : double 3 = 6 := by
  unfold double
  rfl

example (n : ℕ) : double n = n + n := by
  simp only [double]
  ring

example (a b : ℝ) (h : a + b = 2) : (a + b) ^ 2 + (a + b) = 6 := by
  set s := a + b with hs
  rw [h]
  norm_num
```

---

## 4. Closing tactics (the "finishers")

| Tactic | Proves | Notes |
| --- | --- | --- |
| `rfl` | `a = a` up to definitions | |
| `ring` | commutative ring identities | no hypotheses used; fails on `≤` |
| `linarith` | linear (in)equalities from hypotheses | treats `x*y`, `x^2`, `a/b` as atoms |
| `nlinarith [h1, h2]` | nonlinear; multiplies pairs of hypotheses | give hints like `sq_nonneg (a - b)` |
| `positivity` | `0 < e`, `0 ≤ e`, `e ≠ 0` | from structure of `e` and positivity hyps |
| `omega` | linear arithmetic over ℕ and ℤ | handles `-` truncation, `/`, `%` by constants |
| `norm_num` | numeric facts, `∣` on numerals, primality | `norm_num [f]` unfolds `f` first |
| `decide` | any decidable statement with small numbers | `% 7`, `MOD`, bounded `∀` over `Fin n` |
| `field_simp` | equations with fractions | often followed by `ring` |
| `exact_mod_cast h` | `h` up to casts | |
| `gcongr` | `f a ≤ f b` from `a ≤ b` | see section 5 |

```lean
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
```

**Choosing**: equality with no hypotheses → `ring`. Linear facts from hypotheses →
`linarith` (ℝ, ℚ) or `omega` (ℕ, ℤ). Squares and products → `nlinarith` with
`sq_nonneg` hints. Concrete numbers → `norm_num` or `decide`.

---

## 5. Inequalities

**Standard hints for `nlinarith`**: `sq_nonneg (a - b)`, `sq_nonneg (a + b)`,
`sq_nonneg (a ^ 2 - 1)`, `mul_pos ha hb`, `mul_nonneg ha.le hb.le`, `sq_abs a`.
If `nlinarith` fails, first prove the needed auxiliary inequalities as `have`s.

**Divisions**

| Lemma | Statement |
| --- | --- |
| `le_div_iff₀ (hc : 0 < c)` | `a ≤ b / c ↔ a * c ≤ b` |
| `div_le_iff₀ (hc : 0 < c)` | `a / c ≤ b ↔ a ≤ b * c` |
| `div_le_div_of_nonneg_left` | `0 ≤ a → 0 < d → d ≤ D → a / D ≤ a / d` |
| `add_div` | `(a + b) / c = a / c + b / c` |
| `ge_iff_le` | `a ≥ b ↔ b ≤ a` (rewrite `≥` before `le_div_iff₀`) |

```lean
example (x y : ℝ) (hy : 0 < y) (h : 3 * y ≤ 5 * x) : 3 / 5 ≤ x / y := by
  rw [le_div_iff₀ hy]
  linarith

example (a d D : ℝ) (ha : 0 ≤ a) (hd : 0 < d) (h : d ≤ D) : a / D ≤ a / d :=
  div_le_div_of_nonneg_left ha hd h

example (a b : ℝ) (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  gcongr
```

**`gcongr`** reduces `f(stuff) ≤ f(other stuff)` to comparisons of the parts that differ,
and discharges positivity side goals automatically. When it splits too far, give a
pattern: `?_` marks the parts that should be compared, `_` the parts that stay the same.

```lean
-- only the denominators differ
gcongr _ / ?_ + _ / ?_ + _ / ?_
-- products: ∏ f i ≤ ∏ g i, getting the index as i, hi
gcongr with i hi
```

**`calc` chains** are the cleanest way to write an inequality proof:

```lean
example (a : ℝ) (ha : 1 ≤ a) : a ≤ a ^ 3 := by
  calc a = a * 1 * 1 := by ring
    _ ≤ a * a * a := by gcongr
    _ = a ^ 3 := by ring
```

**Worked example (JBMO 2026 P1)** — the three-step pattern
"bound below by a single fraction, split, compare denominators":

```lean
theorem problem_short (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a^2 + b^2 + c^2 ≥ 3) :
    a^4 / (a^2 + 2*b + 2*c) + b^4 / (b^2 + 2*c + 2*a) + c^4 / (c^2 + 2*a + 2*b) ≥ 3/5 := by
  calc 3/5 ≤ (a^4 + b^4 + c^4) / (a^2 + b^2 + c^2 + 2) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (c^2 - 1)]
    _ = a^4 / (a^2 + b^2 + c^2 + 2) + b^4 / (a^2 + b^2 + c^2 + 2)
        + c^4 / (a^2 + b^2 + c^2 + 2) := by ring
    _ ≤ _ := by
        gcongr _ / ?_ + _ / ?_ + _ / ?_ <;>
          nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
```

---

## 6. Case analysis

### 6.1 How `∨` is built

`P ∨ Q ∨ R` means `P ∨ (Q ∨ R)`: an "or" of many things is a chain of two-way "or"s
nested to the **right**. Every case-analysis tactic below is a convenient way to take
that chain apart (when it is a hypothesis) or pick one branch of it (when it is the goal).

### 6.2 Proving an `∨` goal: pick a branch

| Want to prove | Tactic | Term |
| --- | --- | --- |
| the 1st option of `P ∨ Q ∨ R` | `left` | `Or.inl hp` |
| the 2nd option | `right; left` | `Or.inr (Or.inl hq)` |
| the 3rd option | `right; right` | `Or.inr (Or.inr hr)` |
| any option, by arithmetic | `omega`, `simp`, `decide`, `norm_num` | |

```lean
example (P Q R : Prop) (hp : P) : P ∨ Q ∨ R := by
  left; exact hp

example (P Q R : Prop) (hr : R) : P ∨ Q ∨ R := by
  right; right; exact hr

example (P Q R : Prop) (hq : Q) : P ∨ Q ∨ R := Or.inr (Or.inl hq)

example (n : ℕ) (h : n % 2 = 1) : n % 4 = 1 ∨ n % 4 = 3 := by
  omega        -- omega proves ∨-goals of linear facts directly
```

Commit to a branch only when you know it's the right one; `left` on a false option
leaves you with an unprovable goal.

### 6.3 Using an `∨` hypothesis: `rcases`

`rcases h with pat` destructs `h` according to a **pattern**:

| Pattern piece | Meaning |
| --- | --- |
| `h1 \| h2 \| h3` | split an `∨`; one new goal per alternative, hypotheses named `h1`, `h2`, `h3` |
| `⟨ha, hb⟩` | split an `∧` (or `∃`, `↔`) into its parts |
| `rfl` | the part is `x = value`: substitute it everywhere and drop it |
| `_` | discard this part |
| `-` | clear it entirely |

Patterns nest: `⟨rfl, rfl⟩ | ⟨ha, rfl⟩` means "two alternatives; in the first, both parts
are equations to substitute; in the second, keep the first part as `ha` and substitute
the second."

**Names in a pattern are just names.** Writing `⟨linarith, rfl⟩` does *not* run
`linarith`; it creates a hypothesis called `linarith`. Tactics go after the `rcases`.

**`rfl` needs a variable on one side.** `rfl` on `b = 2 * a` substitutes `b := 2 * a`
(fine, `b` is a variable). `rfl` on `0 < a` is an error, since it's not an equation.

```lean
example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  rcases h with h1 | h2 | h3
  · rw [h1]; norm_num
  · omega
  · omega

example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  obtain rfl | rfl | rfl := h <;> norm_num     -- obtain = rcases with the pattern first

example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  omega                                         -- often the whole case split is unnecessary

example (a b : ℕ) (h : a = 1 ∧ b = 2 ∨ a = 2 ∧ b = 1) : a * b = 2 := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  all_goals subst ha hb; rfl
```

The same split done by hand with `cases` (what `rcases` does internally):

```lean
example (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  cases h with
  | inl h1 => omega
  | inr h23 =>
    cases h23 with
    | inl h2 => omega
    | inr h3 => omega
```

Eliminating one option instead of splitting: `h.resolve_left hnp : Q` from
`h : P ∨ Q` and `hnp : ¬P` (and `h.resolve_right`).

```lean
example (P Q : Prop) (h : P ∨ Q) (hp : ¬P) : Q := h.resolve_left hp
```

### 6.4 Handling the cases after the split

After `rcases` you have several goals. Choose how to handle them:

| Situation | Write |
| --- | --- |
| each case needs different work | one `·` bullet per case, in order |
| every case closes the same way | `rcases ... <;> tac` |
| the same tactic for the first k cases | `iterate k (tac)` then handle the rest |
| apply to all remaining goals | `all_goals tac` |
| try a tactic, ignore failure | `try tac`, e.g. `<;> try decide` |
| try alternatives per goal | `first \| tac1 \| tac2` |
| run several tactics as one unit | `(tac1; tac2)` |

`<;>` binds left to right: `rcases ... <;> dsimp [f] <;> decide` runs `dsimp` on every
case, then `decide` on every result. If *any* case fails, the whole line fails, so the
error may come from just one case. Comment out the `<;> ...` part to see all goals.

### 6.5 Worked example: checking an answer set (JBMO 2026 P2)

The reverse direction of a "determine all" problem: every listed answer works.

```lean
def ValidPair (a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ a + 1 ∣ b + 2 ∧ b ∣ 2 * a ^ 2
```

**What goes wrong** with
`rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨linarith, rfl⟩ <;> dsimp [ValidPair] <;> decide`:
the first three cases become concrete (`ValidPair 2 1`, ...) and `decide` checks them.
The fourth case is `ValidPair a (2 * a)` for an *arbitrary* `a`, an infinite family, and
`decide` can only evaluate closed statements, hence
"Expected type must not contain free variables". (`linarith` there is only a hypothesis
name for `0 < a`.)

**Fix**: decide the concrete cases, prove the family by hand.

```lean
-- bullets: clearest
example (a b : ℕ) (h : (a = 2 ∧ b = 1) ∨ (a = 3 ∧ b = 2) ∨ (a = 3 ∧ b = 18)
    ∨ (0 < a ∧ b = 2 * a)) : ValidPair a b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ha, rfl⟩
  · dsimp [ValidPair]; decide
  · dsimp [ValidPair]; decide
  · dsimp [ValidPair]; decide
  · refine ⟨ha, by omega, ⟨2, by ring⟩, ⟨a, by ring⟩⟩

-- compact: the first three cases are identical
example (a b : ℕ) (h : (a = 2 ∧ b = 1) ∨ (a = 3 ∧ b = 2) ∨ (a = 3 ∧ b = 18)
    ∨ (0 < a ∧ b = 2 * a)) : ValidPair a b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ha, rfl⟩
  iterate 3 (dsimp [ValidPair]; decide)
  exact ⟨ha, by omega, ⟨2, by ring⟩, ⟨a, by ring⟩⟩
```

The family case, part by part: `ValidPair a (2 * a)` is
`0 < a ∧ 0 < 2 * a ∧ a + 1 ∣ 2 * a + 2 ∧ 2 * a ∣ 2 * a ^ 2`, so
`ha` proves the first, `omega` the second, and the divisibilities are witnessed
explicitly: `2 * a + 2 = (a + 1) * 2` and `2 * a ^ 2 = (2 * a) * a`.

`decide` needs the definition unfolded first: `decide` on `ValidPair 3 18` fails with
"failed to synthesize Decidable", while `unfold ValidPair; decide`,
`dsimp [ValidPair]; decide` or `norm_num [ValidPair]` all work.

### 6.6 Where case splits come from

| Source of cases | Tactic |
| --- | --- |
| any proposition `P` (true or not) | `by_cases h : P`; also `rcases em P with h \| h` |
| `a * b = 0` | `rcases mul_eq_zero.mp h with h \| h` |
| order of two numbers | `rcases le_or_gt a b with h \| h`, `Nat.lt_or_ge`, `lt_trichotomy a b` |
| even / odd | `rcases Nat.even_or_odd n with ⟨k, rfl⟩ \| ⟨k, rfl⟩` (n becomes `k + k` / `2 * k + 1`) |
| `n = 0`, `n = 1`, `n ≥ 2` | `rcases n with _ \| _ \| m` (n becomes `0`, `0 + 1`, `m + 1 + 1`) |
| small bounded variable | `interval_cases n` |
| a disjunction you can prove | `rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl \| rfl \| rfl` |
| residues mod m | `have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega`, then `rcases` |

```lean
example (x : ℤ) (h : (x - 1) * (x - 2) = 0) : x = 1 ∨ x = 2 := by
  rcases mul_eq_zero.mp h with h | h
  · left; linarith
  · right; linarith

example (x : ℝ) : |x| ≥ 0 := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]; exact h
  · rw [abs_of_neg h]; linarith

example (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left; ring_nf; omega
  · right; ring_nf; omega

example (n : ℕ) (hn : 0 < n) : n = 1 ∨ 2 ≤ n := by
  rcases n with _ | _ | m
  · omega
  · left; rfl
  · right; omega

example (n : ℕ) (h : n < 3) : n * n ≠ 3 := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> decide
```

**`interval_cases n`** needs a lower and an upper bound on `n` among the hypotheses
(for ℕ the lower bound 0 is automatic). It replaces `n` by each value in turn:

```lean
example (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 4) : n ^ 2 ≤ 16 := by
  interval_cases n <;> norm_num

example (n : ℕ) (h : n ≤ 2) : n = 0 ∨ n = 1 ∨ n = 2 := by
  interval_cases n
  · left; rfl
  · right; left; rfl
  · right; right; rfl
```

**`by_cases`** gives one goal with `h : P` and one with `h : ¬P`. Use it when the proof
naturally branches on a condition (IMO 2019 P1: "either `f` is identically zero or not"):

```lean
example (n : ℕ) : n = 0 ∨ 0 < n := by
  by_cases h : n = 0
  · left; exact h
  · right; omega
```

### 6.7 Finite brute force with `decide`

Once every variable is bounded (IMO 2019 P4 finish), state the claim over `Fin n` and let
`decide` check all cases, then instantiate it.

```lean
example : ∀ a : Fin 10, ∀ b : Fin 10, a.val * b.val = 12 → a.val + b.val ≥ 7 := by
  decide

-- using such a fact for concrete k, n with k ≤ 10, n ≤ 5:
-- exact hsmall ⟨k, by omega⟩ ⟨n, by omega⟩ hk_pos hn_pos heq
```

Keep the ranges small; `decide` gets slow quickly.

---

## 7. Number theory

### Divisibility

`a ∣ b` (typed `\mid`) unfolds to `∃ k, b = a * k`.

```lean
example : (6 : ℕ) ∣ 42 := by
  norm_num

example (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c :=
  dvd_trans h1 h2

example (n : ℕ) : 3 ∣ 3 * n + 6 := by
  exact ⟨n + 2, by ring⟩

example (a b : ℕ) (h : a ∣ b) : a ∣ b * 5 := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k * 5, by ring⟩
```

Useful lemmas: `dvd_trans`, `dvd_mul_right a b : a ∣ a * b`, `dvd_mul_left a b : a ∣ b * a`,
`(Nat.dvd_add_right h).mp : a ∣ b + c → a ∣ c`, `Nat.le_of_dvd (hb : 0 < b) : a ∣ b → a ≤ b`,
`Nat.Prime.dvd_mul`, `Nat.Coprime.dvd_of_dvd_mul_left`.

### Listing divisors

```lean
example (g : ℕ) (h : g ∣ 35) : g = 1 ∨ g = 5 ∨ g = 7 ∨ g = 35 := by
  have hg : g ∈ Nat.divisors 35 := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
  change g ∈ ({1, 5, 7, 35} : Finset ℕ) at hg
  simpa using hg
```

### Congruences `a ≡ b [MOD n]`

| Tool | Use |
| --- | --- |
| `decide` | concrete facts like `3 ^ 2 ≡ 2 [MOD 7]` |
| `h.pow n`, `h.add h'`, `h.mul h'`, `h.trans h'` | combine congruences |
| `Nat.modEq_zero_iff_dvd` | `a ≡ 0 [MOD n] ↔ n ∣ a` |
| `Nat.ModEq.pow_card_sub_one_eq_one` | Fermat: `p.Prime → n.Coprime p → n ^ (p - 1) ≡ 1 [MOD p]` |
| `Nat.pow_mul`, `Nat.pow_add` | reshape exponents with `simpa [Nat.pow_mul] using ...` |

```lean
example (n : ℕ) : 2 ^ (3 * n) ≡ 1 [MOD 7] := by
  have h : 2 ^ 3 ≡ 1 [MOD 7] := by decide
  simpa [Nat.pow_mul] using h.pow n

example : 3 ^ 6 ≡ 1 [MOD 7] := by
  simpa using Nat.ModEq.pow_card_sub_one_eq_one (p := 7) (n := 3) (by decide) (by decide)

example (a b : ℕ) (ha : a ≡ 3 [MOD 7]) (hb : b ≡ 4 [MOD 7]) : 7 ∣ a + b := by
  have h : a + b ≡ 0 [MOD 7] := (ha.add hb).trans (by decide)
  exact Nat.modEq_zero_iff_dvd.mp h
```

### gcd of a family (JBMO 1999 P2)

```lean
-- gcd divides each member
example : (Finset.range 5).gcd (fun n => 6 * n + 12) ∣ 12 := by
  have h := Finset.gcd_dvd (s := Finset.range 5) (f := fun n => 6 * n + 12) (b := 0) (by simp)
  simpa using h

-- anything dividing every member divides the gcd
example (f : ℕ → ℕ) (hf : ∀ n, 3 ∣ f n) : 3 ∣ (Finset.range 10).gcd f := by
  apply Finset.dvd_gcd
  intro n _
  exact hf n
```

### Parity

```lean
example (n : ℕ) (h : n % 2 = 1) : Odd n := by
  exact Nat.odd_iff.mpr h

example (n : ℕ) (hn : 0 < n) : Odd (2 * n - 1) := by
  refine ⟨n - 1, ?_⟩      -- Odd m means ∃ k, m = 2 * k + 1
  omega
```

Also: `Odd.not_two_dvd_nat`, `Nat.even_or_odd`, `Nat.even_iff`, and from this repo
`Olympiad.Utils.NumberTheory.two_pow_sub_one_odd`.

### p-adic valuations (IMO 2019 P4)

`n.factorization p` is the exponent of `p` in `n`.

| Lemma | Meaning |
| --- | --- |
| `Nat.factorization_mul ha hb` | `(a * b).factorization = a.factorization + b.factorization` |
| `Nat.factorization_pow_self hp` | exponent of `p` in `p ^ k` is `k` |
| `Nat.factorization_eq_zero_of_not_dvd` | `¬ p ∣ n → n.factorization p = 0` |
| `Nat.factorization_prod hne` | factorization of a `∏` is the `∑` |
| `Finsupp.add_apply`, `Finsupp.finsetSum_apply` | evaluate sums of factorizations |
| `Nat.emultiplicity_two_factorial_lt` | `v₂(k!) < k` |

### Natural-number arithmetic traps

```lean
example (n : ℕ) (h : 5 ≤ n) : n - 3 + 3 = n := by
  omega                     -- ℕ subtraction is truncated, omega knows this

example : (7 : ℕ) - 10 = 0 := by
  norm_num

example : (7 : ℕ) / 2 = 3 := by
  norm_num                  -- ℕ division rounds down
```

`ℕ` subtraction and division are the most common source of false-looking goals. Either
keep a hypothesis like `b ≤ a` around (so `omega` can use it), or move to `ℤ` / `ℝ`.

---

## 8. Induction

```lean
-- ordinary induction on ℕ
example (n : ℕ) : 2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

-- induction starting at a base value
example (n : ℕ) (hn : 4 ≤ n) : 2 ^ n ≥ n ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    nlinarith

-- induction on ℤ in both directions from 0
example (f : ℤ → ℤ) (h0 : f 0 = 0) (hs : ∀ n, f (n + 1) = f n + 2)
    (hp : ∀ n, f (n - 1) = f n - 2) : ∀ x, f x = 2 * x := by
  intro x
  refine Int.inductionOn' (motive := fun n => f n = 2 * n) x 0 ?_ ?_ ?_
  · simp [h0]
  · intro n _ ih
    rw [hs, ih]
    ring
  · intro n _ ih
    rw [hp, ih]
    ring
```

Strong induction: `induction n using Nat.strong_induction_on with | _ n ih => ...`
(`ih : ∀ m < n, P m`).
If the claim needs a general statement, prove `have hgen : ∀ m, ... := by intro m; induction m ...`
first, then apply it (as in IMO 2019 P4).

---

## 9. Sums and products

Notation: `∑ i ∈ Finset.range n, f i` is `f 0 + ... + f (n-1)`.

| Lemma | Statement |
| --- | --- |
| `Finset.sum_range_succ` | `∑ i ∈ range (n+1), f i = ∑ i ∈ range n, f i + f n` |
| `Finset.prod_range_succ` | same for `∏` |
| `Finset.sum_range_id n` | `∑ i ∈ range n, i = n * (n - 1) / 2` |
| `Finset.prod_const`, `Finset.card_range` | `∏ _i ∈ range n, c = c ^ n` |
| `Finset.sum_congr rfl h` | sums equal if terms equal on the range |
| `Finset.mem_range` | `i ∈ range n ↔ i < n` |

```lean
example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), (2 * i + 1) = (n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

example (n : ℕ) : ∏ _i ∈ Finset.range n, (3 : ℕ) = 3 ^ n := by
  rw [Finset.prod_const, Finset.card_range]

example (n : ℕ) : ∏ i ∈ Finset.range n, (i + 1) ≤ ∏ _i ∈ Finset.range n, n := by
  gcongr with i hi
  have := Finset.mem_range.mp hi
  omega
```

Factorials: `Nat.factorial_pos`, `Nat.factorial_le : m ≤ n → m ! ≤ n !`,
`Nat.factorial_mul_pow_le_factorial : m ! * (m + 1) ^ n ≤ (m + n) !`.
Powers: `pow_le_pow_right₀ (h : 1 ≤ a) : n ≤ m → a ^ n ≤ a ^ m`,
`Nat.pow_lt_pow_right (h : 1 < a) : n < m → a ^ n < a ^ m`, `pow_succ`, `pow_add`, `pow_mul`.

---

## 10. Functional equations (IMO 2019 P1)

1. **Substitute values**: `have h := hf 0 0`, `have h' := hf a 0`, ...
2. **Clean up**: `simp at h h'` (removes `+ 0`, `* 1`, ...).
3. **Combine**: `linarith` / `nlinarith` on the specialized equations.
4. **Shift the function**: `let g : ℤ → ℤ := fun x => f x - f 0`, then `dsimp [g]` to unfold it.
5. **Reuse a lemma**: `obtain ⟨k, hk⟩ := Olympiad.Utils.Algebra.additive_int_linear g hg_add`.
6. **Verify candidates** in the reverse direction: `simp only [hf]; ring`.

```lean
example (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) = f x + f y) : f 0 = 0 := by
  have h := hf 0 0
  simp at h
  linarith

example (f : ℤ → ℤ) (hf : ∀ x, f x = 2 * x + 5) :
    ∀ a b, f (a + b) + 5 = f a + f b := by
  intro a b
  simp only [hf]
  ring
```

---

## 11. Casts between ℕ, ℤ, ℝ

`(n : ℝ)` is displayed as `↑n`. Lean inserts casts automatically when types mix.

| Tool | Use |
| --- | --- |
| `exact_mod_cast h` / `norm_cast` | close or simplify goals differing only by casts |
| `push_cast` | push `↑` inward: `↑(a + b)` → `↑a + ↑b` |
| `zify`, `qify` | move a ℕ goal into ℤ / ℚ (pass `zify [hle]` to handle `-`) |
| `omega` | understands `ℕ → ℤ` casts directly |

```lean
example (n : ℕ) (h : (n : ℝ) = 3) : n = 3 := by
  exact_mod_cast h

example (a b : ℕ) : ((a + b : ℕ) : ℝ) = (a : ℝ) + b := by
  push_cast
  ring

example (a b : ℕ) (h : b ≤ a) : ((a - b : ℕ) : ℤ) = a - b := by
  omega
```

---

## 12. Writing problem statements

| Problem says | Lean |
| --- | --- |
| "Prove that ..." | `theorem problem (hyps) : claim := by` |
| "Determine all x such that P" | `theorem problem (x) : P x ↔ x = 1 ∨ x = 3` |
| "Find all functions" | `(∀ a b, eq) ↔ ((∀ x, f x = 0) ∨ ∃ c, ∀ x, f x = 2 * x + c)` |
| "positive integers" | `(a : ℕ) (ha : 0 < a)`, or include `0 < a` in a `def` |
| "positive reals" | `(a : ℝ) (ha : 0 < a)` |
| a named condition | `def ValidPair (a b : ℕ) : Prop := 0 < a ∧ 0 < b ∧ ...` |
| points in the plane | `abbrev Point := ℝ × ℝ`, coordinates `p.1`, `p.2` |
| a finite list of objects | `P : Fin 1999 → Point` with `Function.Injective P` |
| a set of objects | `Set.range P`, `{(0, 0), (20, 0)}`, `s ∪ t` |
| real-valued definitions | `noncomputable def` (anything using `/`, `|·|`, `√` on ℝ) |

Checklist for faithfulness:

- `a / b` on ℝ with `b = 0` is `0`; make sure denominators are provably nonzero.
- `a - b` and `a / b` on ℕ truncate / round down; prefer ℤ or ℝ if the problem means real subtraction.
- Write `2 * a`, never `2a`; `a^2` binds tighter than `*`.
- For "determine all", the right-hand side of the `↔` is the answer set; prove both directions.
- The reverse direction (checking the answers) is usually
  `rcases h with ⟨rfl, rfl⟩ | ... <;> decide` (or `norm_num [ValidPair]`).
  An infinite family like `b = 2 * a` needs its own case: `obtain ⟨ha, rfl⟩ := h`, then a direct proof.

---

## 13. When you're stuck

| Symptom | Try |
| --- | --- |
| don't know the lemma name | `exact?`, `apply?`, `rw?`; guess names like `Nat.mul_le_mul`, `add_pow_two` |
| `linarith failed` | add the missing fact with `have`; for products use `nlinarith [...]` |
| `nlinarith failed` | give better hints, or split into smaller `have`s |
| `omega could not prove` | it ignores nonlinear terms; first `have h : x * y = ... := by ring` |
| `simp made no progress` | use `simp only [...]`, `rw`, or `norm_num` |
| `motive is not type correct` in `rw` | use `simp only [h]` or `conv` instead |
| `unknown identifier` / deprecated | name changed; `exact?` or search Mathlib docs |
| `unknown tactic` | missing import |
| goal has `↑` everywhere | `push_cast`, `norm_cast`, `exact_mod_cast` |
| goal looks false | check ℕ subtraction/division and whether a hypothesis was lost |
| `decide` times out | range too large; bound more tightly first, or use `interval_cases` |

Deprecations seen in this Mathlib version: `push_neg` → `push Not`,
`Finset.prod_le_prod'` → `Finset.prod_le_prod` (or just `gcongr`),
`Mathlib.Data.Real.Basic` → `Mathlib.Basic.Real.Basic`.
