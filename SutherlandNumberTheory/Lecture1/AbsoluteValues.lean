import VersoManual
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.code.warnLineLength 90

#doc (Manual) "Absolute Values" =>
%%%
tag := "absolute-values"
number := false
%%%

We begin with the general notion of an absolute value on a field; a reference for much of this material is \[4, Chapter 1\].

# Definition 1.2
%%%
number := false
%%%

_Definition 1.2._ An _absolute value_ on a field $`k`$ is a map $`\lvert \cdot \rvert \colon k \to \mathbb{R}_{\geq 0}`$ such that for all $`x, y \in k`$ the following hold:

1. $`\lvert x \rvert = 0`$ if and only if $`x = 0`$;
2. $`\lvert xy \rvert = \lvert x \rvert \lvert y \rvert`$;
3. $`\lvert x + y \rvert \leq \lvert x \rvert + \lvert y \rvert`$.

If the stronger condition

4. $`\lvert x + y \rvert \leq \max(\lvert x \rvert, \lvert y \rvert)`$

also holds, then the absolute value is _nonarchimedean_; otherwise it is _archimedean_.

```lean
/-- Definition 1.2: An absolute value on a field k is captured by Mathlib's
`AbsoluteValue k ℝ`. The nonarchimedean property is `IsNonarchimedean f`. -/
def absoluteValue_def (k : Type*) [Field k] := AbsoluteValue k ℝ

def isNonarchimedean_def {k : Type*} [Field k] (f : AbsoluteValue k ℝ) :=
  IsNonarchimedean f
```

# Example 1.3
%%%
number := false
%%%

_Example 1.3._ The map $`\lvert \cdot \rvert \colon k \to \mathbb{R}_{\geq 0}`$ defined by

$$`\lvert x \rvert = \begin{cases} 1 & \text{if } x \neq 0, \\ 0 & \text{if } x = 0, \end{cases}`$$

is the _trivial absolute value_ on $`k`$. It is nonarchimedean.

```lean
/-- Example 1.3: The trivial absolute value exists on any field. -/
noncomputable def trivialAbsoluteValue (k : Type*) [DecidableEq k] [Field k] :
    AbsoluteValue k ℝ :=
  AbsoluteValue.trivial

/-- The trivial absolute value maps nonzero elements to 1. -/
theorem trivialAbsoluteValue_apply_ne_zero (k : Type*) [DecidableEq k] [Field k]
    (x : k) (hx : x ≠ 0) :
    trivialAbsoluteValue k x = 1 :=
  AbsoluteValue.trivial_apply hx

/-- The trivial absolute value is nonarchimedean. -/
theorem trivialAbsoluteValue_isNonarchimedean (k : Type*) [DecidableEq k] [Field k] :
    IsNonarchimedean (trivialAbsoluteValue k) := by
  intro x y
  change AbsoluteValue.trivial (x + y) ≤
    max (AbsoluteValue.trivial x) (AbsoluteValue.trivial y)
  by_cases hx : x = 0
  · simp [AbsoluteValue.trivial, hx]
  · by_cases hy : y = 0
    · simp [AbsoluteValue.trivial, hy]
    · by_cases hxy : x + y = 0 <;> simp [AbsoluteValue.trivial, hx, hy, hxy]
```

# Lemma 1.4
%%%
number := false
%%%

_Lemma 1.4._ An absolute value $`\lvert \cdot \rvert`$ on a field $`k`$ is nonarchimedean if and only if

$$`\lvert \underbrace{1 + \cdots + 1}_{n} \rvert \leq 1`$$

for all $`n \geq 1`$.

_Proof._ See Problem Set 1. $`\square`$

```lean
/-- Key bound via binomial theorem: f(x+y)^n ≤ (n+1) * max(f x, f y)^n. -/
private lemma absval_add_pow_le {k : Type*} [Field k]
    (f : AbsoluteValue k ℝ) (hnat : ∀ n : ℕ, f n ≤ 1)
    (x y : k) (n : ℕ) :
    f (x + y) ^ n ≤ (↑(n + 1) : ℝ) * max (f x) (f y) ^ n := by
  rw [← map_pow, Commute.add_pow (Commute.all x y)]
  calc f (∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i) * ↑(n.choose i))
      ≤ ∑ i ∈ Finset.range (n + 1),
          f (x ^ i * y ^ (n - i) * ↑(n.choose i)) := f.sum_le _ _
    _ = ∑ i ∈ Finset.range (n + 1),
          f x ^ i * f y ^ (n - i) * f ↑(n.choose i) := by
        congr 1; ext i; simp only [map_mul, map_pow]
    _ ≤ ∑ i ∈ Finset.range (n + 1), f x ^ i * f y ^ (n - i) := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_of_le_one_right
          (mul_nonneg (pow_nonneg (f.nonneg _) _) (pow_nonneg (f.nonneg _) _))
          (hnat _)
    _ ≤ ∑ _i ∈ Finset.range (n + 1), max (f x) (f y) ^ n := by
        apply Finset.sum_le_sum; intro i hi
        rw [Finset.mem_range] at hi
        calc f x ^ i * f y ^ (n - i)
            ≤ max (f x) (f y) ^ i * max (f x) (f y) ^ (n - i) := by
              gcongr
              · exact le_max_left _ _
              · exact le_max_right _ _
          _ = max (f x) (f y) ^ n := by
              rw [← pow_add]; congr 1; omega
    _ = (↑(n + 1) : ℝ) * max (f x) (f y) ^ n := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Lemma 1.4: An absolute value on a field is nonarchimedean if and only if
|n| ≤ 1 for all positive integers n. -/
theorem nonarchimedean_iff_natCast_le_one {k : Type*} [Field k]
    (f : AbsoluteValue k ℝ) :
    IsNonarchimedean f ↔ ∀ n : ℕ, f n ≤ 1 := by
  constructor
  · intro hna _
    exact IsNonarchimedean.apply_natCast_le_one_of_isNonarchimedean hna
  · intro hnat x y
    change f (x + y) ≤ max (f x) (f y)
    set M := max (f x) (f y) with hM_def
    have hM : 0 ≤ M := le_max_of_le_left (f.nonneg x)
    refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
    have ha0 : 0 < a := lt_of_le_of_lt hM ha
    rcases eq_or_lt_of_le hM with hM0 | hM0
    · have hfx : f x = 0 := le_antisymm (hM0.symm ▸ le_max_left _ _) (f.nonneg _)
      have hfy : f y = 0 := le_antisymm (hM0.symm ▸ le_max_right _ _) (f.nonneg _)
      rw [map_eq_zero] at hfx hfy
      simp [hfx, hfy, ha0.le]
    · have ham : 1 < a / M := by rwa [one_lt_div hM0]
      obtain ⟨n, hn⟩ := Real.exists_natCast_add_one_lt_pow_of_one_lt ham
      have hMn : 0 < M ^ n := pow_pos hM0 n
      rw [div_pow, lt_div_iff₀ hMn] at hn
      have key := absval_add_pow_le f hnat x y n
      push_cast at key
      rw [← hM_def] at key
      have hn0 : n ≠ 0 := by rintro rfl; simp at hn
      exact le_of_pow_le_pow_left₀ hn0 ha0.le (key.trans hn.le)
```

# Corollary 1.5
%%%
number := false
%%%

_Corollary 1.5._ In a field of positive characteristic every absolute value is nonarchimedean, and the only absolute value on a finite field is the trivial one.

```lean
/-- Corollary 1.5 (part 1): In positive characteristic, every absolute
value is nonarchimedean. -/
theorem posChar_isNonarchimedean {k : Type*} [Field k] {p : ℕ} [CharP k p]
    (hp : p ≠ 0) (f : AbsoluteValue k ℝ) :
    IsNonarchimedean f := by
  rw [nonarchimedean_iff_natCast_le_one]
  intro n
  have hprime := CharP.char_prime_of_ne_zero k hp
  haveI : Fact (Nat.Prime p) := ⟨hprime⟩
  have hfrob : (n : k) ^ p = (n : k) := by
    have := map_natCast (frobenius k p) n
    rwa [frobenius_def] at this
  have h1 : f n ^ p = f n := by rw [← map_pow, hfrob]
  rcases eq_or_lt_of_le (f.nonneg (n : k)) with hfn | hfn
  · linarith
  · have h2 : f n ^ (p - 1) = 1 := by
      have h3 : f n ^ (p - 1) * f n = 1 * f n := by
        rw [← pow_succ, Nat.sub_one_add_one_eq_of_pos hprime.pos, h1, one_mul]
      exact mul_right_cancel₀ (ne_of_gt hfn) h3
    have hp2 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hprime.one_lt
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (f.nonneg _) hp2).mp h2)

/-- Corollary 1.5 (part 2): The only absolute value on a finite field
is the trivial one. -/
theorem finite_field_absval_trivial {k : Type*} [Field k] [Finite k]
    (f : AbsoluteValue k ℝ) (x : k) (hx : x ≠ 0) :
    f x = 1 := by
  haveI : Finite kˣ := Finite.of_injective Units.val Units.val_injective
  set u : kˣ := Units.mk0 x hx
  have hfin : IsOfFinOrder u := isOfFinOrder_of_finite u
  have hord : 0 < orderOf u := hfin.orderOf_pos
  have hpow : u ^ orderOf u = 1 := pow_orderOf_eq_one u
  have hxpow : x ^ orderOf u = 1 := by
    have h : (u : k) ^ orderOf u = (1 : kˣ) := by exact_mod_cast hpow
    simpa using h
  have h1 : f x ^ orderOf u = 1 := by rw [← map_pow, hxpow, map_one]
  exact (pow_eq_one_iff_of_nonneg (f.nonneg _) hord.ne').mp h1
```

# Definition 1.6
%%%
number := false
%%%

_Definition 1.6._ Two absolute values $`\lvert \cdot \rvert`$ and $`\lvert \cdot \rvert'`$ on the same field $`k`$ are _equivalent_ if there exists an $`\alpha \in \mathbb{R}_{>0}`$ for which $`\lvert x \rvert' = \lvert x \rvert^{\alpha}`$ for all $`x \in k`$.

```lean
/-- Definition 1.6: Two absolute values on k are equivalent if one is a
positive real power of the other. -/
def AbsoluteValue.AreEquivalent {k : Type*} [Field k]
    (f g : AbsoluteValue k ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ x : k, g x = (f x) ^ α
```
