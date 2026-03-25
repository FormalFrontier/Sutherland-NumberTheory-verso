import VersoManual
import Mathlib.Tactic.Recall
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
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

_Definition 1.2._ An _absolute value_ on a field $`k` is a map $`\lvert \cdot \rvert \colon k \to \mathbb{R}_{\geq 0}` such that for all $`x, y \in k` the following hold:

1. $`\lvert x \rvert = 0` if and only if $`x = 0`;
2. $`\lvert xy \rvert = \lvert x \rvert \lvert y \rvert`;
3. $`\lvert x + y \rvert \leq \lvert x \rvert + \lvert y \rvert`.

If the stronger condition

4. $`\lvert x + y \rvert \leq \max(\lvert x \rvert, \lvert y \rvert)`

also holds, then the absolute value is _nonarchimedean_; otherwise it is _archimedean_.

```lean
/-- Definition 1.2 (absolute value). -/
recall AbsoluteValue (R : Type*) (S : Type*)
    [Semiring R] [Semiring S] [PartialOrder S] :
    Type _

section
variable {R : Type*} [Semiring R]
  [LinearOrder R] [IsStrictOrderedRing R]

/-- Definition 1.2 (nonarchimedean). -/
recall IsNonarchimedean {α : Type*} [Add α]
    (f : α → R) : Prop :=
  ∀ a b : α, f (a + b) ≤ f a ⊔ f b
end
```

# Example 1.3
%%%
number := false
%%%

_Example 1.3._ The map $`\lvert \cdot \rvert \colon k \to \mathbb{R}_{\geq 0}` defined by

$$`\lvert x \rvert = \begin{cases} 1 & \text{if } x \neq 0, \\ 0 & \text{if } x = 0, \end{cases}`

is the _trivial absolute value_ on $`k`. It is nonarchimedean.

```lean
/-- Example 1.3: The trivial absolute value. -/
recall AbsoluteValue.trivial

/-- Example 1.3: |x| = 1 for x ≠ 0. -/
recall AbsoluteValue.trivial_apply

/-- Example 1.3: The trivial absolute value is
nonarchimedean. -/
theorem trivialAbsoluteValue_isNonarchimedean
    {k : Type*} [DecidableEq k] [Field k] :
    IsNonarchimedean
      (⇑(AbsoluteValue.trivial :
        AbsoluteValue k ℝ)) := by
  intro x y
  by_cases hx : x = 0
  · simp [AbsoluteValue.trivial, hx]
  · by_cases hy : y = 0
    · simp [AbsoluteValue.trivial, hy]
    · by_cases hxy : x + y = 0 <;>
        simp [AbsoluteValue.trivial, hx, hy, hxy]
```

# Lemma 1.4
%%%
number := false
%%%

_Lemma 1.4._ An absolute value $`\lvert \cdot \rvert` on a field $`k` is nonarchimedean if and only if

$$`\lvert \underbrace{1 + \cdots + 1}_{n} \rvert \leq 1`

for all $`n \geq 1`.

_Proof._ See Problem Set 1. $`\square`

```lean
/-- Lemma 1.4: An absolute value on a field is
nonarchimedean iff |n| ≤ 1 for all n : ℕ. -/
theorem sutherland_lemma1_4 {k : Type*} [Field k]
    (f : AbsoluteValue k ℝ) :
    IsNonarchimedean (⇑f) ↔ ∀ n : ℕ, f n ≤ 1 := by
  constructor
  · intro hna n
    exact IsNonarchimedean.apply_natCast_le_one_of_isNonarchimedean hna
  · intro hbnd
    letI : NormedField k := f.toNormedField
    haveI : IsUltrametricDist k :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hbnd
    exact IsUltrametricDist.isNonarchimedean_norm
```

# Corollary 1.5
%%%
number := false
%%%

_Corollary 1.5._ In a field of positive characteristic every absolute value is nonarchimedean, and the only absolute value on a finite field is the trivial one.

```lean
/-- Corollary 1.5 (part 1): In positive characteristic,
every absolute value is nonarchimedean. -/
theorem sutherland_corollary1_5_posChar
    {k : Type*} [Field k] {p : ℕ} [CharP k p]
    (hp : 0 < p) (f : AbsoluteValue k ℝ) :
    IsNonarchimedean (⇑f) := by
  have hp_ne : p ≠ 0 := Nat.pos_iff_ne_zero.mp hp
  have hp_prime : p.Prime :=
    CharP.char_prime_of_ne_zero k hp_ne
  haveI : Fact p.Prime := ⟨hp_prime⟩
  rw [sutherland_lemma1_4 f]
  intro n
  have hfn_pow : f n ^ p = f n := by
    rw [← f.map_pow]
    congr 1
    induction n with
    | zero => simp [hp_ne]
    | succ m ih =>
      push_cast
      rw [add_pow_char, ih, one_pow]
  by_contra h_gt
  push_neg at h_gt
  have := pow_lt_pow_right₀ h_gt hp_prime.one_lt
  rw [pow_one, hfn_pow] at this
  exact lt_irrefl _ this

/-- Corollary 1.5 (part 2): The only absolute value on
a finite field is the trivial one. -/
theorem sutherland_corollary1_5_finite
    {k : Type*} [Field k] [Finite k] [DecidableEq k]
    (f : AbsoluteValue k ℝ) :
    f = AbsoluteValue.trivial := by
  haveI : Fintype k := Fintype.ofFinite k
  ext x
  by_cases hx : x = 0
  · simp [hx, f.map_zero]
  · rw [AbsoluteValue.trivial_apply hx]
    have hq : x ^ (Fintype.card k - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one x hx
    have hfx_pow : f x ^ (Fintype.card k - 1) = 1 :=
      by rw [← f.map_pow, hq, f.map_one]
    have hn : Fintype.card k - 1 ≠ 0 := by
      have : 1 < Fintype.card k :=
        Fintype.one_lt_card
      omega
    exact (pow_eq_one_iff_of_nonneg
      (f.nonneg x) hn).mp hfx_pow
```

# Definition 1.6
%%%
number := false
%%%

_Definition 1.6._ Two absolute values $`\lvert \cdot \rvert` and $`\lvert \cdot \rvert'` on the same field $`k` are _equivalent_ if there exists an $`\alpha \in \mathbb{R}_{>0}` for which $`\lvert x \rvert' = \lvert x \rvert^{\alpha}` for all $`x \in k`.

```lean
/-- Definition 1.6: Two absolute values on k are
equivalent if one is a positive real power of the
other. -/
def AbsoluteValue.AreEquivalent {k : Type*} [Field k]
    (f g : AbsoluteValue k ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ x : k, g x = (f x) ^ α
```
