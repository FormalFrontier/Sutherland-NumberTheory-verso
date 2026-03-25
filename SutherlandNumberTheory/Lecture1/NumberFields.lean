import VersoManual
import Mathlib.Tactic.Recall
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.code.warnLineLength 90

#doc (Manual) "Number Fields and Rings of Integers" =>
%%%
tag := "number-fields"
number := false
%%%

# Definition 1.26
%%%
number := false
%%%

_Definition 1.26._ A _number field_ $`K` is a finite extension of $`\mathbb{Q}`. The _ring of integers_ $`\mathcal{O}_K` is the integral closure of $`\mathbb{Z}` in $`K`.

```lean
/-- Definition 1.26: A number field is a field that
is a finite extension of ℚ. -/
recall NumberField (K : Type*) [Field K] : Prop

/-- Definition 1.26: The ring of integers 𝓞 K is
the integral closure of ℤ in K. -/
recall NumberField.RingOfIntegers (K : Type*)
    [Field K] : Type _
```

# Remark 1.27
%%%
number := false
%%%

_Remark 1.27._ The notation $`\mathbb{Z}_K` is also sometimes used to denote the ring of integers of $`K`. The symbol $`\mathcal{O}` emphasizes the fact that $`\mathcal{O}_K` is an _order_ in $`K`; in any $`\mathbb{Q}`-algebra $`K` of finite dimension $`r`, an order is a subring of $`K` that is also a free $`\mathbb{Z}`-module of rank $`r`, equivalently, a $`\mathbb{Z}`-lattice in $`K` that is also a ring. In fact, $`\mathcal{O}_K` is the _maximal order_ of $`K`: it contains every order in $`K`.

```lean
/-- Remark 1.27: 𝓞 K is a free ℤ-module. -/
example {K : Type*} [Field K] [NumberField K] :
    Module.Free ℤ
      (NumberField.RingOfIntegers K) :=
  inferInstance

/-- Remark 1.27: The ℤ-rank of 𝓞 K equals
[K : ℚ]. -/
recall NumberField.RingOfIntegers.rank
    (K : Type*) [Field K] [NumberField K] :
    Module.finrank ℤ
      (NumberField.RingOfIntegers K) =
    Module.finrank ℚ K
```

# Proposition 1.28
%%%
number := false
%%%

_Proposition 1.28._ _Let $`A` be an integrally closed domain with fraction field $`K`. Let $`\alpha` be an element of a finite extension $`L/K`, and let $`f \in K[x]` be its minimal polynomial over $`K`. Then $`\alpha` is integral over $`A` if and only if $`f \in A[x]`._

_Proof._ The reverse implication is immediate: if $`f \in A[x]` then certainly $`\alpha` is integral over $`A`. For the forward implication, suppose $`\alpha` is integral over $`A` and let $`g \in A[x]` be a monic polynomial for which $`g(\alpha) = 0`. In $`\overline{K}[x]` we may factor $`f(x)` as

$$`f(x) = \prod_i (x - \alpha_i).`

For each $`\alpha_i` we have a field embedding $`K(\alpha) \to \overline{K}` that sends $`\alpha` to $`\alpha_i` and fixes $`K`. As elements of $`\overline{K}` we have $`g(\alpha_i) = 0` (since $`f(\alpha_i) = 0` and $`f` must divide $`g`), so each $`\alpha_i \in \overline{K}` is integral over $`A` and lies in the integral closure $`\tilde{A}` of $`A` in $`\overline{K}`. Each coefficient of $`f \in K[x]` can be expressed as a sum of products of the $`\alpha_i`, and is therefore an element of the ring $`\tilde{A}` that also lies in $`K`. But $`A = \tilde{A} \cap K`, since $`A` is integrally closed in its fraction field $`K`. $`\square`

```lean
/-- Proposition 1.28: For an integrally closed
domain A with fraction field K, an element α of a
finite extension L/K is integral over A iff its
minimal polynomial over K has coefficients in A. -/
theorem sutherland_prop1_28
    {A K L : Type*}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] (α : L) :
    IsIntegral A α ↔
      (minpoly A α).map (algebraMap A K) =
        minpoly K α := by
  constructor
  · intro h
    exact (minpoly.isIntegrallyClosed_eq_field_fractions'
      (R := A) (K := K) h).symm
  · intro h
    by_contra hnotint
    rw [minpoly.eq_zero hnotint,
      Polynomial.map_zero] at h
    haveI : Algebra.IsIntegral K L :=
      Algebra.IsIntegral.of_finite K L
    have hK : IsIntegral K α :=
      Algebra.IsIntegral.isIntegral α
    exact (minpoly.monic hK).ne_zero h.symm
```

# Example 1.29
%%%
number := false
%%%

_Example 1.29._ We saw in Example 1.24 that $`(1 + \sqrt{5})/2` is integral over $`\mathbb{Z}`. Now consider $`\alpha = (1 + \sqrt{7})/2`. Its minimal polynomial $`x^2 - x - 3/2 \notin \mathbb{Z}[x]`, so $`\alpha` is not integral over $`\mathbb{Z}`.

```lean
/-- (1 + √7)/2 is not integral over ℤ (Example
1.29): its minimal polynomial over ℚ is
x² - x - 3/2 ∉ ℤ[x]. -/
theorem halfOnePlusSqrt7_not_integral :
    ¬IsIntegral ℤ
      ((1 + Real.sqrt 7) / 2 : ℝ) := by
  intro h
  -- (1 - √7)/2 is also integral over ℤ
  have hconj :
      IsIntegral ℤ
        ((1 - Real.sqrt 7) / 2 : ℝ) := by
    have heq : (1 - Real.sqrt 7) / 2 =
        1 - (1 + Real.sqrt 7) / 2 := by ring
    rw [heq]; exact isIntegral_one.sub h
  -- α * (1-α) = (1 - 7)/4 = -3/2
  have hval :
      ((1 + Real.sqrt 7) / 2) *
      ((1 - Real.sqrt 7) / 2 : ℝ) =
        (-3 : ℝ) / 2 := by
    have h7 : Real.sqrt 7 ^ 2 = 7 :=
      Real.sq_sqrt (by norm_num)
    have : ((1 + Real.sqrt 7) / 2) *
        ((1 - Real.sqrt 7) / 2) =
        (1 - Real.sqrt 7 ^ 2) / 4 := by ring
    rw [this, h7]; norm_num
  -- So -3/2 : ℝ is integral over ℤ
  have hR : IsIntegral ℤ ((-3 : ℝ) / 2) :=
    hval ▸ h.mul hconj
  -- The map ℚ → ℝ is injective
  have hinj :
      Function.Injective (algebraMap ℚ ℝ) := by
    intro a b hab; exact_mod_cast hab
  -- So -3/2 : ℚ is integral over ℤ
  have hQ : IsIntegral ℤ ((-3 : ℚ) / 2) := by
    have hcast :
        algebraMap ℚ ℝ ((-3 : ℚ) / 2) =
          (-3 : ℝ) / 2 := by
      rw [show algebraMap ℚ ℝ ((-3 : ℚ) / 2) =
        (((-3 : ℚ) / 2 : ℚ) : ℝ) from rfl]
      push_cast; ring
    exact (isIntegral_algebraMap_iff hinj).mp
      (hcast ▸ hR)
  -- ℤ is integrally closed in ℚ, so -3/2 ∈ ℤ
  haveI : IsIntegrallyClosed ℤ :=
    GCDMonoid.toIsIntegrallyClosed
  rw [IsIntegrallyClosed.isIntegral_iff] at hQ
  obtain ⟨a, ha⟩ := hQ
  have ha' : (a : ℚ) = -3 / 2 := ha
  have h2 : (a : ℤ) * 2 = -3 :=
    by exact_mod_cast
      (show (a : ℚ) * 2 = -3 by linarith)
  omega
```
