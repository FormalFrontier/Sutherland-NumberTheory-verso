import VersoManual
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Data.Real.Sqrt

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Number Fields and Rings of Integers" =>
%%%
tag := "number-fields"
number := false
%%%

# Definition 1.26
%%%
number := false
%%%

A _number field_ $K$ is a finite extension of $\mathbb{Q}$. The _ring of integers_ $\mathcal{O}_K$ is the integral closure of $\mathbb{Z}$ in $K$.

```lean
/-- Definition 1.26: A number field is a finite extension of ℚ.
Mathlib's `NumberField` class captures this exactly. -/
example (K : Type*) [Field K] [NumberField K] : FiniteDimensional ℚ K :=
  NumberField.to_finiteDimensional

/-- Definition 1.26: The ring of integers 𝒪_K is the integral closure of ℤ in K.
Mathlib's `𝓞 K` denotes `NumberField.RingOfIntegers K`. -/
example (K : Type*) [Field K] [NumberField K] : Type _ :=
  NumberField.RingOfIntegers K
```

# Remark 1.27
%%%
number := false
%%%

The notation $\mathbb{Z}_K$ is also sometimes used to denote the ring of integers of $K$. The symbol $\mathcal{O}$ emphasizes the fact that $\mathcal{O}_K$ is an _order_ in $K$; in any $\mathbb{Q}$-algebra $K$ of finite dimension $r$, an order is a subring of $K$ that is also a free $\mathbb{Z}$-module of rank $r$, equivalently, a $\mathbb{Z}$-lattice in $K$ that is also a ring. In fact, $\mathcal{O}_K$ is the _maximal order_ of $K$: it contains every order in $K$.

# Proposition 1.28
%%%
number := false
%%%

_Let $A$ be an integrally closed domain with fraction field $K$. Let $\alpha$ be an element of a finite extension $L/K$, and let $f \in K[x]$ be its minimal polynomial over $K$. Then $\alpha$ is integral over $A$ if and only if $f \in A[x]$._

_Proof._ The reverse implication is immediate: if $f \in A[x]$ then certainly $\alpha$ is integral over $A$. For the forward implication, suppose $\alpha$ is integral over $A$ and let $g \in A[x]$ be a monic polynomial for which $g(\alpha) = 0$. In $\overline{K}[x]$ we may factor $f(x)$ as

$$f(x) = \prod_i (x - \alpha_i).$$

For each $\alpha_i$ we have a field embedding $K(\alpha) \to \overline{K}$ that sends $\alpha$ to $\alpha_i$ and fixes $K$. As elements of $\overline{K}$ we have $g(\alpha_i) = 0$ (since $f(\alpha_i) = 0$ and $f$ must divide $g$), so each $\alpha_i \in \overline{K}$ is integral over $A$ and lies in the integral closure $\tilde{A}$ of $A$ in $\overline{K}$. Each coefficient of $f \in K[x]$ can be expressed as a sum of products of the $\alpha_i$, and is therefore an element of the ring $\tilde{A}$ that also lies in $K$. But $A = \tilde{A} \cap K$, since $A$ is integrally closed in its fraction field $K$. $\square$

```lean
/-- Proposition 1.28: For an integrally closed domain A with fraction field K,
an element α of a finite extension L/K is integral over A if and only if its
minimal polynomial over K has coefficients in A.

The forward direction delegates to `minpoly.isIntegrallyClosed_eq_field_fractions'`:
the minimal polynomial over K equals the image of the minimal polynomial over A,
so all coefficients are in the range of `algebraMap A K`.

The reverse direction lifts the polynomial back to A[x] and verifies integrality. -/
theorem integral_iff_minpoly_over_base
    {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L]
    {α : L} (hα : IsIntegral K α) :
    IsIntegral A α ↔
      ∀ i, (minpoly K α).coeff i ∈ (algebraMap A K).range := by
  constructor
  · intro hAα i
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (K := K) hAα]
    simp [Polynomial.coeff_map]
  · intro hcoeff
    have hlifts : minpoly K α ∈ Polynomial.lifts (algebraMap A K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n => RingHom.mem_range.mp (hcoeff n)
    obtain ⟨p, hp_map, -, hp_monic⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic hlifts (minpoly.monic hα)
    refine ⟨p, hp_monic, ?_⟩
    have h1 : Polynomial.aeval (R := A) α p = Polynomial.aeval (R := K) α (minpoly K α) := by
      rw [← Polynomial.aeval_map_algebraMap K α p, hp_map]
    rw [minpoly.aeval] at h1
    exact_mod_cast h1
```

# Example 1.29
%%%
number := false
%%%

We saw in Example 1.24 that $(1 + \sqrt{5})/2$ is integral over $\mathbb{Z}$. Now consider $\alpha = (1 + \sqrt{7})/2$. Its minimal polynomial $x^2 - x - 3/2 \notin \mathbb{Z}[x]$, so $\alpha$ is not integral over $\mathbb{Z}$.

```lean
/-- The element α = (1 + √7)/2 satisfies α² - α - 3/2 = 0. Since the minimal
polynomial has non-integer coefficients, α is not integral over ℤ. -/
theorem half_one_plus_sqrt7_minimal_poly :
    let α : ℝ := (1 + Real.sqrt 7) / 2
    α ^ 2 - α - 3 / 2 = 0 := by
  simp only
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]

/-- Example 1.29: (1 + √7)/2 is not integral over ℤ. Its minimal polynomial
x² - x - 3/2 does not have integer coefficients. -/
theorem half_one_plus_sqrt7_not_integral :
    ¬ IsIntegral ℤ ((1 + Real.sqrt 7) / 2 : ℝ) := by
  intro h_int
  -- (1-√7)/2 = 1 - (1+√7)/2 is also integral
  have h_conj : IsIntegral ℤ ((1 - Real.sqrt 7) / 2 : ℝ) := by
    have : (1 - Real.sqrt 7) / 2 = 1 - (1 + Real.sqrt 7) / 2 := by ring
    rw [this]; exact isIntegral_one.sub h_int
  -- Their product equals -3/2
  have h_prod_int : IsIntegral ℤ ((-3 / 2 : ℚ) : ℝ) := by
    have h := h_int.mul h_conj
    have h_prod_eq : ((1 + Real.sqrt 7) / 2) * ((1 - Real.sqrt 7) / 2 : ℝ) =
        ((-3 / 2 : ℚ) : ℝ) := by
      push_cast
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    rwa [h_prod_eq] at h
  -- Transfer: IsIntegral ℤ ((-3/2 : ℚ) : ℝ) → IsIntegral ℤ (-3/2 : ℚ)
  have h_rat : IsIntegral ℤ (-3 / 2 : ℚ) := by
    obtain ⟨p, hp_monic, hp_eval⟩ := h_prod_int
    exact ⟨p, hp_monic, by
      apply (algebraMap ℚ ℝ).injective
      rw [map_zero, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq ℤ ℚ ℝ]
      exact hp_eval⟩
  -- By ℤ integrally closed: -3/2 must be an integer
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h_rat
  -- But -3/2 is not an integer
  have h_eq : (n : ℚ) = -3 / 2 := by simpa using hn
  have h_two_n : (2 : ℚ) * n = -3 := by linarith
  exact absurd (by exact_mod_cast h_two_n : (2 : ℤ) * n = -3) (by omega)
```
