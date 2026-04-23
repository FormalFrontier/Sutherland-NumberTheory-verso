import VersoManual
import Mathlib.Tactic.Recall
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Localization.Rat
import Mathlib.RingTheory.Polynomial.RationalRoot

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.code.warnLineLength 90

#doc (Manual) "Integral Closure" =>
%%%
tag := "integral-closure"
file := some "integral-closure"
number := false
%%%

# Definition 1.17
%%%
number := false
%%%

_Definition 1.17._ Given a ring extension $`A \subseteq B`, an element $`b \in B` is _integral over $`A`_ if is a root of a monic polynomial in $`A[x]`. The ring $`B` is _integral over $`A`_ if all its elements are.

```lean
/-- Definition 1.17: An element x : A is integral
over R if it is a root of some monic polynomial
p : R[X]. -/
recall IsIntegral (R : Type*) {A : Type*}
    [CommRing R] [Ring A] [Algebra R A]
    (x : A) : Prop

/-- Definition 1.17: An algebra A over R is an
integral extension if every element of A is integral
over R. -/
recall Algebra.IsIntegral (R A : Type*)
    [CommRing R] [Ring A] [Algebra R A] : Prop
```

# Proposition 1.18
%%%
number := false
%%%

_Proposition 1.18._ _Let $`\alpha, \beta \in B` be integral over $`A \subseteq B`. Then $`\alpha + \beta` and $`\alpha\beta` are integral over $`A`._

_Proof._ Let $`f \in A[x]` and $`g \in A[y]` be such that $`f(\alpha) = g(\beta) = 0`, where

$$`f(x) = a_0 + a_1 x + \cdots + a_{m-1} x^{m-1} + x^m,`

$$`g(y) = b_0 + b_1 y + \cdots + b_{n-1} y^{n-1} + y^n.`

It suffices to consider the case

$$`A = \mathbb{Z}[a_0, \ldots, a_{m-1}, b_0, \ldots, b_{n-1}], \qquad \text{and} \qquad B = \frac{A[x, y]}{\bigl(f(x), g(y)\bigr)},`

with $`\alpha` and $`\beta` equal to the images of $`x` and $`y` in $`B`, respectively, since given any $`A' \subseteq B'` we have homomorphisms $`A \to A'` defined by $`a_i \mapsto a_i` and $`b_i \mapsto b_i` and $`B \to B'` defined by $`x \mapsto \alpha` and $`y \mapsto \beta`, and if $`x + y, xy \in B` are integral over $`A` then $`\alpha + \beta, \alpha\beta \in B'` must be integral over $`A'`.

Let $`k` be the algebraic closure of the fraction field of $`A`, and let $`\alpha_1, \ldots, \alpha_m` be the roots of $`f` in $`k` and let $`\beta_1, \ldots, \beta_n` be the roots of $`g` in $`k`. The polynomial

$$`h(z) = \prod_{i,j} \bigl(z - (\alpha_i + \beta_j)\bigr)`

has coefficients that may be expressed as polynomials in the symmetric functions of the $`\alpha_i` and $`\beta_j`, equivalently, the coefficients $`a_i` and $`b_j` of $`f` and $`g`, respectively. Thus $`h \in A[z]`, and $`h(x+y) = 0`, so $`x+y` is integral over $`A`. Applying the same argument to $`h(z) = \prod_{i,j}(z - \alpha_i \beta_j)` shows that $`xy` is also integral over $`A`. $`\square`

```lean
set_option autoImplicit true in
/-- Proposition 1.18 (sum): The sum of integral
elements is integral. -/
recall IsIntegral.add [CommRing R] [CommRing A]
    [Algebra R A] {x y : A}
    (hx : IsIntegral R x)
    (hy : IsIntegral R y) : IsIntegral R (x + y)

set_option autoImplicit true in
/-- Proposition 1.18 (product): The product of
integral elements is integral. -/
recall IsIntegral.mul [CommRing R] [CommRing A]
    [Algebra R A] {x y : A}
    (hx : IsIntegral R x)
    (hy : IsIntegral R y) : IsIntegral R (x * y)
```

# Definition 1.19
%%%
number := false
%%%

_Definition 1.19._ Given a ring extension $`B/A`, the ring $`\tilde{A} = \{b \in B : b \text{ is integral over } A\}` is the _integral closure_ of $`A` in $`B`. When $`\tilde{A} = A` we say that $`A` is _integrally closed in $`B`_. For a domain $`A`, its _integral closure_ (or _normalization_) is its integral closure in its fraction field, and $`A` is _integrally closed_ (or _normal_) if it is integrally closed in its fraction field.

```lean
/-- Definition 1.19: The integral closure of R in A
is the subalgebra of elements satisfying a monic
polynomial over R. -/
recall integralClosure (R A : Type*)
    [CommRing R] [CommRing A] [Algebra R A] :
    Subalgebra R A

/-- Definition 1.19: A domain is integrally closed
if every element of its fraction field that is
integral over it already belongs to it. -/
recall IsIntegrallyClosed (R : Type*)
    [CommRing R] : Prop
```

# Proposition 1.20
%%%
number := false
%%%

_Proposition 1.20._ _If $`C/B/A` is a tower of ring extensions in which $`B` is integral over $`A` and $`C` is integral over $`B` then $`C` is integral over $`A`._

_Proof._ See \[1, Thm. 10.27\] or \[2, Cor. 5.4\]. $`\square`

```lean
/-- Proposition 1.20: Integrality is transitive. -/
example {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B]
    [Algebra.IsIntegral R A]
    [Algebra.IsIntegral A B] :
    Algebra.IsIntegral R B :=
  Algebra.IsIntegral.trans A
```

# Corollary 1.21
%%%
number := false
%%%

_Corollary 1.21._ _If $`B/A` is a ring extension, then the integral closure of $`A` in $`B` is integrally closed in $`B`._

```lean
/-- Corollary 1.21: The integral closure of A in B
is integrally closed in B. -/
example (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] :
    IsIntegrallyClosedIn (integralClosure A B) B :=
  inferInstance
```

# Proposition 1.22
%%%
number := false
%%%

_Proposition 1.22._ _The ring $`\mathbb{Z}` is integrally closed._

_Proof._ We apply the rational root test: suppose $`r/s \in \mathbb{Q}` is integral over $`\mathbb{Z}`, where $`r` and $`s` are coprime integers. Then

$$`\left(\frac{r}{s}\right)^n + a_{n-1} \left(\frac{r}{s}\right)^{n-1} + \cdots a_1 \left(\frac{r}{s}\right) + a_0 = 0`

for some $`a_0, \ldots, a_{n-1} \in \mathbb{Z}`. Clearing denominators yields

$$`r^n + a_{n-1} s r^{n-1} + \cdots a_1 s^{n-1} r + a_0 s^n = 0,`

thus $`r^n = -s(a_{n-1} r^{n-1} + \cdots a_1 s^{n-2} r + a_0 s^{n-1})` is a multiple of $`s`. But $`r` and $`s` are coprime, so $`s = \pm 1` and therefore $`r/s \in \mathbb{Z}`. $`\square`

```lean
/-- Proposition 1.22: ℤ is integrally closed. -/
example : IsIntegrallyClosed ℤ := inferInstance

/-! The book's proof is the rational root test. We
record the argument as a chain of Lean statements:
a rational integral over `ℤ` is in the localization
image, its denominator is therefore `1`, and so it
equals its numerator cast into `ℚ`. -/

/-- Rational-root step (i): a rational number integral
over `ℤ` is an integer in the sense of
`IsLocalization.IsInteger`. -/
theorem sutherland_rat_isInteger_of_isIntegral
    (q : ℚ) (hq : IsIntegral ℤ q) :
    IsLocalization.IsInteger ℤ q := by
  rcases hq with ⟨p, hp, hroot⟩
  exact isInteger_of_is_root_of_monic hp hroot

/-- Rational-root step (ii): the denominator of a
rational integral over `ℤ` is `1`. Since `q.num`
and `q.den` are coprime in Mathlib's reduced form,
this is the "s = ±1" conclusion of the book's
proof. -/
theorem sutherland_rat_den_eq_one_of_isIntegral
    (q : ℚ) (hq : IsIntegral ℤ q) : q.den = 1 := by
  rcases (Rat.isLocalizationIsInteger_iff q).mp
      (sutherland_rat_isInteger_of_isIntegral q hq)
    with ⟨z, rfl⟩
  simp

/-- Rational-root step (iii): a rational integral over
`ℤ` equals its own numerator as a rational. -/
theorem sutherland_rat_num_eq_of_isIntegral
    (q : ℚ) (hq : IsIntegral ℤ q) :
    (q.num : ℚ) = q := by
  simpa using (Rat.den_eq_one_iff q).mp
    (sutherland_rat_den_eq_one_of_isIntegral q hq)

/-- Rational-root conclusion: a rational integral over
`ℤ` is an integer. This is the full content of
Proposition 1.22. -/
theorem sutherland_rat_exists_int_of_isIntegral
    (q : ℚ) (hq : IsIntegral ℤ q) :
    ∃ z : ℤ, (z : ℚ) = q :=
  ⟨q.num, sutherland_rat_num_eq_of_isIntegral q hq⟩
```

# Corollary 1.23
%%%
number := false
%%%

_Corollary 1.23._ _Every unique factorization domain is integrally closed. In particular, every PID is integrally closed._

_Proof._ The proof of Proposition 1.22 works for any UFD. $`\square`

```lean
/-- Corollary 1.23: Every UFD is integrally
closed. -/
example {A : Type*} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] :
    IsIntegrallyClosed A := inferInstance

/-- Corollary 1.23: In particular, every PID is
integrally closed. -/
example {A : Type*} [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] :
    IsIntegrallyClosed A := inferInstance
```

# Integrally closed domains
%%%
number := false
%%%

The corollary implies that every discrete valuation ring is integrally closed. In fact, more is true.

# Example 1.24
%%%
number := false
%%%

_Example 1.24._ The ring $`\mathbb{Z}[\sqrt{5}]` is not a UFD (nor a PID) because it is not integrally closed: consider $`\phi = (1 + \sqrt{5})/2 \in \operatorname{Frac} \mathbb{Z}[\sqrt{5}]`, which is integral over $`\mathbb{Z}` (and hence over $`\mathbb{Z}[\sqrt{5}]`), since $`\phi^2 - \phi - 1 = 0`. But $`\phi \notin \mathbb{Z}[\sqrt{5}]`, so $`\mathbb{Z}[\sqrt{5}]` is not integrally closed.

```lean
/-- φ = (1 + √5)/2 satisfies φ² - φ - 1 = 0,
so it is integral over ℤ (Example 1.24). -/
theorem goldenRatio_isIntegral :
    IsIntegral ℤ ((1 + Real.sqrt 5) / 2 : ℝ) := by
  open Polynomial in
  refine ⟨X ^ 2 - X - 1, ?_, ?_⟩
  · have h1 : (X ^ 2 - X - 1 : ℤ[X]).natDegree = 2
      := by compute_degree!
    unfold Monic leadingCoeff
    rw [h1]
    simp [coeff_X, coeff_one]
  · simp [eval₂_sub, eval₂_pow,
      eval₂_X, eval₂_one]
    nlinarith [Real.sq_sqrt
      (show (5 : ℝ) ≥ 0 by norm_num)]

/-- ℤ[√5] is not integrally closed (Example 1.24).
-/
theorem zsqrtd5_not_integrallyClosed :
    ¬IsIntegrallyClosed (Zsqrtd 5) := by
  haveI h5ns : Zsqrtd.Nonsquare (5 : ℕ) :=
    ⟨fun n h => by
      have hn : n ≤ 2 := by nlinarith
      interval_cases n <;> omega⟩
  haveI : IsDomain (ℤ√(5 : ℕ)) := inferInstance
  intro hic
  have h2nd :
      (2 : Zsqrtd 5) ∈ nonZeroDivisors (Zsqrtd 5)
      := mem_nonZeroDivisors_of_ne_zero (by decide)
  have h2' :
      algebraMap (Zsqrtd 5)
        (FractionRing (Zsqrtd 5)) 2 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors h2nd
  let φ : FractionRing (Zsqrtd 5) :=
    algebraMap (Zsqrtd 5) _
      (⟨1, 1⟩ : Zsqrtd 5) /
    algebraMap _ _ (2 : Zsqrtd 5)
  -- φ is integral over Zsqrtd 5
  have hφ : IsIntegral (Zsqrtd 5) φ := by
    open Polynomial in
    refine ⟨X ^ 2 - X - 1, ?_, ?_⟩
    · have h1 :
          (X ^ 2 - X - 1 : (Zsqrtd 5)[X]).natDegree
            = 2 := by compute_degree!
      unfold Monic leadingCoeff
      rw [h1]; simp [coeff_X, coeff_one]
    · have hkey :
          algebraMap (Zsqrtd 5)
            (FractionRing (Zsqrtd 5))
            (⟨1,1⟩ : Zsqrtd 5) ^ 2 -
          algebraMap (Zsqrtd 5)
            (FractionRing (Zsqrtd 5))
            (⟨1,1⟩ : Zsqrtd 5) *
          algebraMap (Zsqrtd 5)
            (FractionRing (Zsqrtd 5)) 2 -
          algebraMap (Zsqrtd 5)
            (FractionRing (Zsqrtd 5)) 2 ^ 2
            = 0 := by
        have h : (⟨1, 1⟩ : Zsqrtd 5) ^ 2 -
            ⟨1, 1⟩ * 2 - 2 ^ 2 = 0 := by decide
        simpa [map_sub, map_pow, map_mul] using
          congr_arg (algebraMap (Zsqrtd 5)
            (FractionRing (Zsqrtd 5))) h
      simp only [eval₂_sub, eval₂_pow,
        eval₂_X, eval₂_one, φ]
      field_simp [h2']
      linear_combination hkey
  rw [isIntegrallyClosed_iff
    (FractionRing (Zsqrtd 5))] at hic
  obtain ⟨a, ha⟩ := hic hφ
  have h2a : 2 * a = ⟨1, 1⟩ := by
    apply IsFractionRing.injective (Zsqrtd 5)
      (FractionRing (Zsqrtd 5))
    rw [map_mul, ha]
    simp only [φ]
    exact mul_div_cancel₀ _ h2'
  have hre := congr_arg Zsqrtd.re h2a
  simp only [Zsqrtd.re_mul,
    show (2 : Zsqrtd 5).re = (2 : ℤ) from rfl,
    show (2 : Zsqrtd 5).im = (0 : ℤ) from rfl,
    mul_zero, zero_mul, add_zero] at hre
  omega

/-- Since every unique factorization domain is
integrally closed (Corollary 1.23), `ℤ[√5]` is not a
UFD. -/
theorem sutherland_zsqrtd5_not_uniqueFactorizationMonoid :
    ¬UniqueFactorizationMonoid (Zsqrtd 5) := by
  intro _
  haveI h5ns : Zsqrtd.Nonsquare (5 : ℕ) :=
    ⟨fun n h => by
      have hn : n ≤ 2 := by nlinarith
      interval_cases n <;> omega⟩
  haveI : IsDomain (ℤ√(5 : ℕ)) := inferInstance
  exact zsqrtd5_not_integrallyClosed inferInstance

/-- Since every principal ideal ring is integrally
closed (Corollary 1.23), `ℤ[√5]` is not a PID. -/
theorem sutherland_zsqrtd5_not_isPrincipalIdealRing :
    ¬IsPrincipalIdealRing (Zsqrtd 5) := by
  intro _
  haveI h5ns : Zsqrtd.Nonsquare (5 : ℕ) :=
    ⟨fun n h => by
      have hn : n ≤ 2 := by nlinarith
      interval_cases n <;> omega⟩
  haveI : IsDomain (ℤ√(5 : ℕ)) := inferInstance
  exact zsqrtd5_not_integrallyClosed inferInstance
```

# Proposition 1.25
%%%
number := false
%%%

_Proposition 1.25._ _Every valuation ring is integrally closed._

_Proof._ Let $`A` be a valuation ring with fraction field $`k` and let $`\alpha \in k` be integral over $`A`. Then

$$`\alpha^n + a_{n-1} \alpha^{n-1} + a_{n-2} \alpha^{n-2} + \cdots + a_1 \alpha + a_0 = 0`

for some $`a_0, a_1, \ldots, a_{n-1} \in A`. Suppose $`\alpha \notin A`. Then $`\alpha^{-1} \in A`, since $`A` is a valuation ring. Multiplying the equation above by $`\alpha^{-(n-1)} \in A` and moving all but the first term on the LHS to the RHS yields

$$`\alpha = -a_{n-1} - a_{n-1} \alpha^{-1} - \cdots - a_1 \alpha^{2-n} - a_0 \alpha^{1-n} \in A,`

contradicting our assumption that $`\alpha \notin A`. It follows that $`A` is integrally closed. $`\square`

```lean
/-- Proposition 1.25: Every valuation ring is
integrally closed. -/
theorem sutherland_prop1_25 (A : Type*)
    [CommRing A] [IsDomain A] [ValuationRing A] :
    IsIntegrallyClosed A := by
  haveI : GCDMonoid A :=
    Classical.choice inferInstance
  exact GCDMonoid.toIsIntegrallyClosed
```
