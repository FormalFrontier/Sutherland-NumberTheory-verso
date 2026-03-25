import VersoManual
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.code.warnLineLength 90

#doc (Manual) "Integral Closure" =>
%%%
tag := "integral-closure"
number := false
%%%

# Definition 1.17
%%%
number := false
%%%

_Definition 1.17._ Given a ring extension $`A \subseteq B`$, an element $`b \in B`$ is _integral over $`A`$_ if is a root of a monic polynomial in $`A[x]`$. The ring $`B`$ is _integral over $`A`$_ if all its elements are.

```lean
/-- Definition 1.17 (element-level): An element b ∈ B is integral over A if it is
a root of a monic polynomial in A[x]. This is `IsIntegral A b` in Mathlib. -/
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (b : B) :
    Prop := IsIntegral A b

/-- Definition 1.17 (ring-level): B is integral over A if every element of B is
integral over A. This is `Algebra.IsIntegral A B` in Mathlib. -/
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] :
    Prop := Algebra.IsIntegral A B
```

# Proposition 1.18
%%%
number := false
%%%

_Proposition 1.18._ _Let $`\alpha, \beta \in B`$ be integral over $`A \subseteq B`$. Then $`\alpha + \beta`$ and $`\alpha\beta`$ are integral over $`A`$._

_Proof._ Let $`f \in A[x]`$ and $`g \in A[y]`$ be such that $`f(\alpha) = g(\beta) = 0`$, where

$$`f(x) = a_0 + a_1 x + \cdots + a_{m-1} x^{m-1} + x^m,`$$

$$`g(y) = b_0 + b_1 y + \cdots + b_{n-1} y^{n-1} + y^n.`$$

It suffices to consider the case

$$`A = \mathbb{Z}[a_0, \ldots, a_{m-1}, b_0, \ldots, b_{n-1}], \qquad \text{and} \qquad B = \frac{A[x, y]}{\bigl(f(x), g(y)\bigr)},`$$

with $`\alpha`$ and $`\beta`$ equal to the images of $`x`$ and $`y`$ in $`B`$, respectively, since given any $`A' \subseteq B'`$ we have homomorphisms $`A \to A'`$ defined by $`a_i \mapsto a_i`$ and $`b_i \mapsto b_i`$ and $`B \to B'`$ defined by $`x \mapsto \alpha`$ and $`y \mapsto \beta`$, and if $`x + y, xy \in B`$ are integral over $`A`$ then $`\alpha + \beta, \alpha\beta \in B'`$ must be integral over $`A'`$.

Let $`k`$ be the algebraic closure of the fraction field of $`A`$, and let $`\alpha_1, \ldots, \alpha_m`$ be the roots of $`f`$ in $`k`$ and let $`\beta_1, \ldots, \beta_n`$ be the roots of $`g`$ in $`k`$. The polynomial

$$`h(z) = \prod_{i,j} \bigl(z - (\alpha_i + \beta_j)\bigr)`$$

has coefficients that may be expressed as polynomials in the symmetric functions of the $`\alpha_i`$ and $`\beta_j`$, equivalently, the coefficients $`a_i`$ and $`b_j`$ of $`f`$ and $`g`$, respectively. Thus $`h \in A[z]`$, and $`h(x+y) = 0`$, so $`x+y`$ is integral over $`A`$. Applying the same argument to $`h(z) = \prod_{i,j}(z - \alpha_i \beta_j)`$ shows that $`xy`$ is also integral over $`A`$. $`\square`$

```lean
/-- Proposition 1.18 (sum): The sum of integral elements is integral. -/
theorem integral_add {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {α β : B} (hα : IsIntegral A α) (hβ : IsIntegral A β) :
    IsIntegral A (α + β) :=
  hα.add hβ

/-- Proposition 1.18 (product): The product of integral elements is integral. -/
theorem integral_mul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {α β : B} (hα : IsIntegral A α) (hβ : IsIntegral A β) :
    IsIntegral A (α * β) :=
  hα.mul hβ
```

# Definition 1.19
%%%
number := false
%%%

_Definition 1.19._ Given a ring extension $`B/A`$, the ring $`\tilde{A} = \{b \in B : b \text{ is integral over } A\}`$ is the _integral closure_ of $`A`$ in $`B`$. When $`\tilde{A} = A`$ we say that $`A`$ is _integrally closed in $`B`$_. For a domain $`A`$, its _integral closure_ (or _normalization_) is its integral closure in its fraction field, and $`A`$ is _integrally closed_ (or _normal_) if it is integrally closed in its fraction field.

```lean
/-- Definition 1.19: The integral closure of R in A is the subalgebra of elements
integral over R. -/
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] :
    Subalgebra R A := integralClosure R A

/-- A domain R is integrally closed if it contains all elements of its fraction field
that are integral over it. -/
example {R : Type*} [CommRing R] [IsDomain R] :
    Prop := IsIntegrallyClosed R
```

# Proposition 1.20
%%%
number := false
%%%

_Proposition 1.20._ _If $`C/B/A`$ is a tower of ring extensions in which $`B`$ is integral over $`A`$ and $`C`$ is integral over $`B`$ then $`C`$ is integral over $`A`$._

_Proof._ See \[1, Thm. 10.27\] or \[2, Cor. 5.4\]. $`\square`$

```lean
/-- Proposition 1.20: If B is integral over A and C is integral over B, then
C is integral over A. -/
theorem integrality_trans {A B C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : Algebra.IsIntegral A B) (hBC : Algebra.IsIntegral B C) :
    Algebra.IsIntegral A C := by
  have := hAB; have := hBC; exact Algebra.IsIntegral.trans B
```

# Corollary 1.21
%%%
number := false
%%%

_Corollary 1.21._ _If $`B/A`$ is a ring extension, then the integral closure of $`A`$ in $`B`$ is integrally closed in $`B`$._

```lean
/-- Corollary 1.21: The integral closure of A in B is integrally closed in B.
This follows from the transitivity of integrality (Proposition 1.20). -/
theorem integralClosure_isIntegrallyClosedIn
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    IsIntegrallyClosedIn (integralClosure A B) B :=
  inferInstance
```

# Proposition 1.22
%%%
number := false
%%%

_Proposition 1.22._ _The ring $`\mathbb{Z}`$ is integrally closed._

_Proof._ We apply the rational root test: suppose $`r/s \in \mathbb{Q}`$ is integral over $`\mathbb{Z}`$, where $`r`$ and $`s`$ are coprime integers. Then

$$`\left(\frac{r}{s}\right)^n + a_{n-1} \left(\frac{r}{s}\right)^{n-1} + \cdots a_1 \left(\frac{r}{s}\right) + a_0 = 0`$$

for some $`a_0, \ldots, a_{n-1} \in \mathbb{Z}`$. Clearing denominators yields

$$`r^n + a_{n-1} s r^{n-1} + \cdots a_1 s^{n-1} r + a_0 s^n = 0,`$$

thus $`r^n = -s(a_{n-1} r^{n-1} + \cdots a_1 s^{n-2} r + a_0 s^{n-1})`$ is a multiple of $`s`$. But $`r`$ and $`s`$ are coprime, so $`s = \pm 1`$ and therefore $`r/s \in \mathbb{Z}`$. $`\square`$

```lean
/-- Proposition 1.22: ℤ is integrally closed in its fraction field ℚ.
This follows from the fact that ℤ is a UFD (hence integrally closed). -/
theorem int_isIntegrallyClosed : IsIntegrallyClosed ℤ := inferInstance
```

# Corollary 1.23
%%%
number := false
%%%

_Corollary 1.23._ _Every unique factorization domain is integrally closed. In particular, every PID is integrally closed._

_Proof._ The proof of Proposition 1.22 works for any UFD. $`\square`$

```lean
/-- Corollary 1.23: Every UFD is integrally closed. In particular, every PID
is integrally closed. This is `UniqueFactorizationMonoid.instIsIntegrallyClosed`
in Mathlib. -/
theorem ufd_isIntegrallyClosed (A : Type*) [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] : IsIntegrallyClosed A := inferInstance
```

# Example 1.24
%%%
number := false
%%%

_Example 1.24._ The ring $`\mathbb{Z}[\sqrt{5}]`$ is not a UFD (nor a PID) because it is not integrally closed: consider $`\phi = (1 + \sqrt{5})/2 \in \operatorname{Frac} \mathbb{Z}[\sqrt{5}]`$, which is integral over $`\mathbb{Z}`$ (and hence over $`\mathbb{Z}[\sqrt{5}]`$), since $`\phi^2 - \phi - 1 = 0`$. But $`\phi \notin \mathbb{Z}[\sqrt{5}]`$, so $`\mathbb{Z}[\sqrt{5}]`$ is not integrally closed.

The corollary implies that every discrete valuation ring is integrally closed. In fact, more is true.

```lean
/-- The golden ratio φ = (1 + √5)/2 satisfies φ² - φ - 1 = 0,
hence is integral over ℤ. -/
theorem golden_ratio_integral :
    let φ : ℝ := (1 + Real.sqrt 5) / 2
    φ ^ 2 - φ - 1 = 0 := by
  simp only
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  nlinarith [h5]

/-- Every element of ℤ[√5] has the form a + b√5 for some a, b ∈ ℤ. -/
private theorem adjoin_sqrt5_form (x : ℝ)
    (hx : x ∈ (Algebra.adjoin ℤ {Real.sqrt 5} : Subalgebra ℤ ℝ)) :
    ∃ a b : ℤ, x = ↑a + ↑b * Real.sqrt 5 := by
  refine Algebra.adjoin_induction (R := ℤ) (s := {Real.sqrt 5})
    (p := fun x _ => ∃ a b : ℤ, x = ↑a + ↑b * Real.sqrt 5) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact ⟨0, 1, by simp⟩
  · intro r
    exact ⟨r, 0, by simp⟩
  · intro x y _ _ ⟨a₁, b₁, h₁⟩ ⟨a₂, b₂, h₂⟩
    exact ⟨a₁ + a₂, b₁ + b₂, by rw [h₁, h₂]; push_cast; ring⟩
  · intro x y _ _ ⟨a₁, b₁, h₁⟩ ⟨a₂, b₂, h₂⟩
    refine ⟨a₁ * a₂ + 5 * b₁ * b₂, a₁ * b₂ + a₂ * b₁, ?_⟩
    rw [h₁, h₂]
    have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 :=
      Real.mul_self_sqrt (by norm_num : (5 : ℝ) ≥ 0)
    push_cast; linear_combination (↑b₁ * ↑b₂ : ℝ) * h5

/-- The golden ratio φ = (1 + √5)/2 is not in ℤ[√5].
Elements of ℤ[√5] have the form a + b√5 for a, b ∈ ℤ,
but φ = 1/2 + (1/2)√5 has non-integer coefficients. -/
theorem golden_ratio_not_in_Z_adjoin_sqrt5 :
    (1 + Real.sqrt 5) / 2 ∉ (Algebra.adjoin ℤ {Real.sqrt 5} : Subalgebra ℤ ℝ) := by
  intro hmem
  obtain ⟨a, b, hab⟩ := adjoin_sqrt5_form _ hmem
  have hirr : Irrational (Real.sqrt 5) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num]
    exact irrational_sqrt_natCast_iff.mpr (fun ⟨n, hn⟩ => by
      have : n ≤ 2 := by nlinarith
      interval_cases n <;> omega)
  have hodd : (1 : ℤ) - 2 * b ≠ 0 := by omega
  have h_key : (1 - 2 * (↑b : ℝ)) * Real.sqrt 5 = 2 * (↑a : ℝ) - 1 := by
    linear_combination 2 * hab
  exact hirr ⟨((2 * a - 1 : ℤ) : ℚ) / ((1 - 2 * b : ℤ) : ℚ), by
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, div_eq_iff
      (show ((1 - 2 * b : ℤ) : ℝ) ≠ 0 from Int.cast_ne_zero.mpr hodd)]
    push_cast; linarith [h_key]⟩

/-- Example 1.24: ℤ[√5] is not integrally closed. The golden ratio φ = (1 + √5)/2
is integral over ℤ (satisfying φ² - φ - 1 = 0) but does not lie in ℤ[√5]. -/
theorem Z_adjoin_sqrt5_not_integrally_closed :
    ¬ IsIntegrallyClosed (Algebra.adjoin ℤ {Real.sqrt 5} : Subalgebra ℤ ℝ) := by
  set S := (Algebra.adjoin ℤ {Real.sqrt 5} : Subalgebra ℤ ℝ)
  intro hIC
  -- Elements of S
  have h1s5_mem : (1 + Real.sqrt 5) ∈ S :=
    S.add_mem S.one_mem (Algebra.subset_adjoin rfl)
  set a : ↥S := ⟨1 + Real.sqrt 5, h1s5_mem⟩
  set b : ↥S := ⟨(2 : ℝ), S.algebraMap_mem 2⟩
  have hb_ne : b ≠ 0 := by intro h; apply_fun (↑· : ↥S → ℝ) at h; simp [b] at h
  -- φ = (1+√5)/2 in FractionRing S
  set aF := algebraMap ↥S (FractionRing ↥S) a
  set bF := algebraMap ↥S (FractionRing ↥S) b
  have hbF_ne : bF ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ↥S (FractionRing ↥S))).mpr hb_ne
  set φ : FractionRing ↥S := aF / bF
  -- Lift S ↪ ℝ to FractionRing S →+* ℝ
  have h_inj : Function.Injective (S.subtype : ↥S →+* ℝ) := Subtype.val_injective
  set ι : FractionRing ↥S →+* ℝ :=
    IsFractionRing.lift (A := ↥S) (K := FractionRing ↥S)
      (g := S.subtype) h_inj with hι_def
  -- ι maps algebraMap r to r.val
  have hι_alg : ∀ r : ↥S, ι (algebraMap ↥S (FractionRing ↥S) r) = (r : ℝ) :=
    fun r => IsFractionRing.lift_algebraMap h_inj r
  -- ι φ = (1+√5)/2 in ℝ
  have hι_φ : ι φ = (1 + Real.sqrt 5) / 2 := by
    simp only [φ, map_div₀, aF, bF, hι_alg, a, b]
  -- φ² - φ - 1 = 0 in FractionRing S
  have hφ_eq : φ ^ 2 - φ - 1 = 0 := by
    have ha2 : a ^ 2 - a * b - b ^ 2 = (0 : ↥S) := by
      ext
      simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, MulMemClass.coe_mul,
        ZeroMemClass.coe_zero]
      have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
      nlinarith [h5]
    have h := congr_arg (algebraMap ↥S (FractionRing ↥S)) ha2
    simp only [map_pow, map_mul, map_sub, map_zero] at h
    have hφb : φ * bF = aF := div_mul_cancel₀ aF hbF_ne
    have h1 : φ ^ 2 * bF ^ 2 = aF ^ 2 := by
      calc φ ^ 2 * bF ^ 2 = (φ * bF) ^ 2 := by ring
        _ = aF ^ 2 := by rw [hφb]
    have h2 : φ * bF ^ 2 = aF * bF := by
      calc φ * bF ^ 2 = (φ * bF) * bF := by ring
        _ = aF * bF := by rw [hφb]
    have key : (φ ^ 2 - φ - 1) * bF ^ 2 = 0 := by linear_combination h1 - h2 + h
    exact (mul_eq_zero.mp key).resolve_right (pow_ne_zero 2 hbF_ne)
  -- φ is integral over ℤ, hence over S
  have hφ_int : IsIntegral ↥S φ := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X - 1, ?_, ?_⟩
    · -- Monic: X^2 - (X + 1) has leading term from X^2
      have : Polynomial.X ^ 2 - Polynomial.X - (1 : Polynomial ↥S) =
             Polynomial.X ^ 2 - (Polynomial.X + 1 : Polynomial ↥S) := sub_sub _ _ _
      rw [this]
      exact (Polynomial.monic_X_pow 2).sub_of_left (by
        calc (Polynomial.X + 1 : Polynomial ↥S).degree
            ≤ max (Polynomial.X : Polynomial ↥S).degree (1 : Polynomial ↥S).degree :=
              Polynomial.degree_add_le _ _
          _ < (Polynomial.X ^ 2 : Polynomial ↥S).degree := by
              simp [Polynomial.degree_X, Polynomial.degree_one])
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_one]
      exact hφ_eq
  -- By IsIntegrallyClosed: φ in image of algebraMap
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff (K := FractionRing ↥S)).mp hIC hφ_int
  -- Apply ι: y.val = (1+√5)/2 in ℝ
  have : (y : ℝ) = (1 + Real.sqrt 5) / 2 := by
    have h := congr_arg ι hy
    rw [hι_alg, hι_φ] at h
    exact h
  -- Contradiction: y ∈ S but (1+√5)/2 ∉ S
  exact golden_ratio_not_in_Z_adjoin_sqrt5 (this ▸ y.2)
```

# Proposition 1.25
%%%
number := false
%%%

_Proposition 1.25._ _Every valuation ring is integrally closed._

_Proof._ Let $`A`$ be a valuation ring with fraction field $`k`$ and let $`\alpha \in k`$ be integral over $`A`$. Then

$$`\alpha^n + a_{n-1} \alpha^{n-1} + a_{n-2} \alpha^{n-2} + \cdots + a_1 \alpha + a_0 = 0`$$

for some $`a_0, a_1, \ldots, a_{n-1} \in A`$. Suppose $`\alpha \notin A`$. Then $`\alpha^{-1} \in A`$, since $`A`$ is a valuation ring. Multiplying the equation above by $`\alpha^{-(n-1)} \in A`$ and moving all but the first term on the LHS to the RHS yields

$$`\alpha = -a_{n-1} - a_{n-1} \alpha^{-1} - \cdots - a_1 \alpha^{2-n} - a_0 \alpha^{1-n} \in A,`$$

contradicting our assumption that $`\alpha \notin A`$. It follows that $`A`$ is integrally closed. $`\square`$

```lean
/-- Proposition 1.25: Every valuation ring is integrally closed.
If A is a valuation ring (for every x in Frac(A), either x ∈ A or x⁻¹ ∈ A),
then A is integrally closed in its fraction field. -/
theorem valuationRing_isIntegrallyClosed (A : Type*) [CommRing A] [IsDomain A]
    [ValuationRing A] : IsIntegrallyClosed A :=
  IsIntegrallyClosed.of_equiv (ValuationRing.equivInteger A (FractionRing A)).symm
```
