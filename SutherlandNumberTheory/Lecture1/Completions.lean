import VersoManual
import Mathlib.Tactic.Recall
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Polynomial.Reverse

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.code.warnLineLength 90
open IsLocalRing Module

#doc (Manual) "Completions and Discrete Valuations" =>
%%%
tag := "completions"
file := some "completions"
number := false
%%%

# Definition 1.10
%%%
number := false
%%%

_Definition 1.10._ A _valuation_ on a field $`k` is a group homomorphism $`k^{\times} \to \mathbb{R}` such that for all $`x, y \in k` we have

$$`v(x + y) \geq \min\bigl(v(x), v(y)\bigr).`

We may extend $`v` to a map $`k \to \mathbb{R} \cup \{\infty\}` by defining $`v(0) \coloneqq \infty`. For any $`0 < c < 1`, defining $`\lvert x \rvert_v \coloneqq c^{v(x)}` yields a nonarchimedean absolute value. The image of $`v` in $`\mathbb{R}` is the
_value group_ of $`v`. We say that $`v` is a _discrete valuation_ if its value group is equal to $`\mathbb{Z}` (every discrete subgroup of $`\mathbb{R}` is isomorphic to $`\mathbb{Z}`, so we can always rescale a valuation with a discrete value group so that this holds). Given a field $`k` with valuation $`v`, the set

$$`A := \{x \in k : v(x) \geq 0\},`

is the _valuation ring_ of $`k` (with respect to $`v`). A _discrete valuation ring_ (DVR) is an integral domain that is the valuation ring of its fraction field with respect to a discrete valuation; such a ring $`A` cannot be a field, since $`v(\operatorname{Frac} A) = \mathbb{Z} \neq \mathbb{Z}_{\geq 0} = v(A)`.

```lean
/-- Definition 1.10: A valuation on a field in the
additive convention. -/
recall AddValuation (R : Type*) [Ring R]
    (Γ₀ : Type*)
    [LinearOrderedAddCommMonoidWithTop Γ₀] :
    Type _

/-- Definition 1.10: A valuation v : R → Γ₀ in the
multiplicative convention. -/
recall Valuation (R : Type*) (Γ₀ : Type*)
    [LinearOrderedCommMonoidWithZero Γ₀]
    [Ring R] : Type _

/-- Definition 1.10: The value group of a
valuation. -/
recall MonoidWithZeroHom.valueGroup
    {A : Type*} {B : Type*} {F : Type*}
    [FunLike F A B] (f : F) [MonoidWithZero A]
    [MonoidWithZero B]
    [MonoidWithZeroHomClass F A B] :
    Subgroup Bˣ

/-- Definition 1.10: A discrete valuation has a
cyclic nontrivial value group. -/
example (R : Type*) (Γ₀ : Type*)
    [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀)
    [Valuation.IsRankOneDiscrete v] :
    True := trivial

/-- Definition 1.10 (DVR). A discrete valuation ring
is an integral domain that is a local PID and not a
field. -/
recall IsDiscreteValuationRing (R : Type*)
    [CommRing R] [IsDomain R] : Prop

/-- Definition 1.10: The valuation ring: for every x
in Frac(A), either x ∈ A or x⁻¹ ∈ A. -/
recall ValuationRing (A : Type*)
    [CommRing A] [IsDomain A] : Prop

/-- Definition 1.10: A DVR cannot be a field. -/
recall IsDiscreteValuationRing.not_isField
    {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : ¬IsField R

section DVREquivalence

/-! ### Bridging: book's DVR definition ↔ Mathlib's

The book defines a DVR as "an integral domain that
is the valuation ring of its fraction field with
respect to a discrete valuation." Mathlib defines
`IsDiscreteValuationRing A` as "a local PID that is
not a field."

**Forward (Mathlib → book):** Given
`IsDiscreteValuationRing A`, the adic valuation of
the maximal ideal extends to a discrete valuation `v`
on `Frac(A)`, and `A ≃+* v.valuationSubring`.

**Reverse (book → Mathlib):** Given a discrete
valuation `v` on a field `K`,
`v.valuationSubring` is a DVR. -/

/-- **Reverse direction**: The valuation subring of a
discrete valuation is a DVR (Mathlib sense). -/
example (K : Type*)
    [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) [v.IsRankOneDiscrete] :
    IsDiscreteValuationRing v.valuationSubring :=
  inferInstance

end DVREquivalence
```

# Valuation ring structure
%%%
number := false
%%%

It is easy to verify that every valuation ring $`A` is a in fact a ring, and even an integral domain (if $`x` and $`y` are nonzero then $`v(xy) = v(x) + v(y) \neq \infty`, so $`xy \neq 0`), with $`k` as its fraction field. Notice that for any $`x \in k^{\times}` we have $`v(1/x) = v(1) - v(x) = -v(x)`, so at least one of $`x` and $`1/x` has nonnegative valuation and lies in $`A`. It follows that $`x \in A` is invertible (in $`A`) if and only if $`v(x) = 0`, hence the unit group of $`A` is

$$`A^{\times} = \{x \in k : v(x) = 0\},`

We can partition the nonzero elements of $`k` according to the sign of their valuation. Elements with valuation zero are units in $`A`, elements with positive valuation are non-units in $`A`, and elements with negative valuation do not lie in $`A`, but their multiplicative inverses are non-units in $`A`. This leads to a more general notion of a valuation ring.

```lean
/-- v(x⁻¹) = -v(x) for an additive valuation on a
field. -/
recall AddValuation.map_inv
    {K : Type*} [DivisionRing K]
    {Γ₀ : Type*}
    [LinearOrderedAddCommGroupWithTop Γ₀]
    (v : AddValuation K Γ₀) {x : K} :
    v x⁻¹ = -(v x)

/-- x ∈ A is a unit iff v(x) = 1 (multiplicative
convention; i.e. v(x) = 0 additively). -/
recall Valuation.Integers.isUnit_iff_valuation_eq_one
    {F : Type*} {Γ₀ : Type*}
    [Field F]
    [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation F Γ₀} {O : Type*}
    [CommRing O] [Algebra O F]
    (hv : Valuation.Integers v O)
    {x : O} :
    IsUnit x ↔ v (algebraMap O F x) = 1

/-- The nonzero elements of a valued field partition
into three classes by the sign of their valuation. -/
theorem valuation_trichotomy
    {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (x : K) :
    v x = 1 ∨ v x < 1 ∨ 1 < v x := by
  rcases lt_trichotomy (v x) 1 with h | h | h
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inr h)
```

# Definition 1.11
%%%
number := false
%%%

_Definition 1.11._ A _valuation ring_ is an integral domain $`A` with fraction field $`k` with the property that for every $`x \in k`, either $`x \in A` or $`x^{-1} \in A`.

```lean
/-- Definition 1.11: A valuation ring. -/
recall ValuationRing (A : Type*)
    [CommRing A] [IsDomain A] : Prop
```

# Uniformizers and ideals
%%%
number := false
%%%

Let us now suppose that the integral domain $`A` is the valuation ring of its fraction field with respect to some discrete valuation $`v` (which we shall see is uniquely determined). Any element $`\pi \in A` for which $`v(\pi) = 1` is called a _uniformizer_. Uniformizers exist, since $`v(A) = \mathbb{Z}_{\geq 0}`. If we fix a uniformizer $`\pi`, every $`x \in k^{\times}` can be written uniquely as

$$`x = u\pi^n`

where $`n = v(x)` and $`u = x/\pi^n \in A^{\times}` and uniquely determined. It follows that $`A` is a unique factorization domain (UFD), and in fact $`A` is a principal ideal domain (PID). Indeed, every nonzero ideal of $`A` is equal to

$$`(\pi^n) = \{a \in A : v(a) \geq n\},`

for some integer $`n \geq 0`. Moreover, the ideal $`(\pi^n)` depends only on $`n`, not the choice of uniformizer $`\pi`: if $`\pi'` is any other uniformizer its unique representation $`\pi' = u\pi^1` differs from $`\pi` only by a unit. The ideals of $`A` are thus totally ordered, and the ideal

$$`\mathfrak{m} = (\pi) = \{a \in A : v(a) > 0\}`

is the unique maximal ideal of $`A` (and also the only nonzero prime ideal of $`A`).

```lean
variable {R : Type*} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] in
/-- An irreducible element of a DVR generates the
maximal ideal (uniformizer characterization). -/
example (ϖ : R) :
    Irreducible ϖ ↔
      IsLocalRing.maximalIdeal R =
        Ideal.span {ϖ} :=
  IsDiscreteValuationRing.irreducible_iff_uniformizer
    ϖ

/-- Uniformizers (irreducible elements) exist in a
DVR. -/
recall IsDiscreteValuationRing.exists_irreducible
    {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    ∃ ϖ : R, Irreducible ϖ

/-- Every nonzero element is associated to a power
of the uniformizer. -/
recall
  IsDiscreteValuationRing.associated_pow_irreducible
    {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    {a : R} (ha : a ≠ 0) {ϖ : R}
    (hirr : Irreducible ϖ) :
    ∃ n : ℕ, Associated a (ϖ ^ n)

/-- The additive valuation of a DVR. -/
recall IsDiscreteValuationRing.addVal
    (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    AddValuation R ℕ∞

variable {R : Type*} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] in
/-- A DVR is a principal ideal ring. -/
example : IsPrincipalIdealRing R := inferInstance

variable {R : Type*} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] in
/-- A DVR is a unique factorization domain. -/
example : UniqueFactorizationMonoid R :=
  inferInstance

/-- Every nonzero ideal of a DVR is generated by a
power of the uniformizer. -/
recall
  IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    {s : Ideal R} (hs : s ≠ ⊥) {ϖ : R}
    (hirr : Irreducible ϖ) :
    ∃ n : ℕ, s = Ideal.span {ϖ ^ n}

variable {R : Type*} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] in
/-- The ideals of a DVR are totally ordered. -/
example (I J : Ideal R) : I ≤ J ∨ J ≤ I :=
  (ValuationRing.le_total_ideal (A := R)).total
    I J

variable {R : Type*} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] in
/-- The maximal ideal of a DVR is generated by any
uniformizer. -/
theorem maximalIdeal_eq_span_uniformizer
    (ϖ : R) (hirr : Irreducible ϖ) :
    IsLocalRing.maximalIdeal R =
      Ideal.span {ϖ} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer
    ϖ).mp hirr

/-- A DVR is a PID with exactly one nonzero prime
ideal. -/
recall
  IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
    (R : Type u) [CommRing R] [IsDomain R] :
    IsDiscreteValuationRing R ↔
      IsPrincipalIdealRing R ∧
        ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime

/-- Any two irreducible elements of a DVR are
associated (differ by a unit). -/
recall
  IsDiscreteValuationRing.associated_of_irreducible
    {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    {a b : R} (ha : Irreducible a)
    (hb : Irreducible b) :
    Associated a b
```

# Definition 1.12
%%%
number := false
%%%

_Definition 1.12._ A _local ring_ is a commutative ring with a unique maximal ideal.

```lean
/-- Definition 1.12: A local ring has a unique maximal
ideal. -/
recall IsLocalRing (R : Type*) [Semiring R] : Prop
```

# Definition 1.13
%%%
number := false
%%%

_Definition 1.13._ The _residue field_ of a local ring $`A` with maximal ideal $`\mathfrak{m}` is the field $`A/\mathfrak{m}`.

```lean
/-- Definition 1.13: The residue field A/𝔪. -/
recall IsLocalRing.ResidueField (A : Type*)
    [CommRing A] [IsLocalRing A] : Type _
```

# Determining the valuation
%%%
number := false
%%%

We can now see how to determine the valuation $`v` corresponding to a discrete valuation ring $`A`. Given a discrete valuation ring $`A` with unique maximal ideal $`\mathfrak{m}`, we may define $`v \colon A \to \mathbb{Z}` by letting $`v(a)` be the unique integer $`n` for which $`(a) = \mathfrak{m}^n` and $`v(0) \coloneqq \infty`. Extending $`v` to the fraction field $`k` of $`A` via $`v(a/b) \coloneqq v(a) - v(b)` gives a discrete valuation $`v` on $`k` for which $`A = \{x \in k : v(x) \geq 0\}` is the corresponding valuation ring.

Notice that any discrete valuation $`v` on $`k` with $`A` as its valuation ring must satisfy $`v(\pi) = 1` for some $`\pi \in \mathfrak{m}` (otherwise $`v(k) \neq \mathbb{Z}`), and we then have $`v(\pi) = 1` if and only if $`\mathfrak{m} = (\pi)`. Moreover, $`v` must then coincide with the discrete valuation we just defined: for any DVR $`A`, the discrete valuation on the fraction field of $`A` that yields $`A` as its valuation ring is uniquely determined. It follows that we could have defined a uniformizer to be any generator of the maximal ideal of $`A` without reference to a valuation.

```lean
/-- The maximal ideal of a DVR, viewed as a
height-one prime. -/
recall IsDiscreteValuationRing.maximalIdeal
    (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] :
    IsDedekindDomain.HeightOneSpectrum A

/-- A DVR is isomorphic to the valuation subring of
its fraction field under the adic valuation. -/
recall
  IsDiscreteValuationRing.equivValuationSubring
    (A : Type*) (K : Type*)
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [Field K] [Algebra A K]
    [IsFractionRing A K] :
    A ≃+*
      ((IsDiscreteValuationRing.maximalIdeal
        A).valuation K).valuationSubring

/-- The adic valuation on the fraction field of a
DVR is rank-one discrete. -/
recall
  IsDiscreteValuationRing.isRankOneDiscrete
    (A : Type*) (K : Type*)
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [Field K] [Algebra A K]
    [IsFractionRing A K] :
    Valuation.IsRankOneDiscrete
      ((IsDiscreteValuationRing.maximalIdeal
        A).valuation K)

/-- A generator of the maximal ideal is a
uniformizer. -/
recall
  Valuation.isUniformizer_of_maximalIdeal_eq_span
    {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ]
    {K : Type*} [Field K]
    (v : Valuation K Γ)
    [v.IsRankOneDiscrete]
    {r : v.valuationSubring}
    (hr : IsLocalRing.maximalIdeal
        v.valuationSubring =
      Ideal.span {r}) :
    v.IsUniformizer r

/-- A uniformizer generates the maximal ideal. -/
recall Valuation.IsUniformizer.is_generator
    {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ]
    {K : Type*} [Field K]
    {v : Valuation K Γ}
    [hv : v.IsRankOneDiscrete]
    {π : v.valuationSubring}
    (hπ : v.IsUniformizer π) :
    IsLocalRing.maximalIdeal
        v.valuationSubring =
      Ideal.span {π}
```

# Example 1.14
%%%
number := false
%%%

_Example 1.14._ For the $`p`-adic valuation $`v_p \colon \mathbb{Q} \to \mathbb{Z} \cup \{\infty\}` we have the valuation ring

$$`\mathbb{Z}_{(p)} \coloneqq \left\{\frac{a}{b} : a, b \in \mathbb{Z},\, p \nmid b\right\},`

with maximal ideal $`\mathfrak{m} = (p)`; this is the _localization_ of the ring $`\mathbb{Z}` at the prime ideal $`(p)`. The residue field is $`\mathbb{Z}_{(p)}/p\mathbb{Z}_{(p)} \simeq \mathbb{Z}/p\mathbb{Z} \simeq \mathbb{F}_p`.

```lean
/-- The prime ideal (p) in ℤ is prime when p is
a prime natural number. -/
theorem primeIdealZ_isPrime (p : ℕ)
    [hp : Fact (Nat.Prime p)] :
    (Ideal.span {(p : ℤ)} : Ideal ℤ).IsPrime := by
  rw [Ideal.span_singleton_prime
    (by exact_mod_cast hp.out.ne_zero)]
  exact Nat.prime_iff_prime_int.mp hp.out

/-- Example 1.14: The localization ℤ_(p) is a DVR. -/
theorem localization_at_prime_is_dvr (p : ℕ)
    [hp : Fact (Nat.Prime p)]
    (I : Ideal ℤ) [I.IsPrime]
    (hI : I = Ideal.span {(p : ℤ)}) :
    IsDiscreteValuationRing
      (Localization.AtPrime I) := by
  have hI_ne_bot : I ≠ ⊥ := by
    rw [hI, ne_eq, Ideal.span_singleton_eq_bot]
    exact mod_cast hp.out.ne_zero
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hI_ne_bot _

/-- Example 1.14: The residue field of ℤ_(p) is
isomorphic to ℤ/pℤ ≃ 𝔽_p. -/
theorem localization_at_prime_residue_field (p : ℕ)
    [hp : Fact (Nat.Prime p)]
    (I : Ideal ℤ) [I.IsPrime]
    (hI : I = Ideal.span {(p : ℤ)}) :
    Nonempty (IsLocalRing.ResidueField
      (Localization.AtPrime I) ≃+* ZMod p) := by
  subst hI
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (by
      rw [ne_eq, Ideal.span_singleton_eq_bot]
      exact mod_cast hp.out.ne_zero)
  exact ⟨(IsLocalization.AtPrime.equivQuotMaximalIdeal
    (Ideal.span {(p : ℤ)})
    (Localization.AtPrime _)).symm.trans
    (Int.quotientSpanNatEquivZMod p)⟩
```

# Example 1.15
%%%
number := false
%%%

_Example 1.15._ For any field $`k`, the valuation $`v \colon k((t)) \to \mathbb{Z} \cup \{\infty\}` on the field of Laurent series over $`k` defined by

$$`v\!\left(\sum_{n \geq n_0} a_n t^n\right) = n_0,`

where $`a_{n_0} \neq 0`, has valuation ring $`k[[t]]`, the power series ring over $`k`. For $`f \in k((t))^{\times}`, the valuation $`v(f) \in \mathbb{Z}` is the _order of vanishing_ of $`f` at zero. For every $`\alpha \in k` one can similarly define a valuation $`v_{\alpha}` on $`k` as the order of vanishing of $`f` at $`\alpha` by taking the Laurent series expansion of $`f` about $`\alpha`.

```lean
open PowerSeries in
set_option backward.isDefEq.respectTransparency false in
/-- Example 1.15: k⟦X⟧ is a DVR for any field k. -/
example {k : Type*} [Field k] :
    IsDiscreteValuationRing k⟦X⟧ := inferInstance

open PowerSeries in
set_option backward.isDefEq.respectTransparency false in
/-- k⟦X⟧ is also a valuation ring. -/
example {k : Type*} [Field k] :
    ValuationRing k⟦X⟧ := inferInstance

/-! ### The X-adic valuation on Laurent series

Mathlib equips the Laurent series field `k⸨X⸩`
with the X-adic valuation via the `Valued`
instance, built from the height-one-spectrum
valuation of the prime ideal `(X) ⊂ k⟦X⟧`. -/

open scoped LaurentSeries WithZero in
/-- The Laurent series field `k⸨X⸩` carries a
canonical X-adic valuation with values in ℤᵐ⁰. -/
noncomputable example (k : Type*) [Field k] :
    Valued k⸨X⸩ ℤᵐ⁰ := inferInstance

/-! ### The valuation ring is k⟦X⟧

The mathematical content of Example 1.15: the
valuation ring of the X-adic valuation on `k((t))`
is exactly `k[[t]]`. In Mathlib this is
`LaurentSeries.val_le_one_iff_eq_coe`. -/

open scoped LaurentSeries WithZero in
open PowerSeries in
set_option backward.isDefEq.respectTransparency false in
/-- Example 1.15 (key result): the valuation ring of
the X-adic valuation on k⸨X⸩ is k⟦X⟧. -/
example (k : Type*) [Field k] (f : k⸨X⸩) :
    Valued.v f ≤ (1 : ℤᵐ⁰) ↔
      ∃ F : k⟦X⟧, (F : k⸨X⸩) = f :=
  LaurentSeries.val_le_one_iff_eq_coe k f

/-! ### The order function as valuation

`PowerSeries.order` gives the valuation
`v(φ) = n₀` from Example 1.15. The order is
multiplicative and equals the multiplicity of `X`
in `φ`. -/

open PowerSeries in
recall PowerSeries.order (R : Type*)
    [Semiring R] (φ : PowerSeries R) : ℕ∞

open PowerSeries in
recall PowerSeries.order_mul (R : Type*)
    [Semiring R] [NoZeroDivisors R]
    (φ ψ : PowerSeries R) :
    PowerSeries.order (φ * ψ) =
      PowerSeries.order φ +
        PowerSeries.order ψ

open PowerSeries in
recall PowerSeries.order_eq_emultiplicity_X
    (R : Type*) [Semiring R]
    (φ : PowerSeries R) :
    PowerSeries.order φ =
      emultiplicity PowerSeries.X φ

/-! ### The valuation determines the first nonzero
coefficient -/

open scoped LaurentSeries WithZero in
open PowerSeries WithZero in
set_option backward.isDefEq.respectTransparency false in
/-- The valuation of a power series `f` satisfies
`v(f) ≤ exp(-d)` iff all coefficients of index
`< d` vanish. -/
example (k : Type*) [Field k]
    {d : ℕ} (f : k⟦X⟧) :
    Valued.v (f : k⸨X⸩) ≤
      Multiplicative.ofAdd (-d : ℤ) ↔
        ∀ n : ℕ, n < d → coeff n f = 0 :=
  LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero
    k f
```

# Properties of DVRs
%%%
number := false
%%%

Discrete valuation rings are in many respects the nicest rings that are not fields. In addition to being an integral domain, every discrete valuation ring $`A` enjoys the following properties:

- _noetherian_: Every increasing sequence $`I_1 \subseteq I_2 \subseteq \cdots` of ideals eventually stabilizes; equivalently, every ideal is finitely generated.
- _principal ideal domain_: Every ideal is principal (generated by a single element).
- _local_: There is a unique maximal ideal $`\mathfrak{m}`.
- _dimension one_: The (Krull) _dimension_ of a ring $`R` is the supremum of the lengths $`n` of all chains of prime ideals $`\mathfrak{p}_0 \subsetneq \mathfrak{p}_1 \subsetneq \cdots \subsetneq \mathfrak{p}_n` (which need not be finite, in general). For DVRs, $`(0) \subseteq \mathfrak{m}` is the longest chain of prime ideals, with length 1.
- _regular_: The dimension of the $`A/\mathfrak{m}`-vector space $`\mathfrak{m}/\mathfrak{m}^2` is equal to the dimension of $`A`. Non-local rings are regular if this holds for every localization at a prime ideal.
- _integrally closed_ (or _normal_): Every element of the fraction field of $`A` that is the root of a monic polynomial in $`A[x]` lies in $`A`.
- _maximal_: There are no intermediate rings strictly between $`A` and its fraction field.

Various combinations of these properties can be used to uniquely characterize discrete valuation rings (and hence give alternative definitions).

# Theorem 1.16
%%%
number := false
%%%

_Theorem 1.16._ _For an integral domain $`A`, the following are equivalent:_

- _$`A` is a DVR._
- _$`A` is a noetherian valuation ring that is not a field._
- _$`A` is a local PID that is not a field._
- _$`A` is an integrally closed noetherian local ring of dimension one._
- _$`A` is a regular noetherian local ring of dimension one ($`\dim_k(\mathfrak{m}/\mathfrak{m}^2) = 1`)._
- _$`A` is a noetherian local ring whose maximal ideal is nonzero and principal._
- _$`A` is a maximal noetherian local ring of dimension one (no intermediate subalgebras between $`A` and $`\operatorname{Frac}(A)`)._

_Proof._ See \[1, §23\] or \[2, §9\]. $`\square`

```lean
section MaximalSubalgebra

variable {A : Type*} [CommRing A] [IsDomain A]

/-- In a DVR, there are no intermediate subalgebras
between `A` and `Frac(A)`. -/
theorem dvr_subalgebra_eq_bot_or_top
    [IsDiscreteValuationRing A]
    (S : Subalgebra A (FractionRing A)) :
    S = ⊥ ∨ S = ⊤ := by
  set K := FractionRing A
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible
      (R := A)
  suffices h : S ≠ ⊥ → S = ⊤ from
    (eq_or_ne S ⊥).elim Or.inl
      (fun hne => Or.inr (h hne))
  intro hne
  have ⟨x, hxS, hxbot⟩ :=
    SetLike.exists_of_lt
      (bot_lt_iff_ne_bot.mpr hne)
  rw [Algebra.mem_bot] at hxbot
  obtain ⟨a, ha⟩ :=
    (ValuationRing.isInteger_or_isInteger
      A x).resolve_left
      (fun ⟨c, hc⟩ => hxbot ⟨c, hc⟩)
  have ha0 : a ≠ 0 := by
    intro h; rw [h, map_zero] at ha
    have hx0 : x = 0 := by
      rwa [eq_comm, inv_eq_zero] at ha
    exact hxbot ⟨0, by simp [hx0]⟩
  obtain ⟨n, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      ha0 hϖ
  have hn : 0 < n := by
    rcases n with _ | n
    · simp only [pow_zero, mul_one] at ha
      exact absurd
        ⟨↑u⁻¹, by rw [map_units_inv, ha,
          inv_inv]⟩ hxbot
    · exact Nat.succ_pos n
  have hϖ_ne : algebraMap A K ϖ ≠ 0 :=
    IsFractionRing.to_map_eq_zero_iff.not.mpr
      hϖ.ne_zero
  have hϖ_inv :
      (algebraMap A K ϖ)⁻¹ ∈ S := by
    have ha' : algebraMap A K (↑u * ϖ ^ n) =
        x⁻¹ := ha
    have hu_ne :
        algebraMap A K (↑u : A) ≠ 0 :=
      IsFractionRing.to_map_eq_zero_iff.not.mpr
        (Units.ne_zero u)
    have h1 : algebraMap A K ↑u * x =
        ((algebraMap A K ϖ)⁻¹) ^ n := by
      have hx :
          x = (algebraMap A K
            (↑u * ϖ ^ n))⁻¹ := by
        rw [ha', inv_inv]
      rw [hx, map_mul, map_pow,
        mul_inv_rev,
        mul_comm ((algebraMap A K ϖ) ^ n)⁻¹,
        ← mul_assoc, mul_inv_cancel₀ hu_ne,
        one_mul, inv_pow]
    have h2 :
        ((algebraMap A K ϖ)⁻¹) ^ n ∈ S :=
      h1 ▸ S.mul_mem (S.algebraMap_mem ↑u) hxS
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1,
        (Nat.succ_pred_eq_of_pos hn).symm⟩
    have h3 : algebraMap A K ϖ ^ m *
        ((algebraMap A K ϖ)⁻¹) ^ (m + 1) =
        (algebraMap A K ϖ)⁻¹ := by
      rw [pow_succ, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ hϖ_ne, one_pow,
        one_mul]
    exact h3 ▸ S.mul_mem
      (S.pow_mem (S.algebraMap_mem ϖ) _) h2
  rw [eq_top_iff]
  intro y _
  obtain ⟨a', b', hb', hy⟩ :=
    IsFractionRing.div_surjective A y
  rw [← hy]
  have hb'0 : b' ≠ 0 :=
    nonZeroDivisors.ne_zero hb'
  obtain ⟨k, v, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      hb'0 hϖ
  have h_inv_b :
      (algebraMap A K (↑v * ϖ ^ k))⁻¹
        ∈ S := by
    rw [map_mul, map_pow,
      mul_inv_rev, ← inv_pow]
    refine S.mul_mem
      (S.pow_mem hϖ_inv k) ?_
    rw [← map_units_inv]
    exact S.algebraMap_mem _
  rw [div_eq_mul_inv]
  exact S.mul_mem
    (S.algebraMap_mem a') h_inv_b

/-- If `x ∈ A[x⁻¹]` and `x ≠ 0`, then `x` is
integral over `A`. -/
theorem isIntegral_of_mem_adjoin_inv
    [Field K] [Algebra A K] [IsFractionRing A K]
    {x : K} (hx : x ≠ 0)
    (hmem : x ∈ Algebra.adjoin A {x⁻¹}) :
    IsIntegral A x := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
    at hmem
  obtain ⟨p, hp⟩ := hmem
  set q := (1 : Polynomial A) -
    Polynomial.X * p with hq_def
  have hp' : Polynomial.aeval x⁻¹ p = x := hp
  have hq_root : Polynomial.aeval x⁻¹ q = 0 := by
    simp only [q, map_sub, map_one, map_mul,
      Polynomial.aeval_X, hp',
      inv_mul_cancel₀ hx, sub_self]
  letI : Invertible x⁻¹ :=
    invertibleOfNonzero (inv_ne_zero hx)
  have hx_root : Polynomial.aeval x
      (Polynomial.reverse q) = 0 := by
    have h :=
      (Polynomial.eval₂_reverse_eq_zero_iff
        (algebraMap A K) x⁻¹ q).mpr
    simp only [invOf_eq_inv, inv_inv] at h
    exact h hq_root
  have hq_monic :
      (Polynomial.reverse q).Monic := by
    rw [Polynomial.Monic,
      Polynomial.reverse_leadingCoeff,
      Polynomial.trailingCoeff]
    have hcoeff0 : q.coeff 0 = 1 := by
      simp [q, Polynomial.coeff_sub,
        Polynomial.coeff_one_zero]
    have hntd : q.natTrailingDegree = 0 :=
      Nat.eq_zero_of_le_zero
        (Polynomial.natTrailingDegree_le_of_ne_zero
          (hcoeff0 ▸ one_ne_zero))
    rw [hntd, hcoeff0]
  exact ⟨Polynomial.reverse q,
    hq_monic, hx_root⟩

/-- A noetherian local domain that is not a field
and admits no intermediate subalgebras between itself
and its fraction field is a DVR. -/
theorem maximal_noetherian_local_is_dvr
    [IsNoetherianRing A] [IsLocalRing A]
    (hF : ¬IsField A)
    (hmax : ∀ S : Subalgebra A (FractionRing A),
      S = ⊥ ∨ S = ⊤) :
    IsDiscreteValuationRing A := by
  set K := FractionRing A
  have hIC : IsIntegrallyClosed A := by
    rw [isIntegrallyClosed_iff K]
    intro x hx
    have hS := hmax (Algebra.adjoin A {x})
    cases hS with
    | inl hbot =>
      have hx_mem : x ∈ Algebra.adjoin A {x} :=
        Algebra.subset_adjoin rfl
      rw [hbot] at hx_mem
      exact hx_mem
    | inr htop =>
      exfalso; apply hF
      have hfg := hx.fg_adjoin_singleton
      rw [htop] at hfg
      haveI : Module.Finite A K :=
        ⟨by simpa using hfg⟩
      exact isField_of_isIntegral_of_isField
        (IsFractionRing.injective A K)
        (Field.toIsField K)
  haveI := hIC
  have hVR : ValuationRing A := by
    rw [ValuationRing.iff_isInteger_or_isInteger
      A K]
    intro x
    cases hmax (Algebra.adjoin A {x}) with
    | inl hbot =>
      left
      have : x ∈ Algebra.adjoin A {x} :=
        Algebra.subset_adjoin rfl
      rw [hbot, Algebra.mem_bot] at this
      exact this
    | inr htop =>
      cases hmax (Algebra.adjoin A {x⁻¹}) with
      | inl hbot =>
        right
        have : x⁻¹ ∈ Algebra.adjoin A {x⁻¹} :=
          Algebra.subset_adjoin rfl
        rw [hbot, Algebra.mem_bot] at this
        exact this
      | inr htop' =>
        left
        have hx_mem :
            x ∈ Algebra.adjoin A
              ({x⁻¹} : Set K) :=
          htop' ▸ Algebra.mem_top
        by_cases hx0 : x = 0
        · exact ⟨0, by simp [hx0]⟩
        · exact (isIntegrallyClosed_iff K).mp hIC
            (isIntegral_of_mem_adjoin_inv
              hx0 hx_mem)
  exact
    ((IsDiscreteValuationRing.TFAE (R := A)
      hF).out 1 0).mp hVR

end MaximalSubalgebra

/-- Theorem 1.16: Seven equivalent characterizations
of DVRs. -/
theorem sutherland_theorem1_16
    (A : Type*) [CommRing A] [IsDomain A] :
    List.TFAE [
      IsDiscreteValuationRing A,
      IsNoetherianRing A ∧ ValuationRing A ∧
        ¬IsField A,
      IsLocalRing A ∧ IsPrincipalIdealRing A ∧
        ¬IsField A,
      IsIntegrallyClosed A ∧ IsNoetherianRing A ∧
        IsLocalRing A ∧
        ∃! P : Ideal A, P ≠ ⊥ ∧ P.IsPrime,
      IsNoetherianRing A ∧ IsLocalRing A ∧
        ∃ m : Ideal A,
          m.IsMaximal ∧
            finrank (A ⧸ m) m.Cotangent = 1,
      IsNoetherianRing A ∧ IsLocalRing A ∧
        ∃ m : Ideal A,
          m.IsMaximal ∧ m ≠ ⊥ ∧ m.IsPrincipal,
      IsNoetherianRing A ∧ IsLocalRing A ∧
        ¬IsField A ∧
        ∀ S : Subalgebra A (FractionRing A),
          S = ⊥ ∨ S = ⊤
    ] := by
  -- 1 → 2
  tfae_have 1 → 2
  | h => ⟨inferInstance, inferInstance,
    h.not_isField⟩
  -- 2 → 1
  tfae_have 2 → 1
  | ⟨hN, hV, hF⟩ => by
    haveI := hN; haveI := hV
    haveI : IsLocalRing A := inferInstance
    have hF' : ¬IsField A := hF
    exact ((IsDiscreteValuationRing.TFAE A hF').out
      1 0).mp hV
  -- 1 → 3
  tfae_have 1 → 3
  | h => ⟨inferInstance, inferInstance,
    h.not_isField⟩
  -- 3 → 1
  tfae_have 3 → 1
  | ⟨hL, hP, hF⟩ => by
    haveI := hL; haveI := hP
    exact { not_a_field' :=
      isField_iff_maximalIdeal_eq.not.mp hF }
  -- 1 → 4
  tfae_have 1 → 4
  | h => by
    haveI := h
    refine ⟨inferInstance, inferInstance,
      inferInstance, ?_⟩
    have hF := h.not_isField
    have h_tfae :=
      IsDiscreteValuationRing.TFAE A hF
    have h03 : IsIntegrallyClosed A ∧
        ∃! P : Ideal A, P ≠ ⊥ ∧ P.IsPrime :=
      (h_tfae.out 0 3).mp h
    exact h03.2
  -- 4 → 1
  tfae_have 4 → 1
  | ⟨hIC, hN, hL, huniq⟩ => by
    haveI := hIC; haveI := hN; haveI := hL
    have ⟨P, ⟨hPbot, hPprime⟩, _⟩ := huniq
    have hF : ¬IsField A := fun hF =>
      hPbot (le_bot_iff.mp
        ((le_maximalIdeal hPprime.ne_top).trans
        (isField_iff_maximalIdeal_eq.mp hF).le))
    exact ((IsDiscreteValuationRing.TFAE A hF).out
      3 0).mp
      (show IsIntegrallyClosed A ∧
        ∃! P : Ideal A, P ≠ ⊥ ∧ P.IsPrime from
        ⟨hIC, huniq⟩)
  -- 1 → 5
  tfae_have 1 → 5
  | h => by
    haveI := h
    exact ⟨inferInstance, inferInstance,
      maximalIdeal A, maximalIdeal.isMaximal A,
      finrank_CotangentSpace_eq_one A⟩
  -- 5 → 1
  tfae_have 5 → 1
  | ⟨hN, hL, m, hmax, hfin⟩ => by
    haveI := hN; haveI := hL
    have hm : m = maximalIdeal A :=
      eq_maximalIdeal hmax
    subst hm
    exact finrank_CotangentSpace_eq_one_iff.mp
      hfin
  -- 1 → 6
  tfae_have 1 → 6
  | h => by
    haveI := h
    have hF := h.not_isField
    refine ⟨inferInstance, inferInstance,
      maximalIdeal A, maximalIdeal.isMaximal A,
      IsDiscreteValuationRing.not_a_field A, ?_⟩
    exact ((IsDiscreteValuationRing.TFAE A hF).out
      0 4).mp h
  -- 6 → 1
  tfae_have 6 → 1
  | ⟨hN, hL, m, hmax, hne, hprinc⟩ => by
    haveI := hN; haveI := hL
    have hm_eq : m = maximalIdeal A :=
      eq_maximalIdeal hmax
    subst hm_eq
    have hF : ¬IsField A :=
      isField_iff_maximalIdeal_eq.not.mpr hne
    exact ((IsDiscreteValuationRing.TFAE A hF).out
      4 0).mp hprinc
  -- 1 → 7
  tfae_have 1 → 7
  | h => by
    haveI := h
    have hF := h.not_isField
    refine ⟨inferInstance, inferInstance, hF, ?_⟩
    exact dvr_subalgebra_eq_bot_or_top
  -- 7 → 1
  tfae_have 7 → 1
  | ⟨hN, hL, hF, hmax⟩ => by
    haveI := hN; haveI := hL
    exact maximal_noetherian_local_is_dvr hF hmax
  tfae_finish
```

# Integrality
%%%
number := false
%%%

Integrality plays a key role in number theory, so it is worth discussing it in more detail.
