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

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.code.warnLineLength 90
open IsLocalRing

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

/-- Definition 1.10 (DVR). A discrete valuation ring
is an integral domain that is a local PID and not a
field. -/
recall IsDiscreteValuationRing (R : Type*)
    [CommRing R] [IsDomain R] : Prop

/-- Definition 1.10: The valuation ring: for every x
in Frac(A), either x ∈ A or x⁻¹ ∈ A. -/
recall ValuationRing (A : Type*)
    [CommRing A] [IsDomain A] : Prop
```

# Valuation ring structure
%%%
number := false
%%%

It is easy to verify that every valuation ring $`A` is a in fact a ring, and even an integral domain (if $`x` and $`y` are nonzero then $`v(xy) = v(x) + v(y) \neq \infty`, so $`xy \neq 0`), with $`k` as its fraction field. Notice that for any $`x \in k^{\times}` we have $`v(1/x) = v(1) - v(x) = -v(x)`, so at least one of $`x` and $`1/x` has nonnegative valuation and lies in $`A`. It follows that $`x \in A` is invertible (in $`A`) if and only if $`v(x) = 0`, hence the unit group of $`A` is

$$`A^{\times} = \{x \in k : v(x) = 0\},`

We can partition the nonzero elements of $`k` according to the sign of their valuation. Elements with valuation zero are units in $`A`, elements with positive valuation are non-units in $`A`, and elements with negative valuation do not lie in $`A`, but their multiplicative inverses are non-units in $`A`. This leads to a more general notion of a valuation ring.

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
theorem laurentSeries_valuation_ring
    (k : Type*) [Field k] :
    ValuationRing k⟦X⟧ :=
  inferInstance
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
- _$`A` is a regular noetherian local ring of dimension one._
- _$`A` is a noetherian local ring whose maximal ideal is nonzero and principal._
- _$`A` is a maximal noetherian ring of dimension one._

_Proof._ See \[1, §23\] or \[2, §9\]. $`\square`

```lean
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
        ¬IsField A ∧
        ∀ I : Ideal A, I ≠ ⊥ →
          ∃ (m : Ideal A) (n : ℕ),
            m.IsMaximal ∧ I = m ^ n,
      IsNoetherianRing A ∧ IsLocalRing A ∧
        ∃ m : Ideal A,
          m.IsMaximal ∧ m ≠ ⊥ ∧ m.IsPrincipal,
      IsDedekindDomain A ∧ IsLocalRing A ∧
        ¬IsField A
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
    have hF := h.not_isField
    refine ⟨inferInstance, inferInstance, hF, ?_⟩
    have h6 :=
      ((IsDiscreteValuationRing.TFAE A hF).out
        0 6).mp h
    intro I hI
    obtain ⟨n, hn⟩ := h6 I hI
    exact ⟨maximalIdeal A, n,
      maximalIdeal.isMaximal A, hn⟩
  -- 5 → 1
  tfae_have 5 → 1
  | ⟨hN, hL, hF, hall⟩ => by
    haveI := hN; haveI := hL
    have h6 : ∀ I : Ideal A, I ≠ ⊥ →
        ∃ n : ℕ, I = maximalIdeal A ^ n := by
      intro I hI
      obtain ⟨m, n, hm, hIn⟩ := hall I hI
      rw [eq_maximalIdeal hm] at hIn
      exact ⟨n, hIn⟩
    exact ((IsDiscreteValuationRing.TFAE A hF).out
      6 0).mp h6
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
    exact ⟨inferInstance, inferInstance,
      h.not_isField⟩
  -- 7 → 1
  tfae_have 7 → 1
  | ⟨hD, hL, hF⟩ => by
    haveI := hD; haveI := hL
    exact { not_a_field' :=
      isField_iff_maximalIdeal_eq.not.mp hF }
  tfae_finish
```

# Integrality
%%%
number := false
%%%

Integrality plays a key role in number theory, so it is worth discussing it in more detail.
