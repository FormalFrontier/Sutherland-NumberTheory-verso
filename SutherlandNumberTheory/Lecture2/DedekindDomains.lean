import VersoManual
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.code.warnLineLength 90

#doc (Manual) "Dedekind Domains" =>
%%%
tag := "dedekind-domains"
file := some "dedekind-domains"
number := false
%%%

Proposition 2.6 and Corollary 2.7 are powerful tools, because they allow us to work in local rings (rings with just one maximal ideal), which often simplifies matters considerably. For example, to prove that an ideal $`I` in an integral domain $`A` satisfies a certain property, it is enough to show that this property holds for all its localizations $`I_{\mathfrak{p}}` at prime ideals $`\mathfrak{p}` and is preserved under intersections. We now want to consider rings $`A` that satisfy some further assumptions that make its localizations even easier to work with.

# Proposition 2.9
%%%
number := false
%%%

_Proposition 2.9._ _Let $`A` be a noetherian domain. The following are equivalent:_

_(i) For every nonzero prime ideal $`\mathfrak{p} \subset A` the local ring $`A_{\mathfrak{p}}` is a DVR._

_(ii) The ring $`A` is integrally closed and $`\dim A \leq 1`._

_Proof._ If $`A` is a field then (i) and (ii) both hold, so let us assume that $`A` is not a field, and put $`K := \operatorname{Frac} A`. We first show that (i) implies (ii). Recall that $`\dim A` is the supremum of the length of all chains of prime ideals. It follows from Theorem 2.1 that every chain of prime ideals $`(0) \subsetneq \mathfrak{p}_1 \subsetneq \cdots \subsetneq \mathfrak{p}_n` extends to a corresponding chain in $`A_{\mathfrak{p}_n}` of the same length; conversely, every chain in $`A_{\mathfrak{p}}` contracts to a chain in $`A` of the same length. Thus

$$`\dim A = \sup\{\dim A_{\mathfrak{p}} : \mathfrak{p} \in \operatorname{Spec} A\} = 1,`

since every $`A_{\mathfrak{p}}` is either a DVR ($`\mathfrak{p} \neq (0)`), in which case $`\dim A_{\mathfrak{p}} = 1`, or a field ($`\mathfrak{p} = (0)`), in which case $`\dim A_{\mathfrak{p}} = 0`. Any $`x \in K` that is integral over $`A` is integral over every $`A_{\mathfrak{p}}` (since they all contain $`A`), and the $`A_{\mathfrak{p}}` are integrally closed, since they are DVRs or fields. So $`x \in \bigcap_{\mathfrak{p}} A_{\mathfrak{p}} = A`, and therefore $`A` is integrally closed, which shows (ii).

To show that (ii) implies (i), we first show that the following properties are all inherited by localizations of a ring: (1) no zero divisors, (2) noetherian, (3) dimension at most one, (4) integrally closed. (1) is obvious, (2) was noted in Remark 2.2, and (3) follows from Theorem 2.1 since, as argued above, we have $`\dim A_{\mathfrak{p}} \leq \dim A`. To show (4), suppose $`x \in K` is integral over $`A_{\mathfrak{p}}`. Then

$$`x^n + \frac{a_{n-1}}{s_{n-1}} x^{n-1} + \cdots + \frac{a_1}{s_1} x + \frac{a_0}{s_0} = 0`

for some $`a_0, \ldots, a_{n-1} \in A` and $`s_0, \ldots, s_{n-1} \in S := A - \mathfrak{p}`. Multiplying both sides by $`s^n`, where $`s = s_0 \cdots s_{n-1} \in S`, shows that $`sx` is integral over $`A`, hence an element of $`A`, since $`A` is integrally closed. But then $`sx/s = x` is an element of $`A_{\mathfrak{p}}`, so $`A_{\mathfrak{p}}` is integrally closed as claimed.

Thus (ii) implies that every $`A_{\mathfrak{p}}` is an integrally closed noetherian local domain of dimension at most 1, and for $`\mathfrak{p} \neq (0)` we must have $`\dim A_{\mathfrak{p}} = 1`. Thus for every nonzero prime ideal $`\mathfrak{p}`, the ring $`A_{\mathfrak{p}}` is an integrally closed noetherian local domain of dimension 1, and therefore a DVR, by Theorem 1.16. $`\square`

```lean
section Proposition_2_9

/-! ## Condition (i): The DVR characterization

Mathlib packages condition (i) as `IsDedekindDomainDvr`:
a noetherian domain
whose localizations at all nonzero prime ideals are
DVRs. -/

#check @IsDedekindDomainDvr
  -- (A : Type*) → [CommRing A] → [IsDomain A] → Prop

/-! The field `is_dvr_at_nonzero_prime` captures
condition (i) precisely. -/

#check @IsDedekindDomainDvr.is_dvr_at_nonzero_prime
  -- ∀ P ≠ ⊥, ∀ [P.IsPrime],
  --   IsDiscreteValuationRing
  --     (Localization.AtPrime P)

/-! ## Condition (ii): Integrally closed + dim ≤ 1

Mathlib packages condition (ii) as the conjunction of
three typeclasses inside
`IsDedekindDomain`
(= noetherian + integrally closed + dim ≤ 1). -/

#check @IsDedekindDomain
  -- recalled from 02_10_Definition

/-! ## The equivalence (i) ↔ (ii)

Mathlib establishes both directions as instances,
which is stronger than an `iff`:
any context that assumes `IsDedekindDomain`
automatically has `IsDedekindDomainDvr`
and vice versa. -/

/-! ### Direction (ii) → (i): Dedekind domain implies
DVR localizations -/

#check @IsDedekindDomain.isDedekindDomainDvr
  -- IsDedekindDomain A → IsDedekindDomainDvr A

/-! This direction uses that localizations of a
Dedekind domain at nonzero primes
are integrally closed noetherian local domains of
dimension 1, hence DVRs
(by Theorem 1.16 in the book). The key Mathlib
lemma: -/

#check
  @IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
  -- For a Dedekind domain, the localization at a
  -- nonzero prime is a DVR

/-! ### Direction (i) → (ii): DVR localizations imply
Dedekind domain -/

#check @IsDedekindDomainDvr.isDedekindDomain
  -- IsDedekindDomainDvr A → IsDedekindDomain A

/-! The proof of (i) → (ii) proceeds in two steps:

**Step 1: dim A ≤ 1.** Since each DVR has dimension 1
and fields have dimension 0,
and dim A = sup {dim A_𝔭}, we get dim A ≤ 1. -/

#check @IsDedekindDomainDvr.ring_dimensionLEOne
  -- IsDedekindDomainDvr A → Ring.DimensionLEOne A

/-! **Step 2: A is integrally closed.** Any
x ∈ Frac(A) integral over A is integral
over each A_𝔭. Since DVRs are integrally closed,
x ∈ A_𝔭 for all 𝔭, so
x ∈ ⋂_𝔭 A_𝔭 = A. -/

#check @IsDedekindDomainDvr.isIntegrallyClosed
  -- IsDedekindDomainDvr A → IsIntegrallyClosed A

/-! ## Demonstrating the equivalence

The two instances mean that `IsDedekindDomain A` and
`IsDedekindDomainDvr A` are
interchangeable: -/

variable {A : Type*} [CommRing A] [IsDomain A]

-- (ii) → (i): A Dedekind domain has DVR
-- localizations at nonzero primes
example [IsDedekindDomain A] :
    IsDedekindDomainDvr A := inferInstance

-- (i) → (ii): DVR localizations give a Dedekind
-- domain
example [IsDedekindDomainDvr A] :
    IsDedekindDomain A := inferInstance

-- (i) → dim ≤ 1
example [IsDedekindDomainDvr A] :
    Ring.DimensionLEOne A := inferInstance

-- (i) → integrally closed
example [IsDedekindDomainDvr A] :
    IsIntegrallyClosed A := inferInstance

-- (i) → noetherian (inherited from
-- IsDedekindDomainDvr's parent class)
example [IsDedekindDomainDvr A] :
    IsNoetherianRing A := inferInstance

end Proposition_2_9
```

# Definition 2.10
%%%
number := false
%%%

_Definition 2.10._ A noetherian domain satisfying either of the equivalent properties of Proposition 2.9 is called a _Dedekind domain_.

```lean
section DedekindDomain

/-! ### The definition

**Definition 2.10.** A Dedekind domain is a
noetherian, integrally closed domain
of Krull dimension ≤ 1. This is Mathlib's
`IsDedekindDomain`. -/

#check @IsDedekindDomain
  -- recall: (A : Type*) → [CommRing A] → Prop

/-! ### Component properties

The book defines a Dedekind domain as a noetherian
domain satisfying the equivalent
conditions of Proposition 2.9: (i) every localization
at a nonzero prime is a DVR, or
(ii) integrally closed with dim ≤ 1. Mathlib encodes
condition (ii) directly as three
typeclasses. -/

-- Cross-reference: DVR definition from Lecture 1
-- (Definition 1.10)
recall IsDiscreteValuationRing

-- A Dedekind domain is noetherian: every ideal is
-- finitely generated.
#check @IsNoetherianRing

-- Krull dimension ≤ 1: every nonzero prime ideal is
-- maximal.
#check @Ring.DimensionLEOne

-- A Dedekind domain is integrally closed in its
-- fraction field.
#check @IsIntegrallyClosed

/-! ### Instances: a Dedekind domain has all three
properties -/

variable {A : Type*} [CommRing A] [IsDomain A]
  [IsDedekindDomain A]

example : IsNoetherianRing A := inferInstance

example : Ring.DimensionLEOne A := inferInstance

example : IsIntegrallyClosed A := inferInstance

/-! ### Characterization theorem (Mathlib form)

The `iff` characterization shows the definition is
independent of the
choice of fraction field. This is the Mathlib form of
the equivalence
in Proposition 2.9 + Definition 2.10. -/

#check @isDedekindRing_iff

end DedekindDomain
```

# Corollary 2.11
%%%
number := false
%%%

_Corollary 2.11._ _Every PID is a Dedekind domain. In particular, $`\mathbb{Z}` is a Dedekind domain, as is $`k[x]` for any field $`k`._

```lean
section Corollary_2_11

/-! ## The main result: PID → Dedekind domain

Mathlib provides this as an instance (priority 100),
so any PID is automatically
a Dedekind domain. -/

#check @IsPrincipalIdealRing.isDedekindDomain
  -- ∀ {A : Type u_1} [inst : CommRing A]
  --   [inst_1 : IsDomain A]
  --   [inst_2 : IsPrincipalIdealRing A],
  --     IsDedekindDomain A

/-! The proof uses three facts:
- A PID is noetherian
  (`PrincipalIdealRing.isNoetherianRing`)
- A PID has dimension ≤ 1
  (`Ring.DimensionLEOne.principal_ideal_ring`)
- A PID (as a UFD) is integrally closed -/

#check @PrincipalIdealRing.isNoetherianRing
#check @Ring.DimensionLEOne.principal_ideal_ring

/-! The chain: Euclidean domain → PID → UFD →
integrally closed -/

#check @EuclideanDomain.to_principal_ideal_domain

/-! ## Example: ℤ is a Dedekind domain

ℤ is a Euclidean domain, hence a PID, hence a
Dedekind domain. -/

example : IsDedekindDomain ℤ := inferInstance

-- The intermediate steps are also available:
example : IsPrincipalIdealRing ℤ := inferInstance

/-! ## Example: k[x] is a Dedekind domain for any
field k

Polynomial rings over fields are Euclidean domains,
hence PIDs,
hence Dedekind domains. -/

open Polynomial in
variable (k : Type*) [Field k] in
example : IsDedekindDomain k[X] := inferInstance

open Polynomial in
variable (k : Type*) [Field k] in
-- The intermediate step:
example : IsPrincipalIdealRing k[X] := inferInstance

end Corollary_2_11
```

# Remark 2.12
%%%
number := false
%%%

_Remark 2.12._ Every PID is both a UFD and a Dedekind domain. Not every UFD is a Dedekind domain (consider $`k[x, y]`, for any field $`k`), and not every Dedekind domain is a UFD (consider $`\mathbb{Z}[\sqrt{-13}]`, in which $`(1 + \sqrt{-13})(1 - \sqrt{-13}) = 2 \cdot 7 = 14`). However (as we shall see), every ring that is both a UFD and a Dedekind domain is a PID.

```lean
section Remark_2_12

/-! ## Claim 1: Every PID is a UFD

This is a standard result in commutative algebra.
Mathlib proves it via
the fact that a PID is a noetherian ring satisfying
the ascending chain condition
on principal ideals, plus every irreducible is prime.
-/

variable {R : Type*} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R]

-- A PID is a UFD (via the instance chain:
-- PID → noetherian + irreducible_iff_prime → UFD)
example : UniqueFactorizationMonoid R :=
  inferInstance

/-! ## Claim 2: Every PID is a Dedekind domain

This is Corollary 2.11, recalled here. -/

example : IsDedekindDomain R := inferInstance

/-! ## Claim 3: Not every UFD is a Dedekind domain

The book's counterexample is k[x, y] for any field k.
This is a UFD
(since k[x] is a UFD and R[y] is a UFD when R is),
but it has Krull
dimension 2, so it cannot be a Dedekind domain. -/

variable (k : Type*) [Field k]

-- k[x,y] ≅ (k[x])[y] is a UFD: polynomial ring
-- over a UFD is a UFD
example :
    UniqueFactorizationMonoid
      (Polynomial (Polynomial k)) := inferInstance

-- k[x,y] is NOT a Dedekind domain: (Y) is a nonzero
-- prime that's not maximal
-- IsDedekindDomain instance synthesis on
-- Polynomial (Polynomial k) is expensive
set_option maxHeartbeats 400000 in
theorem not_isDedekindDomain_polynomial_polynomial :
    ¬ IsDedekindDomain
      (Polynomial (Polynomial k)) := by
  intro h
  -- If (Y) is maximal then k[x] ≅ k[x,y]/(Y) is a
  -- field, contradiction
  haveI := h
  have hprime :
      (Ideal.span
        {(Polynomial.X :
          Polynomial (Polynomial k))}).IsPrime :=
    (Ideal.span_singleton_prime
      Polynomial.X_ne_zero).mpr Polynomial.prime_X
  have hmax := hprime.isMaximal
    (mt Ideal.span_singleton_eq_bot.mp
      Polynomial.X_ne_zero)
  have hfield :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient
      _).mp hmax
  rw [show (Polynomial.X :
      Polynomial (Polynomial k)) =
      Polynomial.X - Polynomial.C 0 from by simp]
    at hfield
  exact Polynomial.not_isField k
    ((Polynomial.quotientSpanXSubCAlgEquiv
      (0 : Polynomial k)).symm.toMulEquiv.isField
      hfield)

/-! ## Claim 4: Not every Dedekind domain is a UFD

The book's counterexample is ℤ[√-13]. This is a
Dedekind domain
(it is the ring of integers of ℚ(√-13), a number
field) but not a UFD
(since 14 = 2 · 7 = (1 + √-13)(1 - √-13) gives two
distinct factorizations). -/

-- ℤ[√d] for d : ℤ is available in Mathlib as
-- `Zsqrtd d`
#check Zsqrtd

-- ℤ[√-13] is not a UFD: 2 is irreducible but not
-- prime
theorem not_uniqueFactorizationMonoid_Zsqrtd_neg13 :
    ¬ UniqueFactorizationMonoid
      (Zsqrtd (-13)) := by
  intro h
  -- We show 2 is irreducible but not prime in
  -- ℤ[√-13]
  have hd : (-13 : ℤ) ≤ 0 := by norm_num
  have hirr : Irreducible (2 : ℤ√(-13)) := by
    refine ⟨?_, ?_⟩
    · rw [← Zsqrtd.norm_eq_one_iff' hd]; decide
    · -- If 2 = a * b, one of a, b must be a unit
      intro a b hab
      have hn : a.norm * b.norm = 4 := by
        have := congr_arg Zsqrtd.norm hab
        rw [Zsqrtd.norm_mul,
          show (2 : ℤ√(-13)).norm = 4
            from by decide] at this
        linarith
      have hna := Zsqrtd.norm_nonneg hd a
      have hnb := Zsqrtd.norm_nonneg hd b
      rw [← Zsqrtd.norm_eq_one_iff' hd,
        ← Zsqrtd.norm_eq_one_iff' hd]
      -- norm(x) = re² + 13·im² ≥ 13 if im ≠ 0,
      -- so any norm ≤ 4 requires im = 0
      -- Then re² ∈ {0,1,4,...}, so
      -- norm ∈ {0,1,4,...}. Can't be 2 or 3.
      suffices ∀ x : ℤ√(-13),
          x.norm ≠ 2 ∧ x.norm ≠ 3 by
        have ⟨h2a, h3a⟩ := this a
        have hb_pos : 0 < b.norm := by
          rcases eq_or_lt_of_le hnb with h | h
          · exfalso
            rw [← h, mul_zero] at hn; omega
          · exact h
        have ha_pos : 0 < a.norm := by
          rcases eq_or_lt_of_le hna with h | h
          · exfalso
            rw [← h, zero_mul] at hn; omega
          · exact h
        have : a.norm = 1 ∨ a.norm = 4 := by
          have : a.norm ≤ 4 := by
            have : 1 ≤ b.norm := by omega
            nlinarith
          omega
        rcases this with ha | ha
        · left; exact ha
        · right; nlinarith
      intro x
      constructor <;> intro heq <;>
          rw [Zsqrtd.norm_def] at heq <;> {
        have him0 : x.im = 0 := by
          by_contra h0
          have : x.im ≤ -1 ∨ x.im ≥ 1 := by
            omega
          rcases this with hh | hh <;>
            nlinarith [mul_self_nonneg x.re]
        simp [him0] at heq
        have hle : x.re ≤ 1 := by
          nlinarith [mul_self_nonneg (x.re - 2)]
        have hge : -1 ≤ x.re := by
          nlinarith [mul_self_nonneg (x.re + 2)]
        interval_cases x.re <;> omega
      }
  have hprime : ¬ Prime (2 : ℤ√(-13)) := by
    intro ⟨_, _, hdvd⟩
    -- 2 | (1+√-13)(1-√-13) = 14, but
    -- 2 ∤ (1+√-13) and 2 ∤ (1-√-13)
    have h14 :
        (2 : ℤ√(-13)) ∣
          (⟨1, 1⟩ : ℤ√(-13)) * ⟨1, -1⟩ :=
      ⟨⟨7, 0⟩, by ext <;> decide⟩
    rcases hdvd _ _ h14 with
        ⟨⟨c, d⟩, hcd⟩ | ⟨⟨c, d⟩, hcd⟩ <;>
      simp [Zsqrtd.ext_iff] at hcd <;> omega
  haveI := h
  exact hprime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      hirr)

/-! ## Claim 5: Dedekind + UFD → PID

This is the converse direction, completing the
picture:
  PID = Dedekind ∩ UFD

Mathlib has this as a theorem (not an instance, to
avoid timeouts). -/

#check
  @IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid
  -- Dedekind domain + UFD → PID

-- Demonstrate the theorem:
example (S : Type*) [CommRing S]
    [IsDedekindDomain S]
    [UniqueFactorizationMonoid S] :
    IsPrincipalIdealRing S :=
  IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid
    S

/-! ## Summary of class relationships

The remark establishes:
- PID ⊆ UFD (strict: ℤ[√-13] is Dedekind, not UFD,
  so Dedekind ⊄ UFD ⊄ PID would need more)
- PID ⊆ Dedekind (strict: k[x,y] is UFD, not
  Dedekind)
- PID = UFD ∩ Dedekind
- UFD and Dedekind are incomparable classes -/

end Remark_2_12
```

One of our first goals in this course is to prove that the ring of integers of number fields and coordinate rings of global function fields are Dedekind domains. More precisely, we will prove that if $`A` is a Dedekind domain and $`L` is a finite separable extension of its fraction field, then the integral closure of $`A` in $`L` is a Dedekind domain. This includes the two main cases of interest to us, in which either $`A = \mathbb{Z}` and $`L` is a number field, or $`A = \mathbb{F}_q[t]` and $`L` is a global function field. Recall from Lecture 1 that number fields and global function fields are the two types of _global fields_ (as we will prove in later lectures).

```lean
section Discussion_02_12a

/-! ## Main claim: integral closure of Dedekind
domain is Dedekind

If A is a Dedekind domain with fraction field K, and
L/K is a finite separable
extension, then the integral closure of A in L is a
Dedekind domain. -/

#check @IsIntegralClosure.isDedekindDomain
  -- (A : Type) (K : Type) ... (L : Type) ...
  -- (C : Type) ...
  -- [IsDedekindDomain A]
  -- [FiniteDimensional K L]
  -- [Algebra.IsSeparable K L]
  -- [IsIntegralClosure C A L] →
  --   IsDedekindDomain C

/-! The integral closure itself is a Mathlib
construction: -/

#check @integralClosure
  -- (R : Type) (A : Type) → [CommRing R] →
  -- [CommRing A] → [Algebra R A] → Subalgebra R A

/-! ## Examples: ℤ and k[X] are Dedekind domains

These are already established in
`02_11_Corollary.lean` via the PID → Dedekind
instance chain. We recall them here as the two base
cases for the integral
closure theorem above. -/

example : IsDedekindDomain ℤ := inferInstance

open Polynomial in
variable (k : Type*) [Field k] in
example : IsDedekindDomain k[X] := inferInstance

end Discussion_02_12a
```
