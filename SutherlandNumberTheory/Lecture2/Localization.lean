import VersoManual
import Mathlib.Tactic.Recall
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Ideal.NatInt

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.code.warnLineLength 90

#doc (Manual) "Localization" =>
%%%
tag := "localization"
file := some "localization"
number := false
%%%

Let $`A` be a commutative ring (unital, as always), and let $`S` be a multiplicative subset of $`A`; this means $`S` is closed under finite products (including the empty product, so $`1 \in S`), and $`S` does not contain zero. The _localization_ of $`A` with respect to $`S` is a ring $`S^{-1}A` equipped with a ring homomorphism $`\iota\colon A \to S^{-1}A` that maps $`S` into $`(S^{-1}A)^\times` and satisfies the following universal property: if $`\varphi\colon A \to B` is a ring homomorphism with $`\varphi(S) \subseteq B^\times` then there is a unique ring homomorphism $`S^{-1}A \to B` that makes the following diagram commute:

$$`A \xrightarrow{\varphi} B`

$$`\downarrow^{\iota} \nearrow_{\exists!}`

$$`S^{-1}A`

and one says that $`\varphi` factors uniquely through $`S^{-1}A` (via $`\iota`). As usual with universal properties, this guarantees that $`S^{-1}A` is unique (hence well-defined), provided that it exists. To prove existence we construct $`S^{-1}A` as the quotient of $`A \times S` modulo the equivalence relation

$$`(a, s) \sim (b, t) \Leftrightarrow \exists u \in S \text{ such that } u(ta - sb) = 0. \tag{1}`

We then use $`a/s` to denote the equivalence class of $`(a, s)` and define $`\iota(a) := a/1`; one can easily verify that $`S^{-1}A` is a ring with additive identity $`0/1` and multiplicative identity $`1/1`, and that $`\iota : A \to S^{-1}A` is a ring homomorphism. If $`s` is invertible in $`A` we can view $`a/s` either as the element $`as^{-1}` of $`A` or the equivalence class of $`(a, s)` in $`S^{-1}A`; we have $`(a, s) \sim (as^{-1}, 1)`, since $`(a \cdot 1 - as^{-1} \cdot s) \cdot 1 = 0`, so this notation should not cause any confusion. For $`s \in S` we have $`\iota(s)^{-1} = 1/s`, since $`(s/1)(1/s) = s/s = 1/1 = 1`, thus $`\iota(S) \subseteq (S^{-1}A)^\times`.

If $`\varphi\colon A \to B` is a ring homomorphism with $`\varphi(S) \subseteq B^\times`, then $`\varphi = \pi \circ \iota`, where $`\pi` is defined by $`\pi(a/s) := \varphi(a)\varphi(s)^{-1}`. If $`\pi\colon S^{-1}A \to B` is any ring homomorphism that satisfies $`\varphi = \pi \circ \iota`, then $`\varphi(a)\varphi(s)^{-1} = \pi(\iota(a))\pi(\iota(s))^{-1} = \pi(\iota(a)\iota(s)^{-1}) = \pi((a/1)(1/s)) = \pi(a/s)`, so $`\pi` is unique.

In the case of interest to us, $`A` is actually an integral domain, in which case $`(a, s) \sim (b, t)` if and only if $`at - bs = 0` (we can always take $`u = 1` in the equivalence relation (1) above), and we can then identify $`S^{-1}A` with a subring of the fraction field of $`A` (which we note is the localization of $`A` with respect to $`S = A_{\neq 0}`), and if $`T` is a multiplicative subset of $`A` that contains $`S`, then $`S^{-1}A \subseteq T^{-1}A`.

When $`A` is an integral domain the map $`\iota\colon A \to S^{-1}A` is injective, allowing us to identify $`A` with its image $`\iota(A) \subseteq S^{-1}A` (in general, $`\iota` is injective if and only if $`S` contains no zero divisors). When $`A` is an integral domain we may thus view $`S^{-1}A` as an intermediate ring that lies between $`A` and its fraction field: $`A \subseteq S^{-1}A \subseteq \operatorname{Frac} A`.

```lean
section Localization_2_1

/-! ## Claim 1: Universal property of localization

If g : R →+* P maps M to units, there is a ring
homomorphism S →+* P extending g through the
localization map. -/

-- Universal property: lift a map that sends M to
-- units
recall IsLocalization.lift

/-! ## Claim 2: Equivalence relation construction

Elements of the localization are represented as
fractions a/s, with
(a, s) ~ (b, t) ⟺ ∃ c ∈ M,
  c * (t * a) = c * (s * b). -/

-- The `mk'` constructor produces the equivalence
-- class a/s
recall IsLocalization.mk'

-- The equivalence relation on mk' elements
recall IsLocalization.eq

/-! ## Claim 3: ι(S) ⊆ (S⁻¹A)×

The localization map sends every element of M to
a unit in S. -/

recall IsLocalization.map_units

/-! ## Claim 4: Uniqueness of the factoring map

Any ring homomorphism S →+* P that agrees with g
on the image of R must equal the lift. -/

recall IsLocalization.lift_unique

/-! ## Claim 5: Simplified equivalence for integral
domains

When R is a domain, the equivalence relation
simplifies: (a,s) ~ (b,t) iff at − bs = 0 (the
existential witness u can always be taken as 1).

In Mathlib, `IsLocalization.mk'_eq_iff_eq` combined
with domain cancellation gives this directly. -/

recall IsLocalization.mk'_eq_iff_eq

/-! ## Claim 6: S⁻¹A embeds in Frac(A)

The fraction field Frac(A) is the localization at
the nonzero divisors. For a domain, S⁻¹A naturally
embeds in Frac(A). -/

recall IsFractionRing

recall FractionRing

/-! ## Claim 7: S ⊆ T implies S⁻¹A ⊆ T⁻¹A

When M ≤ N as submonoids, S (a localization at M)
is also a localization at N, provided every element
of N maps to a unit. -/

recall IsLocalization.of_le

/-! ## Claim 8: ι is injective when A is a domain

When M consists of non-zero-divisors (in particular
when A is a domain and 0 ∉ S), the localization map
is injective. -/

recall IsLocalization.injective

/-! ## Claim 9: A ⊆ S⁻¹A ⊆ Frac(A)

For a domain, the chain of embeddings
A ↪ S⁻¹A ↪ Frac(A).
The first embedding is ι (algebraMap), injective by
Claim 8. The second is the lift of the fraction
field map. -/

recall IsFractionRing.injective

end Localization_2_1
```

If $`\varphi\colon A \to B` is a ring homomorphism and $`\mathfrak{b}` is a $`B`-ideal, then $`\varphi^{-1}(\mathfrak{b})` is an $`A`-ideal called the _contraction_ of $`\mathfrak{b}` to $`A` and sometimes denoted $`\mathfrak{b}^c`; when $`A` is a subring of $`B` and $`\varphi` is the inclusion map we simply have $`\mathfrak{b}^c = \mathfrak{b} \cap A`. If $`\mathfrak{a}` is an $`A`-ideal, in general $`\varphi(\mathfrak{a})` is not a $`B`-ideal; but we can instead consider the $`B`-ideal generated by $`\varphi(\mathfrak{a})`, the _extension_ of $`\mathfrak{a}` to $`B`, sometimes denoted $`\mathfrak{a}^e`.

In the case of interest to us, $`A` is an integral domain, $`B = S^{-1}A` is the localization of $`A` with respect to some multiplicative set $`S`, and $`\varphi = \iota` is injective, so we view $`A` as a subring of $`B`. We then have

$$`\mathfrak{a}^e = \mathfrak{a}B := (ab : a \in \mathfrak{a}, b \in B). \tag{2}`

We clearly have $`\mathfrak{a} \subseteq \varphi^{-1}(\varphi(\mathfrak{a})B) = \mathfrak{a}^{ec}` and $`\mathfrak{b}^{ce} = \varphi(\varphi^{-1}(\mathfrak{b}))B \subseteq \mathfrak{b}`; one might ask whether these inclusions are equalities. In general the first is not: if $`B = S^{-1}A` and $`\mathfrak{a} \cap S \neq \emptyset` then $`\mathfrak{a}^e = \mathfrak{a}B = B` and $`\mathfrak{a}^{ec} = B \cap A` are both unit ideals, but we may still have $`\mathfrak{a} \subsetneq A`. However when $`B = S^{-1}A` the second inclusion is an equality; see \[1, Prop. 11.19\] or \[2, Prop. 3.11\] for a short proof. We also note the following theorem.

```lean
section Ideals_in_Localizations_2_2

/-! ## Claim 1: Contraction φ⁻¹(𝔟) is an A-ideal

For any ring homomorphism φ : R → S and ideal 𝔟 of
S, the preimage φ⁻¹(𝔟) is an ideal of R. Mathlib
calls this `Ideal.comap`. -/

recall Ideal.comap

/-! ## Claim 2: Extension 𝔞B = ideal generated by
φ(𝔞)

For a ring homomorphism φ : R → S and ideal 𝔞 of R,
the extension 𝔞ᵉ is the ideal of S generated by
φ(𝔞). Mathlib calls this `Ideal.map`. -/

recall Ideal.map

/-! ## Claim 3: 𝔞 ⊆ 𝔞ᵉᶜ

Every element of 𝔞 is in the contraction of its
extension. This holds for arbitrary ring
homomorphisms, not just localizations. -/

recall Ideal.le_comap_map

/-! ## Claim 4: 𝔟ᶜᵉ ⊆ 𝔟

The extension of the contraction is contained in the
original. This also holds for arbitrary ring
homomorphisms. -/

recall Ideal.map_comap_le

/-! ## Claim 5: 𝔞ᵉ = S when 𝔞 ∩ S ≠ ∅

If an ideal 𝔞 of R contains an element of the
multiplicative set M (i.e., 𝔞 ∩ M ≠ ∅), then its
extension to the localization is the entire ring.
Equivalently, 𝔞ᵉ ≠ ⊤ iff 𝔞 and M are disjoint. -/

recall
  IsLocalization.map_algebraMap_ne_top_iff_disjoint

-- Contrapositive: if 𝔞 meets M, then 𝔞ᵉ = ⊤
variable {R S : Type*} [CommRing R] [CommRing S]
  [Algebra R S]
variable {M : Submonoid R} [IsLocalization M S]

theorem ideal_ext_eq_top_of_meets_submonoid
    (I : Ideal R)
    (h : ¬Disjoint (M : Set R) (I : Set R)) :
    Ideal.map (algebraMap R S) I = ⊤ :=
  of_not_not
    ((IsLocalization.map_algebraMap_ne_top_iff_disjoint
      M S I).not.mpr h)

/-! ## Claim 6: 𝔟ᶜᵉ = 𝔟 when B = S⁻¹A

For localizations (unlike general ring
homomorphisms), extending the contraction always
recovers the original ideal. This is the key
property that makes contraction/extension a
well-behaved correspondence for localizations. -/

recall IsLocalization.map_comap

end Ideals_in_Localizations_2_2
```

# Theorem 2.1
%%%
number := false
%%%

_Theorem 2.1._ _Let $`S` be a multiplicative subset of an integral domain $`A`. There is a one-to-one correspondence between the prime ideals of $`S^{-1}A` and the prime ideals of $`A` that do not intersect $`S` given by the inverse maps $`\mathfrak{q} \mapsto \mathfrak{q} \cap A` and $`\mathfrak{p} \mapsto \mathfrak{p}S^{-1}A`._

_Proof._ See \[1, Cor. 11.20\] or \[2, Prop. 3.11.iv\]. $`\square`

```lean
-- **Theorem 2.1** (Prime ideal correspondence).
-- Order isomorphism between primes of S⁻¹A and
-- primes of A disjoint from S.
-- The book states this as a bijection; Mathlib's
-- version is stronger (order-preserving).
recall IsLocalization.orderIsoOfPrime

-- The inverse map of the correspondence:
-- extension p ↦ pS⁻¹A.
-- Given a prime ideal of R disjoint from M, its
-- image under `Ideal.map` is prime in S.
recall IsLocalization.isPrime_of_isPrime_disjoint

-- Contraction then extension is the identity on
-- ideals of S⁻¹A:
-- map (comap q) = q for any ideal q of S.
recall IsLocalization.map_comap

-- Extension then contraction is the identity on
-- primes of A disjoint from S:
-- comap (map p) = p for any prime p disjoint
-- from M.
recall IsLocalization.comap_map_of_isPrime_disjoint
```

# Remark 2.2
%%%
number := false
%%%

_Remark 2.2._ An immediate consequence of (2) is that if $`a_1, \ldots, a_n \in A` generate $`\mathfrak{a}` as an $`A`-ideal, then they also generate $`\mathfrak{a}^e = \mathfrak{a}B` as a $`B`-ideal. As noted above, when $`B = S^{-1}A` we have $`\mathfrak{b} = \mathfrak{b}^{ce}`, so every $`B`-ideal is of the form $`\mathfrak{a}^e` (take $`\mathfrak{a} = \mathfrak{b}^c`). It follows that if $`A` is noetherian then so are all its localizations, and if $`A` is a PID then so are all of its localizations.

```lean
section Remark_2_2

/-! ### Claim 1: Generators of 𝔞 generate 𝔞ᵉ

If {a₁, …, aₙ} generate 𝔞 as an A-ideal, then
their images under algebraMap generate
𝔞ᵉ = Ideal.map (algebraMap R S) 𝔞 as an S-ideal.

This follows from `Ideal.map_span`: the extension
of Ideal.span s is Ideal.span (f '' s). -/

-- Extension of span equals span of image
recall Ideal.map_span

/-! ### Claim 2: Every B-ideal is of the form 𝔞ᵉ

When B = S⁻¹A, we have 𝔟 = 𝔟^{ce} for every B-ideal
𝔟. So every B-ideal is an extension: take
𝔞 = 𝔟^c = comap (algebraMap R S) 𝔟. -/

-- b = b^{ce}: map (comap J) = J for any ideal J
-- of the localization
recall IsLocalization.map_comap

/-! ### Claim 3: A noetherian ⟹ all localizations
noetherian

This is a standard Mathlib result. -/

-- Localization of a noetherian ring is noetherian
recall IsLocalization.isNoetherianRing

-- The instance for the concrete `Localization` type:
example (R : Type*) [CommRing R]
    [IsNoetherianRing R] (S : Submonoid R) :
    IsNoetherianRing (Localization S) :=
  inferInstance

/-! ### Claim 4: A PID ⟹ all localizations PID

Every ideal of S⁻¹A is of the form 𝔞ᵉ (Claim 2).
If A is a PID, then 𝔞 = (a) for some a, so
𝔞ᵉ = (a/1). Hence S⁻¹A is a PID.

For localization at a prime, Mathlib gives this via:
PID → Dedekind domain → localization at prime is
PID. -/

-- PID → Dedekind domain (standard Mathlib instance)
recall IsPrincipalIdealRing.isDedekindDomain

-- Dedekind domain localized at prime → PID
recall
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime

-- General localization of a PID is a PID
-- (The book's argument: every ideal of S⁻¹A equals
-- 𝔞ᵉ for some A-ideal 𝔞; since A is a PID, 𝔞 = (a),
-- so 𝔞ᵉ = (a/1) is principal.)
theorem
    isPrincipalIdealRing_localization_of_isPrincipalIdealRing
    (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (M : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization M S] :
    IsPrincipalIdealRing S where
  principal J := by
    rw [← IsLocalization.map_comap M S J]
    obtain ⟨⟨a, ha⟩⟩ :=
      IsPrincipalIdealRing.principal
        (J.comap (algebraMap R S))
    exact ha ▸ ⟨⟨algebraMap R S a,
      by simp [Ideal.map_span,
        Set.image_singleton]⟩⟩

end Remark_2_2
```

An important special case of localization occurs when $`\mathfrak{p}` is a prime ideal in an integral domain $`A`, and $`S = A - \mathfrak{p}` (the complement of the set $`\mathfrak{p}` in the set $`A`). In this case it is customary to denote $`S^{-1}A` by

$$`A_{\mathfrak{p}} := \{a/b : a \in A, b \notin \mathfrak{p}\} / \sim, \tag{3}`

and call it the _localization of $`A` at $`\mathfrak{p}`_. The prime ideals of $`A_{\mathfrak{p}}` are then in bijection with the prime ideals of $`A` that are contained in $`\mathfrak{p}`. It follows that $`\mathfrak{p}A_{\mathfrak{p}}` is the unique maximal ideal of $`A_{\mathfrak{p}}` and $`A_{\mathfrak{p}}` is therefore a local ring (whence the term _localization_).

```lean
section Discussion_02_02a

variable {A : Type*} [CommRing A] [IsDomain A]
  (𝔭 : Ideal A) [𝔭.IsPrime]

/-! ### Claim 1: A_𝔭 = S⁻¹A for S = A \ 𝔭

The localization of A at 𝔭 is S⁻¹A where
S = 𝔭.primeCompl. Mathlib defines this as
`Localization.AtPrime`. -/

-- The type A_𝔭 = S⁻¹A for S = A \ 𝔭
recall Localization.AtPrime

-- The typeclass characterizing when S is a
-- localization at a prime
recall IsLocalization.AtPrime

/-! ### Claim 2: Prime ideals of A_𝔭 biject with
primes of A contained in 𝔭

There is an order isomorphism between prime ideals
of the localization S⁻¹A and prime ideals of A that
are disjoint from S (equivalently, contained in
𝔭). -/

-- General prime ideal correspondence for
-- localizations
recall IsLocalization.orderIsoOfPrime

-- Specialized version for localization at a prime:
-- primes of A_𝔭 ↔ primes of A contained in 𝔭
recall IsLocalization.AtPrime.orderIsoOfPrime

/-! ### Claim 3: 𝔭A_𝔭 is the unique maximal ideal
of A_𝔭

Since A_𝔭 is a local ring (Claim 4), it has a unique
maximal ideal. That ideal equals the extension of 𝔭
to A_𝔭. -/

-- The unique maximal ideal of a local ring
recall IsLocalRing.maximalIdeal

-- The maximal ideal of A_𝔭 equals the map of 𝔭
recall IsLocalization.AtPrime.map_eq_maximalIdeal

/-! ### Claim 4: A_𝔭 is a local ring

The localization at a prime ideal is always a local
ring. -/

-- A_𝔭 is a local ring (standard Mathlib instance)
example :
    IsLocalRing (Localization.AtPrime 𝔭) :=
  inferInstance

end Discussion_02_02a
```

# Warning 2.3
%%%
number := false
%%%

_Warning 2.3._ The notation in (3) makes it tempting to assume that if $`a/b` is an element of $`\operatorname{Frac} A`, then $`a/b \in A_{\mathfrak{p}}` if and only if $`b \notin \mathfrak{p}`. This is not necessarily true! As an element of $`\operatorname{Frac} A`, the notation "$`a/b`" represents an equivalence class; thus even if $`b \in \mathfrak{p}`, if $`a/b = a'/b'` with $`b' \notin \mathfrak{p}`, then $`a/b \in A_{\mathfrak{p}}`. As a trivial example, take $`A = \mathbb{Z}`, $`\mathfrak{p} = (3)`, $`a/b = 9/3` and $`a'/b' = 3/1`. You may object that we should write $`a/b` in lowest terms, but when $`A` is not a unique factorization domain it is not clear what this means.

```lean
section Warning_2_3

/-! ### The prime ideal (3) in ℤ -/

/-- The prime ideal 𝔭 = (3) in ℤ. -/
noncomputable abbrev primeIdeal3 : Ideal ℤ :=
  Ideal.span {3}

instance primeIdeal3_isPrime :
    primeIdeal3.IsPrime := by
  rw [Ideal.span_singleton_prime
    (by norm_num : (3 : ℤ) ≠ 0)]
  exact Int.prime_iff_natAbs_prime.mpr (by decide)

/-! ### The counterexample: 9/3 = 3/1 in ℚ

The point is that 3 ∈ (3), so naively 9/3
"shouldn't" be in ℤ_(3). But 9/3 = 3/1, and
1 ∉ (3), so it IS in ℤ_(3). -/

/-- 3 is in the ideal (3). -/
theorem three_mem_primeIdeal3 :
    (3 : ℤ) ∈ primeIdeal3 :=
  Ideal.mem_span_singleton_self 3

/-- 9/3 = 3/1 as rational numbers. This is the
equivalence that shows the "denominator" 3 ∈ (3) is
misleading. -/
theorem nine_div_three_eq_three :
    (9 : ℚ) / 3 = 3 := by norm_num

/-- The real content of Warning 2.3: the integer 3
maps to an element of ℤ_(3), and 9 = 3 * 3, so the
"fraction" 9/3 is really just 3/1 in ℤ_(3). This
shows that membership in A_𝔭 does not depend on a
particular representation a/b — even if b ∈ 𝔭, the
element may still be in A_𝔭 via a different
representation. -/
theorem warning_2_3_nine_eq_three_times_three :
    algebraMap ℤ
      (Localization.AtPrime primeIdeal3) 9 =
      algebraMap ℤ
        (Localization.AtPrime primeIdeal3) 3 *
        algebraMap ℤ
          (Localization.AtPrime primeIdeal3) 3 := by
  rw [show (9 : ℤ) = 3 * 3 from by norm_num,
    map_mul]

/-- Warning 2.3 punchline: there exist a, b ∈ ℤ
with b ∈ (3) and a/b = 3 in ℚ, yet a/b ∈ ℤ_(3)
(because a/b = 3/1 and 1 ∉ (3)).

Concretely: a = 9, b = 3, so b ∈ (3), and 9/3 = 3
in ℚ. The element 3 is in the image of ℤ → ℤ_(3),
hence in ℤ_(3). -/
theorem warning_2_3_counterexample :
    ∃ (a b : ℤ), b ∈ primeIdeal3 ∧
      (a : ℚ) / b = 3 ∧
      (algebraMap ℤ
        (Localization.AtPrime primeIdeal3) a =
        algebraMap ℤ
          (Localization.AtPrime primeIdeal3) b *
          algebraMap ℤ
            (Localization.AtPrime primeIdeal3) 3) :=
  ⟨9, 3, three_mem_primeIdeal3, by norm_num,
    warning_2_3_nine_eq_three_times_three⟩

end Warning_2_3
```
