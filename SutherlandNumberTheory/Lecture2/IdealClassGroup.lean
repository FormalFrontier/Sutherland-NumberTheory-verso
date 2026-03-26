import VersoManual
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.code.warnLineLength 90

#doc (Manual) "Invertible Fractional Ideals and the Ideal Class Group" =>
%%%
tag := "ideal-class-group"
file := some "ideal-class-group"
number := false
%%%

In this section $`A` is a noetherian domain (not necessarily a Dedekind domain) and $`K` is its fraction field. Recall that a fractional ideal of $`A` is a finitely generated $`A`-submodule of $`K`, and if $`I` and $`J` are fractional ideals, so is the ideal quotient

$$`I \div J := \{x \in K : xJ \subseteq I\},`

and we say that a fractional ideal $`I` is invertible if $`IJ = A` for some fractional ideal $`J`. The definition of $`A \div I` implies $`I(A \div I) \subseteq A`, and Lemma 2.20 implies that $`I` is invertible precisely when this inclusion is an equality, in which case the inverse of $`I` is $`A \div I`.

Ideal multiplication is commutative and associative, thus the set of nonzero fractional ideals of a noetherian domain form an abelian monoid under multiplication with $`A = (1)` as the identity. It follows that the subset of invertible fractional ideals is an abelian group.

# Definition 2.22
%%%
number := false
%%%

_Definition 2.22._ The _ideal group_ $`\mathcal{I}_A` of a noetherian domain $`A` is the group of invertible fractional ideals. Note that, despite the name, elements of $`\mathcal{I}_A` need not be ideals.

```lean
section IdealGroup

variable {A : Type*} [CommRing A] [IsDomain A]
  [IsNoetherianRing A]
variable {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]

/-! ### The definition

**Definition 2.22.** The ideal group ℐ_A is the
group of invertible fractional ideals. In Mathlib
this is the unit group of `FractionalIdeal`. -/

-- ℐ_A = (FractionalIdeal A⁰ K)ˣ — the group of
-- invertible fractional ideals
#check (FractionalIdeal (nonZeroDivisors A) K)ˣ

/-! ### Group structure

The ideal group is an abelian group under
fractional ideal multiplication. -/

-- ℐ_A is a commutative group
example :
    CommGroup
      (FractionalIdeal (nonZeroDivisors A) K)ˣ :=
  inferInstance

-- The group operation is fractional ideal
-- multiplication
#check @Units.val_mul
  (FractionalIdeal (nonZeroDivisors A) K) _

-- The identity element is A itself (as a fractional
-- ideal)
#check @Units.val_one
  (FractionalIdeal (nonZeroDivisors A) K) _

-- The inverse of I ∈ ℐ_A satisfies I * I⁻¹ = 1
#check @Units.mul_inv
  (FractionalIdeal (nonZeroDivisors A) K) _

/-! ### Elements need not be ideals

The book notes that elements of ℐ_A need not be
ideals (i.e., they need not be contained in A).
This is because fractional ideals can contain
elements of K outside A. For example, (1/a)A is a
fractional ideal not contained in A when a is not
a unit. -/

-- A fractional ideal is an A-submodule of K, not
-- necessarily contained in A
#check @FractionalIdeal.coeToSubmodule

end IdealGroup
```

Every nonzero principal fractional ideal $`(x)` is invertible (since $`(x)^{-1} = (x^{-1})`), and a product of principal fractional ideals is principal (since $`(x)(y) = (xy)`), as is the unit ideal $`(1)`, thus the set of nonzero principal fractional ideals $`\mathcal{P}_A` is a subgroup of $`\mathcal{I}_A`.

```lean
section PrincipalFractionalIdeals

variable {A : Type*} [CommRing A] [IsDomain A]
  [IsNoetherianRing A]
variable {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]

open FractionalIdeal

/-! ### Claim 1: Every nonzero principal fractional
ideal (x) is invertible

The book says: "(x)⁻¹ = (x⁻¹)". In Mathlib,
`toPrincipalIdeal` maps x ∈ Kˣ to a *unit*
fractional ideal — so by construction, the image
is invertible. The inverse of
`toPrincipalIdeal x` is
`toPrincipalIdeal x⁻¹`. -/

-- toPrincipalIdeal maps Kˣ into the invertible
-- fractional ideals
#check toPrincipalIdeal (R := A) (K := K)

-- It is a group homomorphism, so
-- toPrincipalIdeal(x⁻¹) =
-- (toPrincipalIdeal x)⁻¹
#check MonoidHom.map_inv
  (toPrincipalIdeal (R := A) (K := K))

/-! ### Claim 2: Product of principal fractional
ideals is principal

The book says: "(x)(y) = (xy)". This is exactly
the statement that `toPrincipalIdeal` is a
(monoid) homomorphism. -/

-- toPrincipalIdeal(xy) =
-- toPrincipalIdeal(x) * toPrincipalIdeal(y)
#check MonoidHom.map_mul
  (toPrincipalIdeal (R := A) (K := K))

/-! ### Claim 3: 𝒫_A is a subgroup of ℐ_A

The book concludes that the set of nonzero
principal fractional ideals 𝒫_A is a subgroup
of ℐ_A. In Mathlib, this is the range (image)
of `toPrincipalIdeal`, which is a subgroup of
`(FractionalIdeal A⁰ K)ˣ`. -/

-- The range of toPrincipalIdeal is the
-- subgroup 𝒫_A
#check (toPrincipalIdeal (R := A) (K := K)).range

-- 𝒫_A is a normal subgroup (ℐ_A is abelian, so
-- every subgroup is normal)
#check PrincipalIdeals.normal (R := A) (K := K)

-- The unit ideal (1) is principal: it is
-- toPrincipalIdeal(1)
#check MonoidHom.map_one
  (toPrincipalIdeal (R := A) (K := K))

end PrincipalFractionalIdeals
```

# Definition 2.23
%%%
number := false
%%%

_Definition 2.23._ Let $`A` be a noetherian domain. The quotient $`\operatorname{cl}(A) := \mathcal{I}_A / \mathcal{P}_A` is the _ideal class group_ of $`A`; it is also called the _Picard group_ of $`A` and denoted $`\operatorname{Pic}(A)`.$^3$

```lean
section IdealClassGroup

variable (A : Type*) [CommRing A] [IsDomain A]
  [IsNoetherianRing A]

open scoped nonZeroDivisors

/-! ### The definition

**Definition 2.23.** The ideal class group
cl(A) = ℐ_A / 𝒫_A. In Mathlib this is
`ClassGroup`. -/

-- cl(A) = ClassGroup A
#check ClassGroup (R := A)

/-! ### The subgroup of principal ideals 𝒫_A

The map `toPrincipalIdeal` sends x ∈ Kˣ to the
invertible fractional ideal (x). Its range is the
subgroup 𝒫_A of principal fractional ideals. -/

-- toPrincipalIdeal : Kˣ →* (FractionalIdeal A⁰ K)ˣ
#check toPrincipalIdeal
  (R := A) (K := FractionRing A)

-- The range of toPrincipalIdeal is a normal
-- subgroup (which it must be, since the group is
-- abelian)
#check PrincipalIdeals.normal
  (R := A) (K := FractionRing A)

/-! ### The quotient structure

ClassGroup is a commutative group — the quotient
of an abelian group by a subgroup. -/

-- cl(A) is a commutative group
noncomputable example :
    CommGroup (ClassGroup A) := inferInstance

/-! ### The equivalence with the explicit quotient

For a general fraction ring K, the class group is
canonically isomorphic to
(FractionalIdeal A⁰ K)ˣ ⧸
(toPrincipalIdeal A K).range. -/

variable (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K]

-- ClassGroup A ≃*
-- (FractionalIdeal A⁰ K)ˣ ⧸
-- (toPrincipalIdeal A K).range
#check ClassGroup.equiv (R := A) (K := K)

/-! ### The quotient map

The canonical surjection from ℐ_A onto cl(A). -/

-- mk : (FractionalIdeal A⁰ K)ˣ →* ClassGroup A
#check ClassGroup.mk (R := A) (K := K)

/-! ### Two invertible ideals represent the same
class iff they differ by a principal ideal -/

-- I and J have the same class iff
-- ∃ x ∈ Kˣ, I * toPrincipalIdeal x = J
#check @ClassGroup.mk_eq_mk A _ _

end IdealClassGroup
```

# Example 2.24
%%%
number := false
%%%

_Example 2.24._ If $`A` is a DVR with uniformizer $`\pi` then its nonzero fractional ideals are the principal fractional ideals $`(\pi^n)` with $`n \in \mathbb{Z}` (including $`n \leq 0`). We have $`(\pi^m)(\pi^n) = (\pi^{m+n})`, thus the ideal group of $`A` is isomorphic to $`\mathbb{Z}` (under addition). In this case $`\mathcal{P}_A = \mathcal{I}_A` and the ideal class group $`\operatorname{cl}(A)` is trivial.

```lean
section DVRExample

variable {A : Type*} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]

/-! ### Background: DVR structure

A DVR is a local PID that is not a field. -/

-- DVR is a PID
example : IsPrincipalIdealRing A := inferInstance

-- DVR is a local ring
example : IsLocalRing A := inferInstance

-- DVR is not a field
#check IsDiscreteValuationRing.not_a_field'
  (R := A)

-- DVR has a uniformizer (generator of the maximal
-- ideal)
#check IsDiscreteValuationRing.exists_irreducible
  (R := A)

/-! ### Claim 1: Nonzero fractional ideals of a DVR
are (πⁿ) for n ∈ ℤ

In a PID, every nonzero ideal is principal. Since
a DVR has a unique (up to associates) irreducible
π, every nonzero ideal is (πⁿ) for n ≥ 0. For
fractional ideals, this extends to all n ∈ ℤ. -/

-- In a PID, every nonzero ideal is principal
#check IsPrincipalIdealRing.principal (R := A)

-- Every nonzero element of a DVR is a unit times
-- a power of π
#check
  IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (R := A)

-- Every ideal is a power of the maximal ideal
#check
  IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (R := A)

/-! ### Claim 2: (πᵐ)(πⁿ) = (π^(m+n))

The multiplicativity of `spanSingleton`:
`spanSingleton(x) * spanSingleton(y) =
spanSingleton(x * y)`. -/

-- spanSingleton is multiplicative
#check
  FractionalIdeal.spanSingleton_mul_spanSingleton

/-! ### Claim 3: 𝒫_A = ℐ_A and cl(A) is trivial

Since a DVR is a PID, every fractional ideal is
principal, so 𝒫_A = ℐ_A. The quotient
cl(A) = ℐ_A / 𝒫_A is therefore trivial. -/

-- The class group of a PID has cardinality 1
#check card_classGroup_eq_one (R := A)

end DVRExample
```

# Remark 2.25
%%%
number := false
%%%

_Remark 2.25._ A Dedekind domain is a UFD if and only if its ideal class group is trivial (we will prove this in the next lecture), thus $`\operatorname{cl}(A)` may be viewed as a measure of how far $`A` is from being a UFD.

---

$^3$In general, the Picard group of a commutative ring $`A` as the group of isomorphism classes of $`A`-modules that are invertible under tensor product (equivalently, projective modules of rank one). When $`A` is a noetherian domain, the Picard group of $`A` is canonically isomorphic to the ideal class group of $`A` and the two notions may be used interchangeably.

```lean
section RemarkDedekindUFD

/-! ### Claim 1a: Dedekind + UFD → trivial class
group

If A is a Dedekind domain and a UFD, then it is a
PID. A PID has trivial class group. -/

-- Dedekind + UFD → PID
#check
  @IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid

-- PID → trivial class group
#check @card_classGroup_eq_one

/-! ### Claim 1b: Dedekind + trivial class group →
UFD

The converse direction: if cl(A) = 1 then every
ideal is principal (PID), and a PID is a UFD. -/

-- For Dedekind domains: |cl(A)| = 1 ↔ A is a PID
#check @card_classGroup_eq_one_iff

-- PID → UFD
#check @PrincipalIdealRing.to_uniqueFactorizationMonoid

/-! ### Claim 2: cl(A) measures distance from UFD

This is a conceptual/motivational remark — no
Lean formalization needed. The formal content is
captured by Claim 1: cl(A) = 1 ↔ A is a UFD
(for Dedekind domains). -/

/-! ### Claim 3 (Footnote 3): Picard group ≅ ideal
class group

For a noetherian domain, the Picard group Pic(A)
(group of isomorphism classes of invertible
A-modules under tensor product) is canonically
isomorphic to the ideal class group cl(A). -/

-- The canonical isomorphism
-- ClassGroup R ≃* Pic R
#check @ClassGroup.equivPic

end RemarkDedekindUFD
```
