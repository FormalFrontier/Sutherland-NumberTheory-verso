import VersoManual
import Mathlib.Tactic.Recall
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Finprod

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.code.warnLineLength 90

#doc (Manual) "Absolute Values on ℚ" =>
%%%
tag := "absolute-values-on-q"
file := some "absolute-values-on-q"
number := false
%%%

To avoid confusion we will denote the usual absolute value on $`\mathbb{Q}` (inherited from $`\mathbb{R}`) by $`\lvert \cdot \rvert_{\infty}`; it is an archimedean absolute value. But there are infinitely many others. Recall that any element of $`\mathbb{Q}^{\times}` may be written as $`\pm \prod_q q^{e_q}`, where the product ranges over primes and the exponents $`e_q \in \mathbb{Z}` are uniquely determined (as is the sign).

# Definition 1.7
%%%
number := false
%%%

_Definition 1.7._ For a prime $`p` the _$`p`-adic valuation_ $`v_p \colon \mathbb{Q} \to \mathbb{Z}` is defined by

$$`v_p\!\left(\pm \prod_q q^{e_q}\right) \coloneqq e_p,`

and we define $`v_p(0) \coloneqq \infty`. The _$`p`-adic absolute value_ on $`\mathbb{Q}` is defined by

$$`\lvert x \rvert_p \coloneqq p^{-v_p(x)},`

where $`\lvert 0 \rvert_p = p^{-\infty}` is understood to be $`0`.

```lean
/-- Definition 1.7: The p-adic valuation vₚ(x)
for x : ℚ. -/
recall padicValRat (p : ℕ) (q : ℚ) : ℤ

/-- Definition 1.7: The p-adic norm |x|ₚ =
p^{-vₚ(x)} as a rational number. -/
recall padicNorm (p : ℕ) (q : ℚ) : ℚ

/-- Definition 1.7: The p-adic absolute value |x|ₚ
bundled as AbsoluteValue ℚ ℝ. -/
recall Rat.AbsoluteValue.padic (p : ℕ)
    [Fact p.Prime] : AbsoluteValue ℚ ℝ
```

# Theorem 1.8 (Ostrowski's Theorem)
%%%
number := false
%%%

_Theorem 1.8_ (Ostrowski's Theorem)_._ Every nontrivial absolute value on $`\mathbb{Q}` is equivalent to $`\lvert \cdot \rvert_p` for some $`p \leq \infty`.

_Proof._ See Problem Set 1. $`\square`

```lean
/-- Theorem 1.8 (Ostrowski): Every nontrivial
absolute value on ℚ is equivalent to the real
absolute value or to a p-adic absolute value for
a unique prime p. -/
recall Rat.AbsoluteValue.equiv_real_or_padic
    (f : AbsoluteValue ℚ ℝ)
    (hf : f.IsNontrivial) :
    f.IsEquiv Rat.AbsoluteValue.real ∨
    ∃! p : ℕ, ∃ _ : Fact p.Prime,
      f.IsEquiv (Rat.AbsoluteValue.padic p)
```

# Theorem 1.9 (Product Formula)
%%%
number := false
%%%

_Theorem 1.9_ (Product Formula)_._ For every $`x \in \mathbb{Q}^{\times}` we have

$$`\prod_{p \leq \infty} \lvert x \rvert_p = 1.`

_Proof._ See Problem Set 1. $`\square`

```lean
/-- Theorem 1.9 (general). For nonzero x : K, the
product of |x|_v over all places v of a number
field K equals 1. -/
recall NumberField.prod_abs_eq_one
    {K : Type*} [Field K] [NumberField K]
    {x : K} (hx : x ≠ 0) :
    (∏ w : NumberField.InfinitePlace K,
      w x ^ w.mult) *
    ∏ᶠ w : NumberField.FinitePlace K, w x = 1

/-- For a nonzero rational, padicNorm p q = 1 for
all primes p not dividing the numerator or
denominator. -/
theorem padicNorm_eq_one_of_not_dvd (q : ℚ)
    (hq : q ≠ 0) (p : ℕ) (hp : Nat.Prime p)
    (hp_ndvd :
      p ∉ (q.num.natAbs * q.den).primeFactors) :
    padicNorm p q = 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hndvd : ¬(p ∣ q.num.natAbs * q.den) := by
    intro h
    exact hp_ndvd (Nat.mem_primeFactors.mpr
      ⟨hp, h, mul_ne_zero
        (Int.natAbs_ne_zero.mpr
          (Rat.num_ne_zero.mpr hq))
        (Rat.den_pos q).ne'⟩)
  have hndvd_num : ¬(p ∣ q.num.natAbs) :=
    fun h => hndvd (dvd_mul_of_dvd_left h _)
  have hndvd_den : ¬(p ∣ q.den) :=
    fun h => hndvd (dvd_mul_of_dvd_right h _)
  rw [padicNorm.eq_zpow_of_nonzero hq]
  suffices padicValRat p q = 0 by rw [this]; simp
  change (padicValInt p q.num : ℤ) -
    (padicValNat p q.den : ℤ) = 0
  simp [padicValInt,
    padicValNat.eq_zero_of_not_dvd hndvd_num,
    padicValNat.eq_zero_of_not_dvd hndvd_den]

private lemma fta_prod_nat (n : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors,
      p ^ padicValNat p n = n := by
  have h_eq : ∀ p ∈ n.primeFactors,
      p ^ padicValNat p n =
        p ^ n.factorization p :=
    fun p hp => by rw [Nat.factorization_def n
      (Nat.prime_of_mem_primeFactors hp)]
  rw [Finset.prod_congr rfl h_eq]
  exact Nat.prod_factorization_pow_eq_self hn

private lemma fta_prod_rat (n : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors,
      (p : ℚ) ^ padicValNat p n = (n : ℚ) := by
  have h : ∀ p ∈ n.primeFactors,
      (p : ℚ) ^ padicValNat p n =
        ((p ^ padicValNat p n : ℕ) : ℚ) :=
    fun p _ =>
      (Nat.cast_pow p (padicValNat p n)).symm
  rw [Finset.prod_congr rfl h,
    ← Nat.cast_prod, Nat.cast_inj]
  exact fta_prod_nat n hn

/-- Theorem 1.9 (Product Formula for ℚ): For any
nonzero rational q, the product of the real absolute
value and all p-adic absolute values equals 1. -/
theorem product_formula (q : ℚ) (hq : q ≠ 0) :
    |q| * ∏ p ∈
      (q.num.natAbs * q.den).primeFactors,
      padicNorm p q = 1 := by
  set a := q.num.natAbs with ha_def
  set b := q.den with hb_def
  have ha : a ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq)
  have hb : (b : ℕ) ≠ 0 := (Rat.den_pos q).ne'
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  have hcop : Nat.Coprime a b := q.reduced
  have habs : (|q| : ℚ) = (a : ℚ) / (b : ℚ) := by
    rw [Rat.abs_def, Rat.divInt_eq_div,
      Int.cast_natCast, Int.cast_natCast]
  have hS : (a * b).primeFactors =
      a.primeFactors ∪ b.primeFactors :=
    Nat.primeFactors_mul ha hb
  have hdisj :
      Disjoint a.primeFactors b.primeFactors :=
    hcop.disjoint_primeFactors
  rw [hS, Finset.prod_union hdisj]
  have hprod_a : ∏ p ∈ a.primeFactors,
      padicNorm p q = (a : ℚ)⁻¹ := by
    have h_val : ∀ p ∈ a.primeFactors,
        padicNorm p q =
          (p : ℚ) ^ (-(padicValNat p a : ℤ)) := by
      intro p hp
      have hp_prime :=
        Nat.prime_of_mem_primeFactors hp
      haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
      have hp_ndvd_b : ¬(p ∣ b) :=
        fun h => Finset.disjoint_left.mp hdisj hp
          (Nat.mem_primeFactors.mpr
            ⟨hp_prime, h, hb⟩)
      rw [padicNorm.eq_zpow_of_nonzero hq]
      congr 1
      change -((padicValInt p q.num : ℤ) -
        (padicValNat p b : ℤ)) =
        -(padicValNat p a : ℤ)
      simp [padicValInt, ha_def,
        padicValNat.eq_zero_of_not_dvd hp_ndvd_b]
    rw [Finset.prod_congr rfl h_val]
    simp_rw [zpow_neg,
      Finset.prod_inv_distrib, zpow_natCast]
    rw [fta_prod_rat a ha]
  have hprod_b : ∏ p ∈ b.primeFactors,
      padicNorm p q = (b : ℚ) := by
    have h_val : ∀ p ∈ b.primeFactors,
        padicNorm p q =
          (p : ℚ) ^ (padicValNat p b : ℤ) := by
      intro p hp
      have hp_prime :=
        Nat.prime_of_mem_primeFactors hp
      haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
      have hp_ndvd_a : ¬(p ∣ a) :=
        fun h => Finset.disjoint_right.mp hdisj hp
          (Nat.mem_primeFactors.mpr
            ⟨hp_prime, h, ha⟩)
      rw [padicNorm.eq_zpow_of_nonzero hq]
      congr 1
      change -((padicValInt p q.num : ℤ) -
        (padicValNat p b : ℤ)) =
        (padicValNat p b : ℤ)
      have h0 : (padicValInt p q.num : ℤ) = 0 := by
        simp only [padicValInt]
        exact_mod_cast
          padicValNat.eq_zero_of_not_dvd hp_ndvd_a
      omega
    rw [Finset.prod_congr rfl h_val]
    simp_rw [zpow_natCast]
    exact fta_prod_rat b hb
  rw [habs, hprod_a, hprod_b,
    mul_comm (a : ℚ)⁻¹ (b : ℚ), ← mul_assoc,
    div_mul_cancel₀ _ hb', mul_inv_cancel₀ ha']
```
