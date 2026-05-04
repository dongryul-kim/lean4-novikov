import Novikov.Series.Basic
import Novikov.Series.Finite
import Novikov.Series.Multiplication
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finite.Prod

/-! # Ring and algebra structure on multivariable Novikov series

This file shows that `NovikovSeries Γ ι A` is a commutative ring when `A` is a
commutative ring, and an `A`-algebra.

Multiplication is defined by the Cauchy product (convolution):
`(f * g)(d) = ∑_{d1 + d2 = d} f(d1) · g(d2)`.

The key difficulty is proving that for each `d`, this sum is finite, and that the
product satisfies the Novikov finiteness condition.
-/

namespace Novikov

variable {ι A : Type*} [Fintype ι] [CommRing A]
variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S}

section RingStructure

/-- The underlying function of the convolution product (without the Novikov proof). -/
noncomputable def novikovMulFun
    (f g : NovikovSeries Γ ι A) (d : ι → Γ) : A :=
  let S : Finset ((ι → Γ) × (ι → Γ)) := (finite_convolution_support f g d).toFinset
  Finset.sum S fun p : (ι → Γ) × (ι → Γ) => f p.1 * g p.2

/-- The Novikov finiteness condition for the convolution product. -/
lemma isNovikov_novikovMulFun (f g : NovikovSeries Γ ι A) :
    isNovikovSeries (novikovMulFun f g) := by
  intro s hs C
  let Sf := {d1 : ι → Γ | f d1 ≠ 0 ∧ ∑ i, s i * (d1 i : ℝ) < C + 1}
  let Sg := {d2 : ι → Γ | g d2 ≠ 0 ∧ ∑ i, s i * (d2 i : ℝ) < 0}
  have hf : Sf.Finite := f.prop s hs (C + 1)
  have hg : Sg.Finite := g.prop s hs 0
  let T1 := ⋃ d1 ∈ Sf, (fun d2 => d1 + d2) '' {d2 : ι → Γ | g d2 ≠ 0 ∧ ∑ i, s i * (d2 i : ℝ) < C - ∑ i, s i * (d1 i : ℝ)}
  let T2 := ⋃ d2 ∈ Sg, (fun d1 => d1 + d2) '' {d1 : ι → Γ | f d1 ≠ 0 ∧ ∑ i, s i * (d1 i : ℝ) < C - ∑ i, s i * (d2 i : ℝ)}
  have hT1 : T1.Finite := by
    have h' : ∀ d1 ∈ Sf, ((fun d2 => d1 + d2) '' {d2 : ι → Γ | g d2 ≠ 0 ∧ ∑ i, s i * (d2 i : ℝ) < C - ∑ i, s i * (d1 i : ℝ)}).Finite := by
      intro d1 _
      have hfin : {d2 : ι → Γ | g d2 ≠ 0 ∧ ∑ i, s i * (d2 i : ℝ) < C - ∑ i, s i * (d1 i : ℝ)}.Finite := g.prop s hs (C - ∑ i, s i * (d1 i : ℝ))
      exact Set.Finite.image (fun d2 => d1 + d2) hfin
    exact Set.Finite.biUnion hf h'
  have hT2 : T2.Finite := by
    have h' : ∀ d2 ∈ Sg, ((fun d1 => d1 + d2) '' {d1 : ι → Γ | f d1 ≠ 0 ∧ ∑ i, s i * (d1 i : ℝ) < C - ∑ i, s i * (d2 i : ℝ)}).Finite := by
      intro d2 _
      have hfin : {d1 : ι → Γ | f d1 ≠ 0 ∧ ∑ i, s i * (d1 i : ℝ) < C - ∑ i, s i * (d2 i : ℝ)}.Finite := f.prop s hs (C - ∑ i, s i * (d2 i : ℝ))
      exact Set.Finite.image (fun d1 => d1 + d2) hfin
    exact Set.Finite.biUnion hg h'
  have h_sub : {d : ι → Γ | novikovMulFun f g d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} ⊆ T1 ∪ T2 := by
    intro d hd
    rcases hd with ⟨hne, hlt⟩
    have hsum_nz : ∃ p ∈ (finite_convolution_support f g d).toFinset, f p.1 * g p.2 ≠ 0 := by
      by_contra h
      push Not at h
      have : novikovMulFun f g d = 0 := by
        simp only [novikovMulFun, ne_eq]
        apply Finset.sum_eq_zero
        intro p hp
        have h0 : f p.1 * g p.2 = 0 := by
          by_contra hne
          simp_all only [ne_eq, Set.mem_setOf_eq, Set.Finite.mem_toFinset, and_imp, Prod.forall, not_false_eq_true,
            not_true_eq_false, Sf, Sg, T1, T2]
        simp only [h0]
      contradiction
    rcases hsum_nz with ⟨⟨d1, d2⟩, hp, hprod⟩
    have hp' : d1 + d2 = d ∧ f d1 ≠ 0 ∧ g d2 ≠ 0 := by
      simp_all only [ne_eq, Set.mem_setOf_eq, Set.Finite.mem_toFinset, not_false_eq_true, and_self, Sf, Sg, T1, T2] 
    rcases hp' with ⟨hsum, hf1, hg2⟩
    have hL : ∑ i, s i * (d i : ℝ) = ∑ i, s i * (d1 i : ℝ) + ∑ i, s i * (d2 i : ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have h_eq : (d i : ℝ) = (d1 i : ℝ) + (d2 i : ℝ) := by
        have h := congr_fun hsum i
        simp only [Pi.add_apply] at h
        rw [← h]
        rfl
      rw [h_eq]
      ring
    by_cases h : ∑ i, s i * (d1 i : ℝ) < C + 1
    · left
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, exists_prop, T1]
      refine ⟨d1, ⟨hf1, h⟩, d2, ⟨hg2, by linarith⟩, ?_⟩
      funext i
      have h_i := congr_fun hsum i
      subst hsum
      simp_all only [ne_eq, Set.mem_setOf_eq, Pi.add_apply, Set.Finite.mem_toFinset,
        not_false_eq_true, and_self, Sf, Sg, T1, T2]
    · right
      have hgd2 : ∑ i, s i * (d2 i : ℝ) < 0 := by linarith
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, exists_prop, T2]
      refine ⟨d2, ⟨hg2, hgd2⟩, d1, ⟨hf1, by linarith⟩, ?_⟩
      funext i
      have h_i := congr_fun hsum i
      subst hsum
      simp_all only [ne_eq, Set.mem_setOf_eq, not_lt, Pi.add_apply, Set.Finite.mem_toFinset,
        not_false_eq_true, and_self, Sf, Sg, T1, T2]
  exact Set.Finite.subset (Set.Finite.union hT1 hT2) h_sub

/-- The multiplicative identity element. -/
noncomputable def novikovOne :
    NovikovSeries Γ ι A := novikovMonomial 1 0

@[simp]
lemma novikovOne_val (d : ι → Γ) :
    (novikovOne d) = if d = 0 then (1 : A) else (0 : A) := rfl

/-- The convolution product of two Novikov series.
`(f * g)(d) = ∑_{d1 + d2 = d} f(d1) * g(d2)`.
The sum is finite by `finite_convolution_support`. -/
noncomputable def novikovMul [ha : CommRing A]
    (f g : NovikovSeries Γ ι A) : NovikovSeries Γ ι A :=
  novikovSeriesMul f g AddMonoidHom.mul

noncomputable instance : Mul (NovikovSeries Γ ι A) where
  mul := novikovMul

@[simp]
lemma novikovMul_val {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S} {ι A : Type*} [Fintype ι] [CommRing A]
    (f g : NovikovSeries Γ ι A) (d : ι → Γ) :
    (f * g) d = novikovMulFun f g d := rfl

instance : AddCommGroup (NovikovSeries Γ ι A) := inferInstance

lemma novikovMul_zero_mul
    (f : NovikovSeries Γ ι A) : novikovMul 0 f = 0 :=
    novikovSeriesMul_zero_mul f AddMonoidHom.mul

lemma novikovMul_mul_zero
    (f : NovikovSeries Γ ι A) : novikovMul f 0 = 0 :=
    novikovSeriesMul_mul_zero f AddMonoidHom.mul

lemma novikovMul_one_mul
    (f : NovikovSeries Γ ι A) : novikovMul novikovOne f = f := by
  refine Subtype.ext (funext (fun d => ?_))
  rw [novikovOne, novikovMul]
  let mul := Novikov.novikovSeriesMul_left_monomial 1 f AddMonoidHom.mul 0 d
  simp only [zero_add] at mul
  simp_all only [AddMonoidHom.coe_mul, AddMonoidHom.coe_mulLeft, one_mul]

lemma novikovMul_mul_one
    (f : NovikovSeries Γ ι A) : novikovMul f novikovOne = f := by
  refine Subtype.ext (funext (fun d => ?_))
  rw [novikovOne, novikovMul]
  let mul := Novikov.novikovSeriesMul_right_monomial f 1 AddMonoidHom.mul 0 d
  simp only [add_zero] at mul
  simp_all only [AddMonoidHom.coe_mul, AddMonoidHom.coe_mulLeft, mul_one]

lemma novikovMul_mul_comm
    (f g : NovikovSeries Γ ι A) : novikovMul f g = novikovMul g f := by
  refine Subtype.ext (funext (fun d => ?_))
  simp only [novikovMul]
  refine Finset.sum_bij ?_ ?_ ?_ ?_ ?_
  · exact fun p _ => (p.2, p.1)
  · -- hi: image lands in target
    intro p hp
    have hmem : p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ g p.2 ≠ 0 := by
      have h' := hp
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h'
      exact h'
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · funext i
      have h_i := congr_fun hmem.1 i
      simp only [Pi.add_apply] at h_i
      rw [add_comm]
      exact h_i
    constructor
    · exact hmem.2.2
    · exact hmem.2.1
  · -- injectivity
    intro p _ q _ h_eq
    simp only [Prod.mk.injEq] at h_eq
    exact Prod.ext h_eq.2 h_eq.1
  · -- surjectivity
    intro q hq
    have hmem : q.1 + q.2 = d ∧ g q.1 ≠ 0 ∧ f q.2 ≠ 0 := by
      have h' := hq
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h'
      exact h'
    refine ⟨(q.2, q.1), ?_, ?_⟩
    · -- witness is in source
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      constructor
      · funext i
        have h_i := congr_fun hmem.1 i
        simp only [Pi.add_apply] at h_i
        rw [add_comm]
        exact h_i
      constructor
      · exact hmem.2.2
      · exact hmem.2.1
    · -- swap gives back q
      simp only [Prod.mk.eta]
  · -- term equality
    intro p _
    exact mul_comm _ _

lemma novikovMul_left_distrib
    (f g h : NovikovSeries Γ ι A) :
    novikovMul (f + g) h = novikovMul f h + novikovMul g h := by
  exact novikovSeriesMul_left_distrib f g h AddMonoidHom.mul

lemma novikovMul_right_distrib
    (f g h : NovikovSeries Γ ι A) :
    novikovMul f (g + h) = novikovMul f g + novikovMul f h := by
  exact novikovSeriesMul_right_distrib f g h AddMonoidHom.mul

lemma novikovMul_mul_assoc
    (f g h : NovikovSeries Γ ι A) :
    novikovMul (novikovMul f g) h = novikovMul f (novikovMul g h) := by
  exact novikovSeriesMul_assoc f g h AddMonoidHom.mul AddMonoidHom.mul AddMonoidHom.mul AddMonoidHom.mul mul_assoc

/-- Novikov series form a commutative ring. -/
noncomputable instance NovikovSeriesRing : CommRing (NovikovSeries Γ ι A) where
  mul := novikovMul
  mul_assoc := novikovMul_mul_assoc
  one := novikovOne
  one_mul := novikovMul_one_mul
  mul_one := novikovMul_mul_one
  mul_comm := novikovMul_mul_comm
  left_distrib := novikovMul_right_distrib
  right_distrib := novikovMul_left_distrib
  zero_mul := novikovMul_zero_mul
  mul_zero := novikovMul_mul_zero

end RingStructure

end Novikov
