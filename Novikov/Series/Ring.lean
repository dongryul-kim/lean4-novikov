import Novikov.Series.Multiplication
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pointwise.Set.Basic

open Pointwise

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
  let S : Finset ((ι → Γ) × (ι → Γ)) := (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop d).toFinset
  Finset.sum S fun p : (ι → Γ) × (ι → Γ) => f p.1 * g p.2

/-- The Novikov finiteness condition for the convolution product. -/
lemma is_novikov_series_novikovMulFun (f g : NovikovSeries Γ ι A) :
    isNovikovSeries (novikovMulFun f g) :=
  isNovikovSeries_mul f g AddMonoidHom.mul

/-- The multiplicative identity element. -/
noncomputable def novikovOne :
    NovikovSeries Γ ι A := novikovMonomial 1 0

@[simp]
lemma novikovOne_val (d : ι → Γ) :
    (novikovOne d) = if d = 0 then (1 : A) else (0 : A) := rfl

/-- The convolution product of two Novikov series.
`(f * g)(d) = ∑_{d1 + d2 = d} f(d1) * g(d2)`.
The sum is finite by `finite_pair_sum_eq`. -/
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
  ext d
  rw [novikovOne, novikovMul]
  let mul := Novikov.novikovSeriesMul_left_monomial 1 f AddMonoidHom.mul 0 d
  simp only [zero_add] at mul
  simp_all only [AddMonoidHom.coe_mul, AddMonoidHom.coe_mulLeft, one_mul]

lemma novikovMul_mul_one
    (f : NovikovSeries Γ ι A) : novikovMul f novikovOne = f := by
  ext d
  rw [novikovOne, novikovMul]
  let mul := Novikov.novikovSeriesMul_right_monomial f 1 AddMonoidHom.mul 0 d
  simp only [add_zero] at mul
  simp_all only [AddMonoidHom.coe_mul, AddMonoidHom.coe_mulLeft, mul_one]

lemma novikovMul_mul_comm
    (f g : NovikovSeries Γ ι A) : novikovMul f g = novikovMul g f :=
  novikovSeriesMul_comm f g AddMonoidHom.mul AddMonoidHom.mul mul_comm

lemma novikovMul_right_distrib
    (f g h : NovikovSeries Γ ι A) :
    novikovMul (f + g) h = novikovMul f h + novikovMul g h := by
  exact novikovSeriesMul_right_distrib f g h AddMonoidHom.mul

lemma novikovMul_left_distrib
    (f g h : NovikovSeries Γ ι A) :
    novikovMul f (g + h) = novikovMul f g + novikovMul f h := by
  exact novikovSeriesMul_left_distrib f g h AddMonoidHom.mul

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
  left_distrib := novikovMul_left_distrib
  right_distrib := novikovMul_right_distrib
  zero_mul := novikovMul_zero_mul
  mul_zero := novikovMul_mul_zero

lemma support_pow_subset {A : Type*} [CommRing A] (f : NovikovSeries Γ ι A) (n : ℕ) :
    (f ^ n).support ⊆ n • f.support := by
  induction n with
  | zero =>
    rw [pow_zero, zero_nsmul]
    intro d hd
    rw [NovikovSeries.mem_support] at hd
    have h1 : (1 : NovikovSeries Γ ι A) d = if d = 0 then 1 else 0 := rfl
    rw [h1] at hd
    by_cases h0 : d = 0
    · subst h0; exact Set.mem_singleton 0
    · rw [if_neg h0] at hd; contradiction
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    refine (support_mul_subset (f ^ n) f (AddMonoidHom.mul)).trans ?_
    exact Set.add_subset_add ih (Set.Subset.refl _)

end RingStructure

/-- The canonical ring homomorphism `A → NovikovSeriesMultivar Γ ι A` sending `a`
to the series with `a` at the zero exponent and `0` elsewhere. -/
noncomputable def algebraMapNovikov :
    A →+* NovikovSeries Γ ι A where
  toFun a := ⟨fun d => if d = (0 : ι → Γ) then a else 0, is_novikov_series_monomial a 0⟩
  map_one' := by
    rfl
  map_mul' := by
    intros x y
    change novikovMonomial (x * y) (0 : ι → Γ) = novikovSeriesMul (novikovMonomial x (0 : ι → Γ)) (novikovMonomial y (0 : ι → Γ)) AddMonoidHom.mul
    rw [novikovSeriesMul_monomial]
    simp
  map_zero' := by
    ext d
    dsimp
    split_ifs <;> rfl
  map_add' := by
    intros x y
    ext d
    dsimp
    split_ifs <;> simp

/-- Novikov series form an `A`-algebra. -/
noncomputable instance novikovAlgebra :
    Algebra A (NovikovSeries Γ ι A) where
  smul r f := ⟨r • f.val, is_novikov_series_smul r f.prop⟩
  smul_def' r f := by
    ext d
    have h_lhs : (r • f).val d = r * f.val d := rfl
    rw [h_lhs]
    rw [novikovMul_val]
    unfold novikovMulFun
    rw [Finset.sum_eq_single ((0 : ι → Γ), d)]
    · dsimp [algebraMapNovikov]
      simp
    · rintro ⟨b1, b2⟩ hb hne
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hb
      rcases hb with ⟨hsum, hb1, hb2⟩
      dsimp [algebraMapNovikov] at hb1
      split_ifs at hb1 with h0
      · subst h0
        simp only [zero_add] at hsum
        subst hsum
        exact (hne rfl).elim
      · contradiction
    · intro h
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at h
      dsimp [algebraMapNovikov] at h
      simp only [zero_add, ↓reduceIte, true_and, not_and, not_not] at h
      by_cases hr : r = 0
      · subst hr; simp
      · by_cases hfd : f.val d = 0
        · rw [hfd]; simp
        · exfalso; simp_all only [not_false_eq_true, mul_zero, imp_false, not_true_eq_false]
  commutes' r f := novikovMul_mul_comm _ _
  algebraMap := algebraMapNovikov

end Novikov

