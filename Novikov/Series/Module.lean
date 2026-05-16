import Novikov.Series.Ring
import Novikov.Series.Exact
import Mathlib.Algebra.Module.BigOperators
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.Algebra.Module.Presentation.Finite
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace Novikov

open TensorProduct

variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ]
variable (Γ : S)
variable {ι A : Type*} [Fintype ι] [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]

/-- Scalar multiplication as a bi-additive map. Alias of mathlib's `_root_.smulAddHom`. -/
def smulAddHom : A →+ M →+ M := _root_.smulAddHom A M

/-- Scalar multiplication of a Novikov series by a Novikov series on M. -/
noncomputable def novikovSeriesSMul (f : NovikovSeries Γ ι A) (m : NovikovSeries Γ ι M) :
    NovikovSeries Γ ι M :=
  novikovSeriesMul f m smulAddHom

noncomputable instance : SMul (NovikovSeries Γ ι A) (NovikovSeries Γ ι M) where
  smul := novikovSeriesSMul Γ

@[simp]
lemma novikovSMul_val (f : NovikovSeries Γ ι A) (m : NovikovSeries Γ ι M) (d : ι → Γ) :
    (f • m) d = novikovSeriesMulFun f m smulAddHom d := rfl

noncomputable instance moduleNovikovSeries : Module (NovikovSeries Γ ι A) (NovikovSeries Γ ι M) where
  smul_add f m1 m2 := by
    exact novikovSeriesMul_left_distrib f m1 m2 smulAddHom
  add_smul f1 f2 m := by
    exact novikovSeriesMul_right_distrib f1 f2 m smulAddHom
  mul_smul f1 f2 m := by
    exact novikovSeriesMul_assoc f1 f2 m AddMonoidHom.mul smulAddHom smulAddHom smulAddHom mul_smul
  one_smul m := by
    ext d
    rw [show (1 : NovikovSeries Γ ι A) = novikovOne from rfl, novikovOne, novikovSMul_val]
    have h : novikovSeriesMulFun (novikovMonomial (1 : A) 0) m smulAddHom d =
             (novikovSeriesMul (novikovMonomial (1 : A) 0) m smulAddHom) (0 + d) := by
      simp only [zero_add]
      rfl
    rw [h, Novikov.novikovSeriesMul_left_monomial (1 : A) m smulAddHom 0 d]
    simp only [smulAddHom, _root_.smulAddHom_apply, one_smul]
  zero_smul m := by
    exact novikovSeriesMul_zero_mul (A := A) m smulAddHom
  smul_zero f := by
    exact novikovSeriesMul_mul_zero (B := M) f smulAddHom

lemma algebraMapNovikov_smul (a : A) (z : NovikovSeries Γ ι M) :
    (algebraMapNovikov (Γ := Γ) (ι := ι) a : NovikovSeries Γ ι A) • z = a • z := by
  ext d
  have h := novikovSeriesMul_left_monomial a z smulAddHom 0 d
  simp only [zero_add] at h
  rw [show (algebraMapNovikov a : NovikovSeries Γ ι A) = novikovMonomial a 0 from rfl]
  exact h

instance novikov_isScalarTower : IsScalarTower A (NovikovSeries Γ ι A) (NovikovSeries Γ ι M) where
  smul_assoc a f m := by
    rw [Algebra.smul_def, mul_smul]
    exact algebraMapNovikov_smul Γ a (f • m)

/-- Component of a `Novikov`-series-valued product equals the convolution on each fiber. -/
lemma novikovSeriesMulFun_pi_apply {ι' : Type*} {N : ι' → Type*}
    [∀ j, AddCommGroup (N j)] [∀ j, Module A (N j)]
    (f : NovikovSeries Γ ι A) (s : NovikovSeries Γ ι (∀ j, N j)) (j : ι') (d : ι → Γ) :
    (novikovSeriesMulFun f s (_root_.smulAddHom A (∀ j, N j)) d) j =
    novikovSeriesMulFun f (⟨fun d' => s.val d' j, is_novikov_series_pi s.prop j⟩)
      (_root_.smulAddHom A (N j)) d := by
  simp only [novikovSeriesMulFun, Finset.sum_apply, _root_.smulAddHom]
  symm
  apply Finset.sum_subset
  · rintro p hp
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hp ⊢
    exact ⟨hp.1, hp.2.1, fun h => hp.2.2 (congr_fun h j)⟩
  · rintro p hp hnot
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hp hnot
    rw [not_and, not_and] at hnot
    have : s.val p.2 j = 0 := by
      have := hnot hp.1 hp.2.1
      rw [not_not] at this
      exact this
    simp [this]

/-- Novikov series with values in a product are equivalent to a product of Novikov series. -/
def novikovPiEquiv {ι' : Type*} [Fintype ι'] :
    NovikovSeries Γ ι (ι' → M) ≃ₗ[NovikovSeries Γ ι A] (ι' → NovikovSeries Γ ι M) where
  toFun s j := ⟨fun d => s.val d j, is_novikov_series_pi s.prop j⟩
  map_add' s t := by
    ext j d
    rfl
  map_smul' f s := by
    ext j d
    simp only [novikovSMul_val, smulAddHom, Novikov.novikovSeriesMulFun_pi_apply]
    rfl
  invFun f := ⟨fun d j => (f j).val d, is_novikov_series_pi_inv (fun j => (f j).prop)⟩
  left_inv s := by
    ext d j
    rfl
  right_inv f := by
    ext j d
    rfl

/-- The natural $A$-linear map $M \to \text{NovikovSeries } \Gamma \ \iota \ M$ sending $m$ to the constant series. -/
noncomputable def toNovikovSeriesLinear : M →ₗ[A] NovikovSeries Γ ι M where
  toFun m := novikovMonomial m 0
  map_add' m1 m2 := by
    ext d
    change (if d = 0 then m1 + m2 else 0) = (if d = 0 then m1 else 0) + (if d = 0 then m2 else 0)
    by_cases h : d = 0 <;> simp [h]
  map_smul' a m := by
    ext d
    change (if d = 0 then a • m else 0) = a • (if d = 0 then m else 0)
    by_cases h : d = 0 <;> simp [h]

/-- The natural map from the base change $A\dparenmult \otimes_A M$
to $M\dparenmult$. -/
noncomputable def novikovBaseChangeMap :
    (NovikovSeries Γ ι A ⊗[A] M) →ₗ[NovikovSeries Γ ι A] NovikovSeries Γ ι M :=
  LinearMap.liftBaseChange (NovikovSeries Γ ι A) (toNovikovSeriesLinear Γ)

@[simp]
lemma novikovBaseChangeMap_tmul (x : NovikovSeries Γ ι A) (m : M) :
    novikovBaseChangeMap Γ (x ⊗ₜ[A] m) = x • novikovMonomial m 0 := rfl

/-- The functor `lmap` commutes with the `NovikovSeries Γ ι A`-action:
`lmap f (x • s) = x • lmap f s`. -/
lemma lmap_smul_novikovSeries {N : Type*} [AddCommGroup N] [Module A N] (f : M →ₗ[A] N)
    (x : NovikovSeries Γ ι A) (s : NovikovSeries Γ ι M) :
    lmap (R := A) (Γ := Γ) (ι := ι) f (x • s) = x • lmap (R := A) (Γ := Γ) (ι := ι) f s := by
  ext d
  exact novikovSeriesMul_map (AddMonoidHom.id A) f.toAddMonoidHom f.toAddMonoidHom
    smulAddHom smulAddHom (fun a b => f.map_smul a b) x s x
    (lmap (R := A) (Γ := Γ) (ι := ι) f s) (fun _ => rfl) (fun _ => rfl) d

/-- Naturality of `toNovikovSeriesLinear` in the module argument. -/
lemma toNovikovSeriesLinear_naturality {N : Type*} [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (m : M) :
    lmap f
        ((toNovikovSeriesLinear Γ : M →ₗ[A] NovikovSeries Γ ι M) m)
      = (toNovikovSeriesLinear Γ : N →ₗ[A] NovikovSeries Γ ι N) (f m) := by
  ext d
  change f ((novikovMonomial m 0).val d) = (novikovMonomial (f m) 0).val d
  simp only [novikovMonomial]
  by_cases h : d = 0 <;> simp [h]

/-- Naturality of `novikovBaseChangeMap` in the module argument: applies on pure tensors. -/
lemma novikovBaseChangeMap_naturality {N : Type*} [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (z : NovikovSeries Γ ι A ⊗[A] M) :
    lmap f ((novikovBaseChangeMap Γ : _ →ₗ[NovikovSeries Γ ι A] NovikovSeries Γ ι M) z)
      = (novikovBaseChangeMap Γ : _ →ₗ[NovikovSeries Γ ι A] NovikovSeries Γ ι N)
          ((LinearMap.lTensor (NovikovSeries Γ ι A) f) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x m =>
    simp only [LinearMap.lTensor_tmul, novikovBaseChangeMap_tmul]
    rw [lmap_smul_novikovSeries]
    congr 1
    exact toNovikovSeriesLinear_naturality Γ f m
  | add z1 z2 hz1 hz2 =>
    simp [hz1, hz2]

/-- `lmap` as a `NovikovSeries Γ ι A`-linear map. -/
def lmapNovikov {N : Type*} [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) :
    NovikovSeries Γ ι M →ₗ[NovikovSeries Γ ι A] NovikovSeries Γ ι N where
  toFun := lmap f
  map_add' s t := (lmap f).map_add s t
  map_smul' := lmap_smul_novikovSeries Γ f

/-! ### Free finite case: `M = ι' → A` -/

variable {ι' : Type*} [Fintype ι'] [DecidableEq ι']

/-- For `M = ι' → A`, the base change map is the composition of
`TensorProduct.piScalarRight` and the inverse of `novikovPiEquiv`. -/
noncomputable def novikovBaseChangeEquivPi :
    (NovikovSeries Γ ι A ⊗[A] (ι' → A)) ≃ₗ[NovikovSeries Γ ι A]
      NovikovSeries Γ ι (ι' → A) :=
  (TensorProduct.piScalarRight A (NovikovSeries Γ ι A) (NovikovSeries Γ ι A) ι').trans
    (novikovPiEquiv (M := A) Γ).symm

/-- The composed equivalence agrees with `novikovBaseChangeMap` for finite-product modules. -/
lemma novikovBaseChangeMap_eq_equivPi :
    (novikovBaseChangeMap Γ : _ →ₗ[NovikovSeries Γ ι A] NovikovSeries Γ ι (ι' → A))
      = (novikovBaseChangeEquivPi (A := A) (ι := ι) (ι' := ι') Γ).toLinearMap := by
  apply (Pi.basisFun A ι').baseChange (NovikovSeries Γ ι A) |>.ext
  intro j
  ext d k
  rw [Module.Basis.baseChange_apply]
  change ((novikovBaseChangeMap Γ : _ →ₗ[NovikovSeries Γ ι A] NovikovSeries Γ ι (ι' → A))
        (1 ⊗ₜ[A] ((Pi.basisFun A ι') j))).val d k =
      ((novikovBaseChangeEquivPi (A := A) (ι := ι) (ι' := ι') Γ).toLinearMap
        (1 ⊗ₜ[A] ((Pi.basisFun A ι') j))).val d k
  rw [novikovBaseChangeMap_tmul, LinearEquiv.coe_toLinearMap, novikovBaseChangeEquivPi,
    LinearEquiv.trans_apply, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, one_smul,
    show (1 : NovikovSeries Γ ι A) = novikovOne from rfl]
  change (novikovMonomial (Pi.basisFun A ι' j) 0).val d k =
    ((novikovPiEquiv Γ).symm (fun j_1 => Pi.basisFun A ι' j j_1 • novikovOne)).val d k
  change (novikovMonomial (Pi.basisFun A ι' j) 0).val d k =
    ((Pi.basisFun A ι' j k • novikovOne : NovikovSeries Γ ι A)).val d
  simp only [novikovMonomial, Pi.basisFun_apply, Pi.single_apply, ite_smul, one_smul, zero_smul]
  by_cases hd : d = 0
  · subst hd; simp; split_ifs <;> simp [Pi.single_apply, *]
  · split_ifs <;> simp [hd, novikovOne_val]


set_option linter.unusedDecidableInType false in
/-- For `M = ι' → A`, `novikovBaseChangeMap` is bijective. -/
lemma novikovBaseChangeMap_bijective_pi :
    Function.Bijective
      (novikovBaseChangeMap Γ : _ →ₗ[NovikovSeries Γ ι A] NovikovSeries Γ ι (ι' → A)) := by
  rw [novikovBaseChangeMap_eq_equivPi]
  exact (novikovBaseChangeEquivPi (A := A) (ι := ι) (ι' := ι') Γ).bijective

/-- For finite `ι'`, the base change map is bijective for `ι' →₀ A`. -/
lemma novikovBaseChangeMap_bijective_finsupp {ι' : Type*} [Finite ι'] :
    Function.Bijective (novikovBaseChangeMap (A := A) (Γ := Γ) (ι := ι) (M := ι' →₀ A)) := by
  cases nonempty_fintype ι'
  classical
  let e : (ι' →₀ A) ≃ₗ[A] (ι' → A) := Finsupp.linearEquivFunOnFinite A A ι'
  let R := NovikovSeries Γ ι A
  let v1 := novikovBaseChangeMap (A := A) (Γ := Γ) (ι := ι) (M := ι' →₀ A)
  let v2 := novikovBaseChangeMap (A := A) (Γ := Γ) (ι := ι) (M := ι' → A)
  let Le := lmapNovikov (Γ := Γ) (ι := ι) (M := ι' →₀ A) (N := ι' → A) e.toLinearMap
  have hv2 : Function.Bijective v2 := novikovBaseChangeMap_bijective_pi Γ
  have hTe : Function.Bijective (LinearMap.lTensor R e.toLinearMap) := (LinearEquiv.lTensor R e).bijective
  have hLe : Function.Bijective Le := ⟨lmap_injective _ e.injective, lmap_surjective _ e.surjective⟩
  have h_eq (x : NovikovSeries Γ ι A ⊗[A] (ι' →₀ A)) : Le (v1 x) = v2 (LinearMap.lTensor R e.toLinearMap x) := by
    change lmap e.toLinearMap (v1 x) = v2 (LinearMap.lTensor R e.toLinearMap x)
    exact novikovBaseChangeMap_naturality Γ e.toLinearMap x
  constructor
  · intro x y h; apply hTe.injective; apply hv2.injective; rw [← h_eq, ← h_eq, h]
  · intro y; obtain ⟨x2, hx2⟩ := hv2.surjective (Le y)
    obtain ⟨x1, hx1⟩ := hTe.surjective x2
    use x1; apply hLe.injective; rw [h_eq, hx1, hx2]

lemma novikovBaseChangeMap_bijective [hM : Module.FinitePresentation A M] :
    Function.Bijective (novikovBaseChangeMap (A := A) (Γ := Γ) (ι := ι) (M := M)) := by
  have h_pres := Module.finitePresentation_iff_exists_presentation.{0, 0, _, _}.mp hM
  obtain ⟨pres, hG, hR⟩ := h_pres
  let R := NovikovSeries Γ ι A
  let P1 := pres.R →₀ A
  let P2 := pres.G →₀ A
  let f := Finsupp.linearCombination A pres.relation
  let g := pres.π
  let v1 := novikovBaseChangeMap (A := A) (Γ := Γ) (ι := ι) (M := P1)
  let v2 := novikovBaseChangeMap (A := A) (Γ := Γ) (ι := ι) (M := P2)
  let vM := novikovBaseChangeMap (A := A) (Γ := Γ) (ι := ι) (M := M)
  let Le_f := lmapNovikov (Γ := Γ) (ι := ι) (M := P1) (N := P2) f
  let Le_g := lmapNovikov (Γ := Γ) (ι := ι) (M := P2) (N := M) g
  have hv1 : Function.Bijective v1 := novikovBaseChangeMap_bijective_finsupp Γ
  have hv2 : Function.Bijective v2 := novikovBaseChangeMap_bijective_finsupp Γ
  have h_pres_iff := (pres.isPresentation_iff).mp pres.toIsPresentation
  have h_exact : Function.Exact f g := by
    rw [LinearMap.exact_iff, h_pres_iff.2, Finsupp.range_linearCombination]
  have h_surj : Function.Surjective g := pres.toIsPresentation.surjective_π
  have h_exact_bot : Function.Exact Le_f Le_g := lmap_exact f g h_exact
  have h_surj_bot : Function.Surjective Le_g := lmap_surjective g h_surj
  have h_exact_top : Function.Exact (LinearMap.lTensor R f) (LinearMap.lTensor R g) :=
    lTensor_exact R h_exact h_surj
  have h_surj_top : Function.Surjective (LinearMap.lTensor R g) := LinearMap.lTensor_surjective R h_surj
  constructor
  · intro x1 x2 h; obtain ⟨y1, rfl⟩ := h_surj_top x1; obtain ⟨y2, rfl⟩ := h_surj_top x2
    have h_eq : Le_g (v2 y1) = Le_g (v2 y2) := by
      change lmap g (v2 y1) = lmap g (v2 y2)
      rw [novikovBaseChangeMap_naturality, novikovBaseChangeMap_naturality, h]
    have : v2 y1 - v2 y2 ∈ LinearMap.range Le_f := by
      rw [← LinearMap.exact_iff.mp h_exact_bot, LinearMap.mem_ker, map_sub, h_eq, sub_self]
    obtain ⟨z, hz⟩ := this; obtain ⟨w, rfl⟩ := hv1.surjective z
    have : v2 y1 - v2 y2 = v2 ((LinearMap.lTensor R f) w) := by
      rw [← novikovBaseChangeMap_naturality Γ f w]; change v2 y1 - v2 y2 = Le_f (v1 w); rw [hz]
    rw [← map_sub] at this; have : y1 - y2 = (LinearMap.lTensor R f) w := hv2.injective this
    have : (LinearMap.lTensor R g) (y1 - y2) = 0 := by
      rw [this, ← LinearMap.comp_apply]
      have h_comp : (LinearMap.lTensor R g).comp (LinearMap.lTensor R f) = 0 := by
        exact LinearMap.ext h_exact_top.apply_apply_eq_zero
      rw [h_comp, LinearMap.zero_apply]
    have h_final : (LinearMap.lTensor R g) y1 - (LinearMap.lTensor R g) y2 = 0 := by
      rw [← map_sub, this]
    exact sub_eq_zero.mp h_final
  · intro y; obtain ⟨y2, rfl⟩ := h_surj_bot y; obtain ⟨x2, rfl⟩ := hv2.surjective y2
    use (LinearMap.lTensor R g) x2; rw [← novikovBaseChangeMap_naturality Γ g x2]; rfl

/-- The natural map from $A\dparenmult \otimes_A M$ to
$M\dparenmult$ is a linear isomorphism when $M$ is finitely presented. -/
noncomputable def novikovModule_base_change_equiv [Module.FinitePresentation A M] :
    (NovikovSeries Γ ι A ⊗[A] M) ≃ₗ[NovikovSeries Γ ι A] NovikovSeries Γ ι M :=
  LinearEquiv.ofBijective (novikovBaseChangeMap Γ) (novikovBaseChangeMap_bijective Γ)

end Novikov
