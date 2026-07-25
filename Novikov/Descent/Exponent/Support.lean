import Novikov.Descent.Exponent.Ring
import Novikov.Descent.Real

/-!
# Exponent support of a real trivialization

This file begins the descent of a real-exponent trivialization to an arbitrary
additive exponent submonoid.  It associates a real-exponent, module-valued
Novikov series to each element of the original descent datum and records its
basic algebraic properties.
-/

namespace Novikov.Descent

open CategoryTheory Novikov TensorProduct
open Novikov.Descent.Abstract Novikov.Miscellany

variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ]
variable {Γ : S} {A : Type*} [CommRing A]

/-- The real-exponent, `P`-valued series obtained by trivializing `m` after
extension of exponents. -/
noncomputable def realTrivializedSeries
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (m : M.M) : NovikovSeries (⊤ : AddSubgroup ℝ) Unit P.M := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  exact novikovModule_base_change_equiv
    (A := A) (M := P.M) (ι := Unit) (⊤ : AddSubgroup ℝ)
    (realConstantModuleEquiv P
      (e.hom.toLinearMap ((1 : D.R₁) ⊗ₜ[C.R₁] m)))

@[simp]
lemma realTrivializedSeries_zero
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    realTrivializedSeries M P e 0 = 0 := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  let b := realConstantModuleEquiv P
  let N := novikovModule_base_change_equiv
    (A := A) (M := P.M) (ι := Unit) (⊤ : AddSubgroup ℝ)
  rw [realTrivializedSeries]
  rw [TensorProduct.tmul_zero]
  change N (b (e.hom.toLinearMap 0)) = 0
  rw [e.hom.toLinearMap.map_zero, b.map_zero, N.map_zero]

@[simp]
lemma realTrivializedSeries_add
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (m n : M.M) :
    realTrivializedSeries M P e (m + n) =
      realTrivializedSeries M P e m + realTrivializedSeries M P e n := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  let b := realConstantModuleEquiv P
  let N := novikovModule_base_change_equiv
    (A := A) (M := P.M) (ι := Unit) (⊤ : AddSubgroup ℝ)
  rw [realTrivializedSeries, realTrivializedSeries, realTrivializedSeries]
  rw [TensorProduct.tmul_add]
  change N (b (e.hom.toLinearMap (_ + _))) =
    N (b (e.hom.toLinearMap _)) + N (b (e.hom.toLinearMap _))
  rw [e.hom.toLinearMap.map_add, b.map_add, N.map_add]

lemma realTrivializedSeries_smul
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (a : (novikovCosimplicialRing Γ A).R₁) (m : M.M) :
    realTrivializedSeries M P e (a • m) =
      extendExponents Γ a • realTrivializedSeries M P e m := by
  simp only [realTrivializedSeries]
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  have htmul : (1 : D.R₁) ⊗ₜ[C.R₁] (a • m) =
      F.f₁ a • ((1 : D.R₁) ⊗ₜ[C.R₁] m) := by
    rw [TensorProduct.tmul_smul]
    change F.f₁ a • ((1 : D.R₁) ⊗ₜ[C.R₁] m) =
      F.f₁ a • ((1 : D.R₁) ⊗ₜ[C.R₁] m)
    rfl
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  let b := realConstantModuleEquiv P
  let N := novikovModule_base_change_equiv
    (A := A) (M := P.M) (ι := Unit) (⊤ : AddSubgroup ℝ)
  let targetMod : Module D.R₁
      (NovikovSeries (⊤ : AddSubgroup ℝ) Unit P.M) := by
    change Module (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) Unit P.M)
    infer_instance
  letI : Module D.R₁ (NovikovSeries (⊤ : AddSubgroup ℝ) Unit P.M) := targetMod
  rw [htmul]
  change N (b (e.hom.toLinearMap (F.f₁ a • _))) =
    F.f₁ a • N (b (e.hom.toLinearMap _))
  rw [e.hom.toLinearMap.map_smul]
  have hb := b.map_smul (F.f₁ a)
    (e.hom.toLinearMap ((1 : D.R₁) ⊗ₜ[C.R₁] m))
  erw [hb]
  exact N.map_smul (F.f₁ a)
    (b (e.hom.toLinearMap ((1 : D.R₁) ⊗ₜ[C.R₁] m)))

lemma realTrivializedSeries_injective
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    Function.Injective (realTrivializedSeries M P e) := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  let b := realConstantModuleEquiv P
  let N := novikovModule_base_change_equiv
    (A := A) (M := P.M) (ι := Unit) (⊤ : AddSubgroup ℝ)
  intro m n h
  apply one_tmul_injective_of_injective (exponentInclusionCHom_f₁_injective Γ A)
  apply (DescentDatum.isoLinearEquiv e).injective
  apply b.injective
  apply N.injective
  exact h

private noncomputable def realConstantPullbackSeriesEquiv₁
    (P : FiniteProjectiveModule A) := by
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  exact (realConstantPullbackπ₁Equiv P).trans
    (novikovModule_base_change_equiv
      (A := A) (M := P.M) (ι := Fin 2) (⊤ : AddSubgroup ℝ))

private noncomputable def realConstantPullbackSeriesEquiv₂
    (P : FiniteProjectiveModule A) := by
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  exact (realConstantPullbackπ₂Equiv P).trans
    (novikovModule_base_change_equiv
      (A := A) (M := P.M) (ι := Fin 2) (⊤ : AddSubgroup ℝ))

private lemma realConstantPullbackSeriesEquiv_commute_φ
    (P : FiniteProjectiveModule A)
    (z : π₁s (realC A)
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M) :
    realConstantPullbackSeriesEquiv₂ P
        (((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).φ z) =
      realConstantPullbackSeriesEquiv₁ P z := by
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  let N := novikovModule_base_change_equiv
    (A := A) (M := P.M) (ι := Fin 2) (⊤ : AddSubgroup ℝ)
  have h := realConstantPullbackEquiv_commute_φ P z
  unfold realConstantPullbackSeriesEquiv₂ realConstantPullbackSeriesEquiv₁
  simp only [LinearEquiv.trans_apply]
  exact congrArg N h

private noncomputable def firstRealizationInput
    (M : NovikovDescentDatum Γ A)
    (z : π₁s (novikovCosimplicialRing Γ A) M.M) :
    π₁s (realC A) (M.baseChange (exponentInclusionCHom Γ A)).M := by
  let C := novikovCosimplicialRing Γ A
  let D := realC A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  exact (F.pullbackBaseChangeπ₁ M.M).symm
    ((1 : D.R₂) ⊗ₜ[C.R₂] z)

private noncomputable def secondRealizationInput
    (M : NovikovDescentDatum Γ A)
    (z : π₂s (novikovCosimplicialRing Γ A) M.M) :
    π₂s (realC A) (M.baseChange (exponentInclusionCHom Γ A)).M := by
  let C := novikovCosimplicialRing Γ A
  let D := realC A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  exact (F.pullbackBaseChangeπ₂ M.M).symm
    ((1 : D.R₂) ⊗ₜ[C.R₂] z)

private lemma realizationInputs_commute_φ
    (M : NovikovDescentDatum Γ A)
    (z : π₁s (novikovCosimplicialRing Γ A) M.M) :
    (M.baseChange (exponentInclusionCHom Γ A)).φ
        (firstRealizationInput M z) =
      secondRealizationInput M (M.φ z) := by
  let C := novikovCosimplicialRing Γ A
  let D := realC A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
  change F.baseChangePhi M
      ((F.pullbackBaseChangeπ₁ M.M).symm
        ((1 : D.R₂) ⊗ₜ[C.R₂] z)) =
    (F.pullbackBaseChangeπ₂ M.M).symm
      ((1 : D.R₂) ⊗ₜ[C.R₂] (M.φ z))
  apply (F.pullbackBaseChangeπ₂ M.M).injective
  simp only [CosimplicialRingHom.baseChangePhi, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.baseChange_tmul]

private noncomputable def firstRealizationCoordinate
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (u : π₁s (realC A) (M.baseChange (exponentInclusionCHom Γ A)).M) :
    NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) P.M := by
  let D := realC A
  letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
  exact realConstantPullbackSeriesEquiv₁ P
    (Novikov.Miscellany.baseChangeMap D.π₁ e.hom.toLinearMap u)

private noncomputable def secondRealizationCoordinate
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (u : π₂s (realC A) (M.baseChange (exponentInclusionCHom Γ A)).M) :
    NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) P.M := by
  let D := realC A
  letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
  exact realConstantPullbackSeriesEquiv₂ P
    (Novikov.Miscellany.baseChangeMap D.π₂ e.hom.toLinearMap u)

private lemma realTrivializationIso_commute_φ_apply
    (M N : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (e : M ≅ N) (u : π₁s (realC A) M.M) :
    N.φ
        ((letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
          LinearMap.baseChange (realC A).R₂ e.hom.toLinearMap) u) =
      (letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
       LinearMap.baseChange (realC A).R₂ e.hom.toLinearMap) (M.φ u) := by
  have h := LinearMap.congr_fun e.hom.commute_φ u
  simpa only [LinearMap.comp_apply] using h

private lemma realizationCoordinates_commute_φ
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (u : π₁s (realC A) (M.baseChange (exponentInclusionCHom Γ A)).M) :
    secondRealizationCoordinate M P e
        ((M.baseChange (exponentInclusionCHom Γ A)).φ u) =
      firstRealizationCoordinate M P e u := by
  let X := M.baseChange (exponentInclusionCHom Γ A)
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  have h := realTrivializationIso_commute_φ_apply X K e u
  unfold secondRealizationCoordinate firstRealizationCoordinate
  dsimp only
  simp only [Novikov.Miscellany.baseChangeMap]
  rw [← h]
  exact realConstantPullbackSeriesEquiv_commute_φ P _

private noncomputable def firstRealizationFun
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (z : π₁s (novikovCosimplicialRing Γ A) M.M) :
    NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) P.M := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
  exact realConstantPullbackSeriesEquiv₁ P
    (Novikov.Miscellany.baseChangeMap D.π₁ e.hom.toLinearMap
      ((F.pullbackBaseChangeπ₁ M.M).symm
        ((1 : D.R₂) ⊗ₜ[C.R₂] z)))

private lemma firstRealizationFun_eq_coordinate
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (z : π₁s (novikovCosimplicialRing Γ A) M.M) :
    firstRealizationFun M P e z =
      firstRealizationCoordinate M P e (firstRealizationInput M z) := rfl

/-- Realize the first pullback of `M` as a two-variable, real-exponent,
`P`-valued Novikov series. -/
noncomputable def firstRealization
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    π₁s (novikovCosimplicialRing Γ A) M.M →+
      NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) P.M := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
  let oneTmul : π₁s C M.M →+ D.R₂ ⊗[C.R₂] (π₁s C M.M) :=
    { toFun := fun z => (1 : D.R₂) ⊗ₜ[C.R₂] z
      map_zero' := by simp
      map_add' := by intro x y; rw [TensorProduct.tmul_add] }
  let pipeline :=
    (realConstantPullbackSeriesEquiv₁ P).toLinearMap.toAddMonoidHom.comp
      ((Novikov.Miscellany.baseChangeMap D.π₁ e.hom.toLinearMap).toAddMonoidHom.comp
        ((F.pullbackBaseChangeπ₁ M.M).symm.toLinearMap.toAddMonoidHom.comp oneTmul))
  exact
    { toFun := firstRealizationFun M P e
      map_zero' := pipeline.map_zero
      map_add' := pipeline.map_add }

/-- Formula for the first realization on a pure tensor. -/
lemma firstRealization_tmul
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (a : (novikovCosimplicialRing Γ A).R₂) (m : M.M) :
    firstRealization M P e
        (by
          let C := novikovCosimplicialRing Γ A
          letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
          letI : Module C.R₁ C.R₂ := Algebra.toModule
          change C.R₂ ⊗[C.R₁] M.M
          exact a ⊗ₜ[C.R₁] m) =
      extendExponents Γ a •
        substitute (fun _ : Unit => (0 : Fin 2))
          (realTrivializedSeries M P e m) := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
  letI : Algebra D.R₁
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := D.π₁.toAlgebra
  letI : Module D.R₁
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := Algebra.toModule
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  have hinner : (a ⊗ₜ[C.R₁] m : C.R₂ ⊗[C.R₁] M.M) =
      a • ((1 : C.R₂) ⊗ₜ[C.R₁] m) := by
    simpa only [smul_eq_mul, mul_one] using
      (TensorProduct.smul_tmul' (R := C.R₁) a (1 : C.R₂) m).symm
  have hone :
      (1 : D.R₂) ⊗ₜ[C.R₂] (a ⊗ₜ[C.R₁] m) =
        F.f₂ a ⊗ₜ[C.R₂] ((1 : C.R₂) ⊗ₜ[C.R₁] m) := by
    rw [hinner, TensorProduct.tmul_smul]
    change F.f₂ a • ((1 : D.R₂) ⊗ₜ[C.R₂]
        ((1 : C.R₂) ⊗ₜ[C.R₁] m)) =
      F.f₂ a ⊗ₜ[C.R₂] ((1 : C.R₂) ⊗ₜ[C.R₁] m)
    simpa only [smul_eq_mul, mul_one] using
      (TensorProduct.smul_tmul' (R := C.R₂) (F.f₂ a) (1 : D.R₂)
        ((1 : C.R₂) ⊗ₜ[C.R₁] m))
  dsimp only [firstRealization]
  change firstRealizationFun M P e (a ⊗ₜ[C.R₁] m) = _
  unfold firstRealizationFun
  dsimp only [id_eq]
  rw [hone]
  erw [F.pullbackBaseChangeπ₁_symm_tmul]
  erw [Novikov.Miscellany.baseChangeMap_tmul]
  unfold realConstantPullbackSeriesEquiv₁
  simp only [LinearEquiv.trans_apply]
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  letI : Module D.R₁
      (baseChange_along (algebraMapNovikov : A →+* D.R₁) P.M) := K.instModule
  let s : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A := F.f₂ a
  let x : K.M := e.hom.toLinearMap ((1 : D.R₁) ⊗ₜ[C.R₁] m)
  let N := novikovModule_base_change_equiv
    (A := A) (M := P.M) (ι := Fin 2) (⊤ : AddSubgroup ℝ)
  change N (realConstantPullbackπ₁Equiv P
    ((show D.R₂ from s) ⊗ₜ[D.R₁] x)) = _
  rw [realConstantPullbackπ₁Equiv_tmul_right]
  rw [N.map_smul]
  change s • N
    (algebraTensorMap
      (substituteAlgHom (Γ := (⊤ : AddSubgroup ℝ))
        (A := A) (fun _ : Unit => (0 : Fin 2))) P.M
      (realConstantModuleEquiv P x)) = _
  rw [novikovModule_base_change_equiv_substitute]
  rfl

private noncomputable def secondRealizationFun
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (z : π₂s (novikovCosimplicialRing Γ A) M.M) :
    NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) P.M := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
  exact realConstantPullbackSeriesEquiv₂ P
    (Novikov.Miscellany.baseChangeMap D.π₂ e.hom.toLinearMap
      ((F.pullbackBaseChangeπ₂ M.M).symm
        ((1 : D.R₂) ⊗ₜ[C.R₂] z)))

private lemma secondRealizationFun_eq_coordinate
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (z : π₂s (novikovCosimplicialRing Γ A) M.M) :
    secondRealizationFun M P e z =
      secondRealizationCoordinate M P e (secondRealizationInput M z) := rfl

/-- Realize the second pullback of `M` as a two-variable, real-exponent,
`P`-valued Novikov series. -/
noncomputable def secondRealization
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    π₂s (novikovCosimplicialRing Γ A) M.M →+
      NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) P.M := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
  let oneTmul : π₂s C M.M →+ D.R₂ ⊗[C.R₂] (π₂s C M.M) :=
    { toFun := fun z => (1 : D.R₂) ⊗ₜ[C.R₂] z
      map_zero' := by simp
      map_add' := by intro x y; rw [TensorProduct.tmul_add] }
  let pipeline :=
    (realConstantPullbackSeriesEquiv₂ P).toLinearMap.toAddMonoidHom.comp
      ((Novikov.Miscellany.baseChangeMap D.π₂ e.hom.toLinearMap).toAddMonoidHom.comp
        ((F.pullbackBaseChangeπ₂ M.M).symm.toLinearMap.toAddMonoidHom.comp oneTmul))
  exact
    { toFun := secondRealizationFun M P e
      map_zero' := pipeline.map_zero
      map_add' := pipeline.map_add }

/-- Formula for the second realization on a pure tensor. -/
lemma secondRealization_tmul
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (a : (novikovCosimplicialRing Γ A).R₂) (m : M.M) :
    secondRealization M P e
        (by
          let C := novikovCosimplicialRing Γ A
          letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
          letI : Module C.R₁ C.R₂ := Algebra.toModule
          change C.R₂ ⊗[C.R₁] M.M
          exact a ⊗ₜ[C.R₁] m) =
      extendExponents Γ a •
        substitute (fun _ : Unit => (1 : Fin 2))
          (realTrivializedSeries M P e m) := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
  letI : Algebra D.R₁
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := D.π₂.toAlgebra
  letI : Module D.R₁
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := Algebra.toModule
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  have hinner : (a ⊗ₜ[C.R₁] m : C.R₂ ⊗[C.R₁] M.M) =
      a • ((1 : C.R₂) ⊗ₜ[C.R₁] m) := by
    simpa only [smul_eq_mul, mul_one] using
      (TensorProduct.smul_tmul' (R := C.R₁) a (1 : C.R₂) m).symm
  have hone :
      (1 : D.R₂) ⊗ₜ[C.R₂] (a ⊗ₜ[C.R₁] m) =
        F.f₂ a ⊗ₜ[C.R₂] ((1 : C.R₂) ⊗ₜ[C.R₁] m) := by
    rw [hinner, TensorProduct.tmul_smul]
    change F.f₂ a • ((1 : D.R₂) ⊗ₜ[C.R₂]
        ((1 : C.R₂) ⊗ₜ[C.R₁] m)) =
      F.f₂ a ⊗ₜ[C.R₂] ((1 : C.R₂) ⊗ₜ[C.R₁] m)
    simpa only [smul_eq_mul, mul_one] using
      (TensorProduct.smul_tmul' (R := C.R₂) (F.f₂ a) (1 : D.R₂)
        ((1 : C.R₂) ⊗ₜ[C.R₁] m))
  dsimp only [secondRealization]
  change secondRealizationFun M P e (a ⊗ₜ[C.R₁] m) = _
  unfold secondRealizationFun
  dsimp only [id_eq]
  rw [hone]
  erw [F.pullbackBaseChangeπ₂_symm_tmul]
  erw [Novikov.Miscellany.baseChangeMap_tmul]
  unfold realConstantPullbackSeriesEquiv₂
  simp only [LinearEquiv.trans_apply]
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  letI : Module D.R₁
      (baseChange_along (algebraMapNovikov : A →+* D.R₁) P.M) := K.instModule
  let s : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A := F.f₂ a
  let x : K.M := e.hom.toLinearMap ((1 : D.R₁) ⊗ₜ[C.R₁] m)
  let N := novikovModule_base_change_equiv
    (A := A) (M := P.M) (ι := Fin 2) (⊤ : AddSubgroup ℝ)
  change N (realConstantPullbackπ₂Equiv P
    ((show D.R₂ from s) ⊗ₜ[D.R₁] x)) = _
  rw [realConstantPullbackπ₂Equiv_tmul_right]
  rw [N.map_smul]
  change s • N
    (algebraTensorMap
      (substituteAlgHom (Γ := (⊤ : AddSubgroup ℝ))
        (A := A) (fun _ : Unit => (1 : Fin 2))) P.M
      (realConstantModuleEquiv P x)) = _
  rw [novikovModule_base_change_equiv_substitute]
  rfl

/-- The second realization remains injective after extending exponents. -/
lemma secondRealization_injective
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    Function.Injective (secondRealization M P e) := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
  letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
  letI : Module.Projective C.R₂ (π₂s C M.M) :=
    Novikov.Miscellany.baseChange_projective M.M
  intro x y h
  dsimp only [secondRealization] at h
  change realConstantPullbackSeriesEquiv₂ P
      (Novikov.Miscellany.baseChangeMap D.π₂ e.hom.toLinearMap
        ((F.pullbackBaseChangeπ₂ M.M).symm
          ((1 : D.R₂) ⊗ₜ[C.R₂] x))) =
    realConstantPullbackSeriesEquiv₂ P
      (Novikov.Miscellany.baseChangeMap D.π₂ e.hom.toLinearMap
        ((F.pullbackBaseChangeπ₂ M.M).symm
          ((1 : D.R₂) ⊗ₜ[C.R₂] y))) at h
  have h₁ := (realConstantPullbackSeriesEquiv₂ P).injective h
  let X := M.baseChange F
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  letI : Module D.R₁ X.M := X.instModule
  letI : Module D.R₁ K.M := K.instModule
  let X₂ := π₂s D X.M
  let K₂ := π₂s D K.M
  let x₂Mod : Module D.R₂ X₂ := by
    letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    exact inferInstance
  let k₂Mod : Module D.R₂ K₂ := by
    letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    exact inferInstance
  letI : Module D.R₂ X₂ := x₂Mod
  letI : Module D.R₂ K₂ := k₂Mod
  let e₂ := LinearEquiv.baseChange D.R₁ D.R₂ X.M K.M
    (DescentDatum.isoLinearEquiv e)
  change e₂ ((F.pullbackBaseChangeπ₂ M.M).symm
      ((1 : D.R₂) ⊗ₜ[C.R₂] x)) =
    e₂ ((F.pullbackBaseChangeπ₂ M.M).symm
      ((1 : D.R₂) ⊗ₜ[C.R₂] y)) at h₁
  have h₂ := e₂.injective h₁
  have h₃ := (F.pullbackBaseChangeπ₂ M.M).symm.injective h₂
  exact one_tmul_injective_of_injective
    (exponentInclusionCHom_f₂_injective Γ A) h₃

/-- The two realization maps identify elements related by the descent
isomorphism of `M`. -/
lemma realizations_commute_φ
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (z : π₁s (novikovCosimplicialRing Γ A) M.M) :
    secondRealization M P e (M.φ z) = firstRealization M P e z := by
  dsimp only [secondRealization, firstRealization]
  change secondRealizationFun M P e (M.φ z) = firstRealizationFun M P e z
  rw [secondRealizationFun_eq_coordinate, firstRealizationFun_eq_coordinate,
    ← realizationInputs_commute_φ]
  exact realizationCoordinates_commute_φ M P e (firstRealizationInput M z)

/-- A two-variable real-exponent Novikov series has second-coordinate support
in `Γ`. -/
def HasSecondExponentSupport
    {M : Type*} [AddCommGroup M]
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) M) : Prop :=
  ∀ d, x.val d ≠ 0 → (d (1 : Fin 2) : ℝ) ∈ Γ

private lemma hasSecondExponentSupport_substitute_first
    {M : Type*} [AddCommGroup M]
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) Unit M) :
    HasSecondExponentSupport (Γ := Γ)
      (substitute (fun _ : Unit => (0 : Fin 2)) x) := by
  intro d hd
  change substituteFun (fun _ : Unit => (0 : Fin 2)) x d ≠ 0 at hd
  unfold substituteFun at hd
  obtain ⟨g, hg, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  rw [mem_finite_substitution_support] at hg
  have hcoord := congrFun hg.1 (1 : Fin 2)
  have hzero :
      pushExponents (fun _ : Unit => (0 : Fin 2)) g (1 : Fin 2) = 0 := by
    simp [pushExponents]
  have hdZero : d (1 : Fin 2) = 0 := hcoord.symm.trans hzero
  rw [hdZero]
  exact zero_mem Γ

private lemma hasSecondExponentSupport_smul
    {M : Type*} [AddCommGroup M] [Module A M]
    (f : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) M)
    (hf : HasExponentSupport Γ f)
    (hx : HasSecondExponentSupport (Γ := Γ) x) :
    HasSecondExponentSupport (Γ := Γ) (f • x) := by
  intro d hd
  have hdSupport : d ∈
      (novikovSeriesMul f x smulAddHom).support := by
    rw [NovikovSeries.mem_support]
    exact hd
  have hdSum := support_mul_subset f x smulAddHom hdSupport
  rw [Set.mem_add] at hdSum
  obtain ⟨d₁, hd₁, d₂, hd₂, hadd⟩ := hdSum
  have hd₁ne : f.val d₁ ≠ 0 := by
    simpa only [NovikovSeries.mem_support] using hd₁
  have hd₂ne : x.val d₂ ≠ 0 := by
    simpa only [NovikovSeries.mem_support] using hd₂
  have hcoord :
      (d₁ (1 : Fin 2) : ℝ) + (d₂ (1 : Fin 2) : ℝ) =
        (d (1 : Fin 2) : ℝ) := by
    exact congrArg (fun z : (⊤ : AddSubgroup ℝ) => (z : ℝ))
      (congrFun hadd (1 : Fin 2))
  rw [← hcoord]
  exact add_mem (hf d₁ hd₁ne (1 : Fin 2)) (hx d₂ hd₂ne)

/-- Every series in the image of the first realization has its second exponent
coordinate in `Γ`. -/
lemma firstRealization_has_second_exponent_support
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (z : π₁s (novikovCosimplicialRing Γ A) M.M) :
    HasSecondExponentSupport (Γ := Γ) (firstRealization M P e z) := by
  let C := novikovCosimplicialRing Γ A
  letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
  induction z using TensorProduct.induction_on with
  | zero =>
      intro d hd
      rw [map_zero] at hd
      exact (hd rfl).elim
  | add x y hx hy =>
      intro d hd
      rw [map_add] at hd
      change (firstRealization M P e x).val d +
        (firstRealization M P e y).val d ≠ 0 at hd
      by_cases hxd : (firstRealization M P e x).val d = 0
      · apply hy d
        intro hyd
        apply hd
        rw [hxd, hyd, add_zero]
      · exact hx d hxd
  | tmul a m =>
      have hformula := firstRealization_tmul M P e a m
      dsimp only [id_eq] at hformula
      rw [hformula]
      exact hasSecondExponentSupport_smul
        (extendExponents Γ a)
        (substitute (fun _ : Unit => (0 : Fin 2))
          (realTrivializedSeries M P e m))
        (hasExponentSupport_extendExponents Γ a)
        (hasSecondExponentSupport_substitute_first
          (Γ := Γ) (realTrivializedSeries M P e m))

/-- Every real-trivialized series has exponent support in `Γ`. -/
lemma realTrivializedSeries_has_exponent_support
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (m : M.M) :
    HasExponentSupport Γ (realTrivializedSeries M P e m) := by
  let C := novikovCosimplicialRing Γ A
  letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
  let w : π₂s C M.M := (1 : C.R₂) ⊗ₜ[C.R₁] m
  let z : π₁s C M.M := M.φ.symm w
  have hsupport := firstRealization_has_second_exponent_support M P e z
  have hcompare := realizations_commute_φ M P e z
  have hφ : M.φ z = w := M.φ.apply_symm_apply w
  rw [hφ] at hcompare
  have hformula := secondRealization_tmul M P e (1 : C.R₂) m
  change secondRealization M P e w = _ at hformula
  have hone : extendExponents Γ (1 : C.R₂) =
      (1 : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := by
    exact extendExponents_one Γ
  rw [hone, one_smul] at hformula
  have hsubSupport : HasSecondExponentSupport (Γ := Γ)
      (substitute (fun _ : Unit => (1 : Fin 2))
        (realTrivializedSeries M P e m)) := by
    rw [← hformula, hcompare]
    exact hsupport
  intro d hd i
  cases i
  let d₂ : Fin 2 → (⊤ : AddSubgroup ℝ) := fun j =>
    if j = (1 : Fin 2) then d () else 0
  have hd₂val :
      (substitute (fun _ : Unit => (1 : Fin 2))
        (realTrivializedSeries M P e m)).val d₂ =
        (realTrivializedSeries M P e m).val d := by
    rw [substitute_const_apply]
    simp [d₂]
  have hd₂ := hsubSupport d₂ (by rw [hd₂val]; exact hd)
  simpa [d₂] using hd₂

end Novikov.Descent
