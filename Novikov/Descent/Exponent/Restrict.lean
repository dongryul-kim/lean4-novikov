import Novikov.Descent.Exponent.Support

/-!
# Restricting a real Novikov trivialization

This file restricts the real-exponent, module-valued series attached to a real
trivialization back to the original exponent monoid.  Since unrestricted
coefficient restriction is not linear for a general additive submonoid, all
linearity proofs are reflected through injective extension of exponents.
-/

namespace Novikov.Descent

open CategoryTheory Novikov TensorProduct
open Novikov.Descent.Abstract Novikov.Miscellany

variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ]
variable {Γ : S} {A : Type*} [CommRing A]

/-- Restrict the real-trivialized series of an element back to `Γ`. -/
noncomputable def restrictedTrivializedSeries
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (m : M.M) : NovikovSeries Γ Unit P.M :=
  restrictExponents Γ (realTrivializedSeries M P e m)

@[simp]
lemma restrictedTrivializedSeries_zero
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    restrictedTrivializedSeries M P e 0 = 0 := by
  rw [restrictedTrivializedSeries, realTrivializedSeries_zero,
    restrictExponents_zero]

lemma restrictedTrivializedSeries_add
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (m n : M.M) :
    restrictedTrivializedSeries M P e (m + n) =
      restrictedTrivializedSeries M P e m +
        restrictedTrivializedSeries M P e n := by
  rw [restrictedTrivializedSeries, realTrivializedSeries_add,
    restrictExponents_add]
  rfl

/-- Extending a restricted trivialized series recovers the original real
series. -/
lemma extendExponents_restrictedTrivializedSeries
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (m : M.M) :
    extendExponents Γ (restrictedTrivializedSeries M P e m) =
      realTrivializedSeries M P e m := by
  exact extendExponents_restrictExponents Γ _
    (realTrivializedSeries_has_exponent_support M P e m)

lemma restrictedTrivializedSeries_smul
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (a : (novikovCosimplicialRing Γ A).R₁) (m : M.M) :
    restrictedTrivializedSeries M P e (a • m) =
      (show NovikovSeries Γ Unit A from a) •
        restrictedTrivializedSeries M P e m := by
  apply extendExponents_injective Γ
  rw [extendExponents_restrictedTrivializedSeries, extendExponents_smul,
    extendExponents_restrictedTrivializedSeries]
  exact realTrivializedSeries_smul M P e a m

lemma restrictedTrivializedSeries_injective
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    Function.Injective (restrictedTrivializedSeries M P e) := by
  intro m n h
  apply realTrivializedSeries_injective M P e
  rw [← extendExponents_restrictedTrivializedSeries M P e m,
    ← extendExponents_restrictedTrivializedSeries M P e n, h]

private noncomputable def exponentConstantCancelHom
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : NovikovSeries Γ ι A →+* NovikovSeries Γ κ A)
    (hf : f.comp algebraMapNovikov = algebraMapNovikov)
    (P : FiniteProjectiveModule A) :
    let R := NovikovSeries Γ ι A
    let T := NovikovSeries Γ κ A
    letI : Algebra A R := algebraMapNovikov.toAlgebra
    letI : Algebra R T := f.toAlgebra
    (T ⊗[R] baseChange_along
      (algebraMapNovikov : A →+* R) P.M) ≃ₗ[T] T ⊗[A] P.M := by
  let R := NovikovSeries Γ ι A
  let T := NovikovSeries Γ κ A
  let aR : Algebra A R := algebraMapNovikov.toAlgebra
  let aT : Algebra A T := inferInstance
  letI : Algebra A R := aR
  letI : SMul A R := aR.toSMul
  letI : Module A R := aR.toModule
  letI : Algebra A T := aT
  letI : SMul A T := aT.toSMul
  letI : Module A T := aT.toModule
  let rTAlg : Algebra R T := f.toAlgebra
  letI : Algebra R T := rTAlg
  letI : SMul R T := rTAlg.toSMul
  letI : Module R T := rTAlg.toModule
  letI : IsScalarTower A R T :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (RingHom.congr_fun hf a).symm)
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T P.M

private noncomputable def exponentConstantModuleEquiv
    (P : FiniteProjectiveModule A) :
    let R := NovikovSeries Γ Unit A
    let K := (vectToNovikovDescent Γ A).obj P
    let Y := R ⊗[A] P.M
    let yAdd : AddCommGroup Y := inferInstance
    let yMod : Module R Y := inferInstance
    letI : AddCommGroup K.M := K.instAddCommGroup
    letI : Module R K.M := K.instModule
    letI : AddCommGroup Y := yAdd
    letI : Module R Y := yMod
    K.M ≃ₗ[R] Y := by
  let R := NovikovSeries Γ Unit A
  let f : R →+* R := RingHom.id R
  have hf : f.comp (algebraMapNovikov : A →+* R) = algebraMapNovikov := by
    rfl
  let c := exponentConstantCancelHom (Γ := Γ) f hf P
  let K := (vectToNovikovDescent Γ A).obj P
  let X := K.M
  let xAdd : AddCommGroup X := K.instAddCommGroup
  let xMod : Module R X := K.instModule
  letI : AddCommGroup X := xAdd
  letI : Module R X := xMod
  let l : (letI : Algebra R R := f.toAlgebra; R ⊗[R] X) ≃ₗ[R] X :=
    TensorProduct.lid R X
  exact l.symm.trans c

private noncomputable def exponentConstantSeriesEquiv
    (P : FiniteProjectiveModule A) := by
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  exact (exponentConstantModuleEquiv (Γ := Γ) P).trans
    (novikovModule_base_change_equiv
      (A := A) (M := P.M) (ι := Unit) Γ)

private theorem exponentConstantModuleEquiv_tmul
    (P : FiniteProjectiveModule A) (r : NovikovSeries Γ Unit A) (p : P.M) :
    exponentConstantModuleEquiv (Γ := Γ) P
        (by
          let E := novikovExtendedCosimplicialRing Γ A
          letI : Module E.R₀ P.M := P.instModule
          letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
          exact (show E.R₁ from r) ⊗ₜ[E.R₀] p) =
      r ⊗ₜ[A] p := by
  simp only [Lean.Elab.WF.paramLet]
  change (r * 1) ⊗ₜ[A] p = r ⊗ₜ[A] p
  rw [mul_one]

private theorem realConstantModuleEquiv_tmul_restrict
    (P : FiniteProjectiveModule A)
    (r : NovikovSeries (⊤ : AddSubgroup ℝ) Unit A) (p : P.M) :
    realConstantModuleEquiv P
        (by
          let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A
          letI : Module E.R₀ P.M := P.instModule
          letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
          exact (show E.R₁ from r) ⊗ₜ[E.R₀] p) =
      r ⊗ₜ[A] p := by
  simp only [Lean.Elab.WF.paramLet]
  change (r * 1) ⊗ₜ[A] p = r ⊗ₜ[A] p
  rw [mul_one]

private theorem exponentConstantSeriesEquiv_tmul
    (P : FiniteProjectiveModule A) (r : NovikovSeries Γ Unit A) (p : P.M) :
    exponentConstantSeriesEquiv (Γ := Γ) P
        (by
          let E := novikovExtendedCosimplicialRing Γ A
          letI : Module E.R₀ P.M := P.instModule
          letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
          exact (show E.R₁ from r) ⊗ₜ[E.R₀] p) =
      r • novikovMonomial p 0 := by
  unfold exponentConstantSeriesEquiv
  simp only [LinearEquiv.trans_apply]
  rw [exponentConstantModuleEquiv_tmul]
  rfl

private noncomputable def realConstantSeriesCoordinate
    (P : FiniteProjectiveModule A) :
    ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M →+
      NovikovSeries (⊤ : AddSubgroup ℝ) Unit P.M := by
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  let kMod : Module (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A) K.M :=
    K.instModule
  letI : Module (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A) K.M := kMod
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  exact (novikovModule_base_change_equiv
    (A := A) (M := P.M) (ι := Unit)
      (⊤ : AddSubgroup ℝ)).toLinearMap.toAddMonoidHom.comp
        (realConstantModuleEquiv P).toLinearMap.toAddMonoidHom

private lemma realConstantSeriesCoordinate_apply
    (P : FiniteProjectiveModule A)
    (z : ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M) :
    realConstantSeriesCoordinate P z =
      (by
        let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
        let kMod : Module (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A) K.M :=
          K.instModule
        letI : Module (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A) K.M := kMod
        haveI : Module.FinitePresentation A P.M :=
          Module.finitePresentation_of_projective A P.M
        exact novikovModule_base_change_equiv
          (A := A) (M := P.M) (ι := Unit) (⊤ : AddSubgroup ℝ)
          (realConstantModuleEquiv P z)) := rfl

private lemma realConstantSeriesCoordinate_injective
    (P : FiniteProjectiveModule A) :
    Function.Injective (realConstantSeriesCoordinate P) := by
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  let kMod : Module (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A) K.M :=
    K.instModule
  letI : Module (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A) K.M := kMod
  haveI : Module.FinitePresentation A P.M :=
    Module.finitePresentation_of_projective A P.M
  let N := novikovModule_base_change_equiv
    (A := A) (M := P.M) (ι := Unit) (⊤ : AddSubgroup ℝ)
  let b := realConstantModuleEquiv P
  exact N.injective.comp b.injective

private theorem realConstantSeriesCoordinate_tmul
    (P : FiniteProjectiveModule A)
    (r : NovikovSeries (⊤ : AddSubgroup ℝ) Unit A) (p : P.M) :
    realConstantSeriesCoordinate P
        (by
          let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A
          letI : Module E.R₀ P.M := P.instModule
          letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
          exact (show E.R₁ from r) ⊗ₜ[E.R₀] p) =
      r • novikovMonomial p 0 := by
  rw [realConstantSeriesCoordinate_apply]
  rw [realConstantModuleEquiv_tmul_restrict]
  rfl

private lemma exponentConstantBaseChange_series_tmul
    (P : FiniteProjectiveModule A) (r : NovikovSeries Γ Unit A) (p : P.M) :
    let C := novikovCosimplicialRing Γ A
    let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
    let F := exponentInclusionCHom Γ A
    letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
    realConstantSeriesCoordinate P
        ((exponentConstantBaseChangeIso Γ A P).hom.toLinearMap
          ((1 : D.R₁) ⊗ₜ[C.R₁]
            (by
              let E := novikovExtendedCosimplicialRing Γ A
              letI : Module E.R₀ P.M := P.instModule
              letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
              exact (show E.R₁ from r) ⊗ₜ[E.R₀] p))) =
      extendExponents Γ (r • novikovMonomial p 0) := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  have hcomp :
      (exponentConstantBaseChangeIso Γ A P).hom.toLinearMap
          ((1 : D.R₁) ⊗ₜ[C.R₁]
            (by
              let E := novikovExtendedCosimplicialRing Γ A
              letI : Module E.R₀ P.M := P.instModule
              letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
              exact (show E.R₁ from r) ⊗ₜ[E.R₀] p)) =
        (by
          let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A
          letI : Module E.R₀ P.M := P.instModule
          letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
          exact ((show E.R₁ from extendExponents Γ r) * (1 : E.R₁))
            ⊗ₜ[E.R₀] p) := by
    exact exponentConstantBaseChangeIso_hom_tmul Γ A P (1 : D.R₁) r p
  dsimp only
  rw [hcomp, realConstantSeriesCoordinate_tmul]
  change (extendExponents Γ r * 1) • novikovMonomial p 0 =
    extendExponents Γ (r • novikovMonomial p 0)
  rw [mul_one, extendExponents_smul, extendExponents_novikovMonomial,
    includeExponent_zero]

private lemma exponentConstantBaseChange_series
    (P : FiniteProjectiveModule A)
    (x : ((vectToNovikovDescent Γ A).obj P).M) :
    let C := novikovCosimplicialRing Γ A
    let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
    let F := exponentInclusionCHom Γ A
    letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
    realConstantSeriesCoordinate P
        ((exponentConstantBaseChangeIso Γ A P).hom.toLinearMap
          ((1 : D.R₁) ⊗ₜ[C.R₁] x)) =
      extendExponents Γ (exponentConstantSeriesEquiv (Γ := Γ) P x) := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  let K := (vectToNovikovDescent Γ A).obj P
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  let kMod : Module (NovikovSeries Γ Unit A) K.M := K.instModule
  letI : Module (NovikovSeries Γ Unit A) K.M := kMod
  let a := exponentConstantModuleEquiv (Γ := Γ) P
  let oneTmul : K.M →+ D.R₁ ⊗[C.R₁] K.M :=
    { toFun := fun z => (1 : D.R₁) ⊗ₜ[C.R₁] z
      map_zero' := by simp
      map_add' := by intro u v; rw [TensorProduct.tmul_add] }
  let lhs : K.M →+ NovikovSeries (⊤ : AddSubgroup ℝ) Unit P.M :=
    (realConstantSeriesCoordinate P).comp
      ((exponentConstantBaseChangeIso Γ A P).hom.toLinearMap.toAddMonoidHom.comp
        oneTmul)
  let rhs : K.M →+ NovikovSeries (⊤ : AddSubgroup ℝ) Unit P.M :=
    (extendExponentsAddHom Γ).comp
      (exponentConstantSeriesEquiv (Γ := Γ) P).toLinearMap.toAddMonoidHom
  change lhs x = rhs x
  let lhs' := lhs.comp a.symm.toLinearMap.toAddMonoidHom
  let rhs' := rhs.comp a.symm.toLinearMap.toAddMonoidHom
  have hx : x = a.symm (a x) := (a.symm_apply_apply x).symm
  rw [hx]
  change lhs' (a x) = rhs' (a x)
  generalize a x = y
  induction y using TensorProduct.induction_on with
  | zero =>
      exact lhs'.map_zero.trans rhs'.map_zero.symm
  | add y₁ y₂ h₁ h₂ =>
      rw [lhs'.map_add, rhs'.map_add, h₁, h₂]
  | tmul r p =>
      dsimp only [lhs', rhs', lhs, rhs, AddMonoidHom.comp_apply, oneTmul]
      change realConstantSeriesCoordinate P
          ((exponentConstantBaseChangeIso Γ A P).hom.toLinearMap
            ((1 : D.R₁) ⊗ₜ[C.R₁] a.symm (r ⊗ₜ[A] p))) =
        extendExponents Γ
          (exponentConstantSeriesEquiv (Γ := Γ) P
            (a.symm (r ⊗ₜ[A] p)))
      have ha : a.symm (r ⊗ₜ[A] p) =
          (by
            let E := novikovExtendedCosimplicialRing Γ A
            letI : Module E.R₀ P.M := P.instModule
            letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
            exact (show E.R₁ from r) ⊗ₜ[E.R₀] p) := by
        apply a.injective
        rw [a.apply_symm_apply, exponentConstantModuleEquiv_tmul]
      rw [ha, exponentConstantSeriesEquiv_tmul]
      exact exponentConstantBaseChange_series_tmul P r p

/-- The underlying linear map obtained by restricting a real trivialization to
`Γ`. -/
noncomputable def restrictRealTrivializationLinearMap
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    M.M →ₗ[(novikovCosimplicialRing Γ A).R₁]
      ((vectToNovikovDescent Γ A).obj P).M := by
  let C := novikovCosimplicialRing Γ A
  let K := (vectToNovikovDescent Γ A).obj P
  let kMod : Module (NovikovSeries Γ Unit A) K.M := K.instModule
  letI : Module (NovikovSeries Γ Unit A) K.M := kMod
  let targetMod : Module C.R₁ (NovikovSeries Γ Unit P.M) := by
    change Module (NovikovSeries Γ Unit A) (NovikovSeries Γ Unit P.M)
    infer_instance
  letI : Module C.R₁ (NovikovSeries Γ Unit P.M) := targetMod
  let r : M.M →ₗ[C.R₁] NovikovSeries Γ Unit P.M :=
    { toFun := restrictedTrivializedSeries M P e
      map_add' := restrictedTrivializedSeries_add M P e
      map_smul' := restrictedTrivializedSeries_smul M P e }
  exact (exponentConstantSeriesEquiv (Γ := Γ) P).symm.toLinearMap.comp r

@[simp]
lemma restrictRealTrivializationLinearMap_apply
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (m : M.M) :
    restrictRealTrivializationLinearMap M P e m =
      (exponentConstantSeriesEquiv (Γ := Γ) P).symm
        (restrictedTrivializedSeries M P e m) := rfl

/-- On a canonical base-change tensor, the restricted map becomes the given
real trivialization after applying the constant-object comparison. -/
lemma restrictRealTrivializationLinearMap_baseChange_one_tmul
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (m : M.M) :
    let C := novikovCosimplicialRing Γ A
    let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
    let F := exponentInclusionCHom Γ A
    letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
    (exponentConstantBaseChangeIso Γ A P).hom.toLinearMap
        ((1 : D.R₁) ⊗ₜ[C.R₁]
          (restrictRealTrivializationLinearMap M P e m)) =
      e.hom.toLinearMap ((1 : D.R₁) ⊗ₜ[C.R₁] m) := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  apply realConstantSeriesCoordinate_injective P
  have h := exponentConstantBaseChange_series (Γ := Γ) P
    (restrictRealTrivializationLinearMap M P e m)
  dsimp only at h
  rw [restrictRealTrivializationLinearMap_apply,
    (exponentConstantSeriesEquiv (Γ := Γ) P).apply_symm_apply,
    extendExponents_restrictedTrivializedSeries] at h
  have hr : realConstantSeriesCoordinate P
      (e.hom.toLinearMap ((1 : D.R₁) ⊗ₜ[C.R₁] m)) =
      realTrivializedSeries M P e m := by
    rw [realConstantSeriesCoordinate_apply]
    rfl
  exact h.trans hr.symm

/-- After extending exponents and applying the constant-object comparison, the
restricted linear map is exactly the original real trivialization. -/
lemma restrictRealTrivializationLinearMap_baseChange
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    let C := novikovCosimplicialRing Γ A
    let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
    let F := exponentInclusionCHom Γ A
    letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
    (exponentConstantBaseChangeIso Γ A P).hom.toLinearMap.comp
        (LinearMap.baseChange D.R₁
          (restrictRealTrivializationLinearMap M P e)) =
      e.hom.toLinearMap := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, h₁, h₂]
  | tmul s m =>
      simp only [LinearMap.comp_apply]
      change (exponentConstantBaseChangeIso Γ A P).hom.toLinearMap
          ((LinearMap.baseChange D.R₁
            (restrictRealTrivializationLinearMap M P e))
              (s ⊗ₜ[C.R₁] m)) =
        e.hom.toLinearMap (s ⊗ₜ[C.R₁] m)
      have hbase :
          (LinearMap.baseChange D.R₁
              (restrictRealTrivializationLinearMap M P e))
              (s ⊗ₜ[C.R₁] m) =
            s ⊗ₜ[C.R₁] (restrictRealTrivializationLinearMap M P e m) :=
        LinearMap.baseChange_tmul
          (restrictRealTrivializationLinearMap M P e) s m
      rw [hbase]
      have hsTarget :
          (s ⊗ₜ[C.R₁] (restrictRealTrivializationLinearMap M P e m) :
              D.R₁ ⊗[C.R₁] ((vectToNovikovDescent Γ A).obj P).M) =
            s • ((1 : D.R₁) ⊗ₜ[C.R₁]
              (restrictRealTrivializationLinearMap M P e m)) := by
        simpa only [smul_eq_mul, mul_one] using
          (TensorProduct.smul_tmul' (R := C.R₁) s (1 : D.R₁)
            (restrictRealTrivializationLinearMap M P e m)).symm
      have hsSource :
          (s ⊗ₜ[C.R₁] m : D.R₁ ⊗[C.R₁] M.M) =
            s • ((1 : D.R₁) ⊗ₜ[C.R₁] m) := by
        simpa only [smul_eq_mul, mul_one] using
          (TensorProduct.smul_tmul' (R := C.R₁) s (1 : D.R₁) m).symm
      calc
        (exponentConstantBaseChangeIso Γ A P).hom.toLinearMap
              (s ⊗ₜ[C.R₁]
                (restrictRealTrivializationLinearMap M P e m)) =
            (exponentConstantBaseChangeIso Γ A P).hom.toLinearMap
              (s • ((1 : D.R₁) ⊗ₜ[C.R₁]
                (restrictRealTrivializationLinearMap M P e m))) :=
          congrArg _ hsTarget
        _ = s • (exponentConstantBaseChangeIso Γ A P).hom.toLinearMap
              ((1 : D.R₁) ⊗ₜ[C.R₁]
                (restrictRealTrivializationLinearMap M P e m)) :=
          (exponentConstantBaseChangeIso Γ A P).hom.toLinearMap.map_smul _ _
        _ = s • e.hom.toLinearMap ((1 : D.R₁) ⊗ₜ[C.R₁] m) :=
          congrArg (fun z => s • z)
            (restrictRealTrivializationLinearMap_baseChange_one_tmul M P e m)
        _ = e.hom.toLinearMap
              (s • ((1 : D.R₁) ⊗ₜ[C.R₁] m)) :=
          (e.hom.toLinearMap.map_smul _ _).symm
        _ = e.hom.toLinearMap (s ⊗ₜ[C.R₁] m) :=
          congrArg _ hsSource.symm

/-- Restricting a real trivialization remains injective. -/
lemma restrictRealTrivializationLinearMap_injective
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    Function.Injective (restrictRealTrivializationLinearMap M P e) := by
  intro m n h
  apply restrictedTrivializedSeries_injective M P e
  have h' := congrArg (exponentConstantSeriesEquiv (Γ := Γ) P) h
  simpa only [restrictRealTrivializationLinearMap_apply,
    LinearEquiv.apply_symm_apply] using h'

private noncomputable def restrictRealTrivializationPullback₁
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    π₁s (novikovCosimplicialRing Γ A) M.M →ₗ[
      (novikovCosimplicialRing Γ A).R₂]
      π₁s (novikovCosimplicialRing Γ A)
        ((vectToNovikovDescent Γ A).obj P).M := by
  let C := novikovCosimplicialRing Γ A
  letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
  exact LinearMap.baseChange C.R₂
    (restrictRealTrivializationLinearMap M P e)

private noncomputable def restrictRealTrivializationPullback₂
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    π₂s (novikovCosimplicialRing Γ A) M.M →ₗ[
      (novikovCosimplicialRing Γ A).R₂]
      π₂s (novikovCosimplicialRing Γ A)
        ((vectToNovikovDescent Γ A).obj P).M := by
  let C := novikovCosimplicialRing Γ A
  letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
  exact LinearMap.baseChange C.R₂
    (restrictRealTrivializationLinearMap M P e)

private lemma restrictRealTrivializationPullback₁_eq
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    restrictRealTrivializationPullback₁ M P e =
      (letI : Algebra (novikovCosimplicialRing Γ A).R₁
          (novikovCosimplicialRing Γ A).R₂ :=
        (novikovCosimplicialRing Γ A).π₁.toAlgebra
       LinearMap.baseChange (novikovCosimplicialRing Γ A).R₂
        (restrictRealTrivializationLinearMap M P e)) := rfl

private lemma restrictRealTrivializationPullback₂_eq
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    restrictRealTrivializationPullback₂ M P e =
      (letI : Algebra (novikovCosimplicialRing Γ A).R₁
          (novikovCosimplicialRing Γ A).R₂ :=
        (novikovCosimplicialRing Γ A).π₂.toAlgebra
       LinearMap.baseChange (novikovCosimplicialRing Γ A).R₂
        (restrictRealTrivializationLinearMap M P e)) := rfl

private lemma restrictRealTrivialization_realTrivializedSeries
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (m : M.M) :
    realTrivializedSeries ((vectToNovikovDescent Γ A).obj P) P
        (exponentConstantBaseChangeIso Γ A P)
        (restrictRealTrivializationLinearMap M P e m) =
      realTrivializedSeries M P e m := by
  have h := restrictRealTrivializationLinearMap_baseChange_one_tmul M P e m
  dsimp only at h
  unfold realTrivializedSeries
  dsimp only
  rw [h]

private lemma firstRealization_restrictRealTrivialization
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (z : π₁s (novikovCosimplicialRing Γ A) M.M) :
    firstRealization ((vectToNovikovDescent Γ A).obj P) P
        (exponentConstantBaseChangeIso Γ A P)
        (restrictRealTrivializationPullback₁ M P e z) =
      firstRealization M P e z := by
  let C := novikovCosimplicialRing Γ A
  let K := (vectToNovikovDescent Γ A).obj P
  let k := exponentConstantBaseChangeIso Γ A P
  letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, h₁, h₂]
  | tmul a m =>
      rw [restrictRealTrivializationPullback₁, LinearMap.baseChange_tmul]
      have hK := firstRealization_tmul K P k a
        (restrictRealTrivializationLinearMap M P e m)
      have hM := firstRealization_tmul M P e a m
      dsimp only [id_eq] at hK hM
      rw [hK, hM, restrictRealTrivialization_realTrivializedSeries]

private lemma secondRealization_restrictRealTrivialization
    (M : NovikovDescentDatum Γ A) (P : FiniteProjectiveModule A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
    (z : π₂s (novikovCosimplicialRing Γ A) M.M) :
    secondRealization ((vectToNovikovDescent Γ A).obj P) P
        (exponentConstantBaseChangeIso Γ A P)
        (restrictRealTrivializationPullback₂ M P e z) =
      secondRealization M P e z := by
  let C := novikovCosimplicialRing Γ A
  let K := (vectToNovikovDescent Γ A).obj P
  let k := exponentConstantBaseChangeIso Γ A P
  letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, h₁, h₂]
  | tmul a m =>
      rw [restrictRealTrivializationPullback₂, LinearMap.baseChange_tmul]
      have hK := secondRealization_tmul K P k a
        (restrictRealTrivializationLinearMap M P e m)
      have hM := secondRealization_tmul M P e a m
      dsimp only [id_eq] at hK hM
      rw [hK, hM, restrictRealTrivialization_realTrivializedSeries]

universe u

private lemma restrictRealTrivialization_realizations_commute
    {A₀ : Type u} [CommRing A₀]
    (M : NovikovDescentDatum Γ A₀)
    (P : FiniteProjectiveModule.{u, u} A₀)
    (e : M.baseChange (exponentInclusionCHom Γ A₀) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A₀).obj P)
    (z : π₁s (novikovCosimplicialRing Γ A₀) M.M) :
    secondRealization ((vectToNovikovDescent Γ A₀).obj P) P
        (exponentConstantBaseChangeIso Γ A₀ P)
        (((vectToNovikovDescent Γ A₀).obj P).φ
          (restrictRealTrivializationPullback₁ M P e z)) =
      secondRealization ((vectToNovikovDescent Γ A₀).obj P) P
        (exponentConstantBaseChangeIso Γ A₀ P)
        (restrictRealTrivializationPullback₂ M P e (M.φ z)) := by
  calc
    secondRealization ((vectToNovikovDescent Γ A₀).obj P) P
        (exponentConstantBaseChangeIso Γ A₀ P)
        (((vectToNovikovDescent Γ A₀).obj P).φ
          (restrictRealTrivializationPullback₁ M P e z)) =
      firstRealization ((vectToNovikovDescent Γ A₀).obj P) P
        (exponentConstantBaseChangeIso Γ A₀ P)
        (restrictRealTrivializationPullback₁ M P e z) :=
      realizations_commute_φ ((vectToNovikovDescent Γ A₀).obj P) P
        (exponentConstantBaseChangeIso Γ A₀ P)
        (restrictRealTrivializationPullback₁ M P e z)
    _ = firstRealization M P e z :=
      firstRealization_restrictRealTrivialization M P e z
    _ = secondRealization M P e (M.φ z) :=
      (realizations_commute_φ M P e z).symm
    _ = secondRealization ((vectToNovikovDescent Γ A₀).obj P) P
        (exponentConstantBaseChangeIso Γ A₀ P)
        (restrictRealTrivializationPullback₂ M P e (M.φ z)) :=
      (secondRealization_restrictRealTrivialization M P e (M.φ z)).symm

private lemma restrictRealTrivialization_commute_apply
    {A₀ : Type u} [CommRing A₀]
    (M : NovikovDescentDatum Γ A₀)
    (P : FiniteProjectiveModule.{u, u} A₀)
    (e : M.baseChange (exponentInclusionCHom Γ A₀) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A₀).obj P)
    (z : π₁s (novikovCosimplicialRing Γ A₀) M.M) :
    ((vectToNovikovDescent Γ A₀).obj P).φ
        (restrictRealTrivializationPullback₁ M P e z) =
      restrictRealTrivializationPullback₂ M P e (M.φ z) := by
  apply secondRealization_injective ((vectToNovikovDescent Γ A₀).obj P) P
    (exponentConstantBaseChangeIso Γ A₀ P)
  exact restrictRealTrivialization_realizations_commute M P e z

/-- Restrict a real trivialization to a morphism from `M` to the constant
`Γ`-exponent descent datum. -/
noncomputable def restrictRealTrivialization
    {A₀ : Type u} [CommRing A₀]
    (M : NovikovDescentDatum Γ A₀)
    (P : FiniteProjectiveModule.{u, u} A₀)
    (e : M.baseChange (exponentInclusionCHom Γ A₀) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A₀).obj P) :
    M ⟶ (vectToNovikovDescent Γ A₀).obj P := by
  refine
    { toLinearMap := restrictRealTrivializationLinearMap M P e
      commute_φ := ?_ }
  rw [← restrictRealTrivializationPullback₁_eq,
    ← restrictRealTrivializationPullback₂_eq]
  apply LinearMap.coe_injective
  funext z
  exact restrictRealTrivialization_commute_apply M P e z

@[simp]
lemma restrictRealTrivialization_toLinearMap
    {A₀ : Type u} [CommRing A₀]
    (M : NovikovDescentDatum Γ A₀)
    (P : FiniteProjectiveModule.{u, u} A₀)
    (e : M.baseChange (exponentInclusionCHom Γ A₀) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A₀).obj P) :
    (restrictRealTrivialization M P e).toLinearMap =
      restrictRealTrivializationLinearMap M P e := rfl

/-- The restricted real trivialization is injective on underlying modules. -/
lemma restrictRealTrivialization_injective
    {A₀ : Type u} [CommRing A₀]
    (M : NovikovDescentDatum Γ A₀)
    (P : FiniteProjectiveModule.{u, u} A₀)
    (e : M.baseChange (exponentInclusionCHom Γ A₀) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A₀).obj P) :
    Function.Injective (restrictRealTrivialization M P e).toLinearMap :=
  restrictRealTrivializationLinearMap_injective M P e

/-- The base change of the restricted descent morphism is the given real
trivialization after applying the constant-object comparison. -/
lemma restrictRealTrivialization_baseChange
    {A₀ : Type u} [CommRing A₀]
    (M : NovikovDescentDatum Γ A₀)
    (P : FiniteProjectiveModule.{u, u} A₀)
    (e : M.baseChange (exponentInclusionCHom Γ A₀) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A₀).obj P) :
    let C := novikovCosimplicialRing Γ A₀
    let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A₀
    let F := exponentInclusionCHom Γ A₀
    letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
    (exponentConstantBaseChangeIso Γ A₀ P).hom.toLinearMap.comp
        (LinearMap.baseChange D.R₁
          (restrictRealTrivialization M P e).toLinearMap) =
      e.hom.toLinearMap := by
  exact restrictRealTrivializationLinearMap_baseChange M P e

end Novikov.Descent
