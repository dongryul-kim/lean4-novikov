import Novikov.Descent.CoefficientMap
import Novikov.Isocrystal.BaseChange

/-!
# Coefficient base change for descended isocrystals

This file proves that forming the isocrystal associated to real Novikov descent
data commutes with extension of the coefficient ring.
-/

open CategoryTheory TensorProduct Novikov.Miscellany
open Novikov.Descent.Abstract

namespace Novikov.Descent

universe u

variable {Λ : ℝ} [Fact (Λ > 1)]
variable {A B : Type u} [CommRing A] [CommRing B]

/-- Coefficient extension commutes with Frobenius on the second coordinate. -/
lemma F2_comp_realCCoeffHom_f₂ (f : A →+* B) :
    (F2 (Λ := Λ) B).comp (realCCoeffHom f).f₂ =
      (realCCoeffHom f).f₂.comp (F2 (Λ := Λ) A) := by
  apply RingHom.ext
  intro x
  apply Novikov.NovikovSeries.ext
  intro d
  change f (x.val (Novikov.scaleCoordinate (Λ := Λ) (1 : Fin 2) d)) =
    f (x.val (Novikov.scaleCoordinate (Λ := Λ) (1 : Fin 2) d))
  rfl

/-- Coefficient extension commutes with inverse Frobenius on the second
coordinate. -/
lemma F2Inv_comp_realCCoeffHom_f₂ (f : A →+* B) :
    (F2Inv (Λ := Λ) B).comp (realCCoeffHom f).f₂ =
      (realCCoeffHom f).f₂.comp (F2Inv (Λ := Λ) A) := by
  apply RingHom.ext
  intro x
  apply Novikov.NovikovSeries.ext
  intro d
  change f (x.val (Novikov.scaleCoordinate (Λ := 1 / Λ) (1 : Fin 2) d)) =
    f (x.val (Novikov.scaleCoordinate (Λ := 1 / Λ) (1 : Fin 2) d))
  rfl

/-- The comparison between pullback after coefficient base change and
coefficient base change after pullback intertwines the Frobenius twist on the
`π₁` pullback. -/
lemma pullbackBaseChangeπ₁_F2
    (f : A →+* B)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (x : π₁s (realC B) (baseChange_along (realCCoeffHom f).f₁ M.M)) :
    let F := realCCoeffHom f
    let T_B := baseChangeSemilinearSelf (realC B).π₁ (F2 (Λ := Λ) B)
      (F2Inv (Λ := Λ) B) (F2_comp_π₁_eq (Λ := Λ) B)
      (F2Inv_comp_π₁_eq (Λ := Λ) B)
      (baseChange_along F.f₁ M.M)
    let T_A := baseChangeSemilinearSelf (realC A).π₁ (F2 (Λ := Λ) A)
      (F2Inv (Λ := Λ) A) (F2_comp_π₁_eq (Λ := Λ) A)
      (F2Inv_comp_π₁_eq (Λ := Λ) A) M.M
    F.pullbackBaseChangeπ₁ M.M (T_B x) =
      baseChangeSemilinearMap F.f₂ (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
        (F2 (Λ := Λ) B) (F2Inv (Λ := Λ) B)
        (F2_comp_realCCoeffHom_f₂ f)
        (F2Inv_comp_realCCoeffHom_f₂ f)
        (π₁s (realC A) M.M) (π₁s (realC A) M.M) T_A
        (F.pullbackBaseChangeπ₁ M.M x) := by
  dsimp only
  letI : Algebra (realC A).R₁ (realC B).R₁ := (realCCoeffHom f).f₁.toAlgebra
  letI : Algebra (realC A).R₂ (realC B).R₂ := (realCCoeffHom f).f₂.toAlgebra
  letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
  letI : Algebra (realC B).R₁ (realC B).R₂ := (realC B).π₁.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r y =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
      | tmul s m =>
          rw [baseChangeSemilinearSelf_tmul]
          rw [CosimplicialRingHom.pullbackBaseChangeπ₁_tmul]
          rw [CosimplicialRingHom.pullbackBaseChangeπ₁_tmul]
          rw [baseChangeSemilinearMap_tmul]
          rw [baseChangeSemilinearSelf_tmul]
          congr 1
          · rw [Algebra.smul_def, Algebra.smul_def, map_mul]
            congr 1
            exact (congrFun (congrArg DFunLike.coe
              (F2_comp_π₁_eq (Λ := Λ) B)) s).symm
          · rw [map_one]

/-- The pullback comparison along `π₂` intertwines the Frobenius `FM2` of a
descent datum with the coefficient-base-changed `FM2`. -/
lemma pullbackBaseChangeπ₂_FM2
    (f : A →+* B)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (x : π₂s (realC B) (baseChange_along (realCCoeffHom f).f₁ M.M)) :
    let F := realCCoeffHom f
    let N := M.baseChange F
    F.pullbackBaseChangeπ₂ M.M (FM2 (Λ := Λ) B N x) =
      baseChangeSemilinearMap F.f₂ (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
        (F2 (Λ := Λ) B) (F2Inv (Λ := Λ) B)
        (F2_comp_realCCoeffHom_f₂ f)
        (F2Inv_comp_realCCoeffHom_f₂ f)
        (π₂s (realC A) M.M) (π₂s (realC A) M.M) (FM2 (Λ := Λ) A M)
        (F.pullbackBaseChangeπ₂ M.M x) := by
  dsimp only
  let F := realCCoeffHom f
  letI : Algebra (realC A).R₁ (realC B).R₁ := F.f₁.toAlgebra
  letI : Algebra (realC A).R₂ (realC B).R₂ := F.f₂.toAlgebra
  let T_A : π₁s (realC A) M.M ≃ₛₗ[F2 (Λ := Λ) A] π₁s (realC A) M.M :=
    baseChangeSemilinearSelf (realC A).π₁ (F2 (Λ := Λ) A)
      (F2Inv (Λ := Λ) A) (F2_comp_π₁_eq (Λ := Λ) A)
      (F2Inv_comp_π₁_eq (Λ := Λ) A) M.M
  let T_B : π₁s (realC B) (baseChange_along F.f₁ M.M) ≃ₛₗ[F2 (Λ := Λ) B]
      π₁s (realC B) (baseChange_along F.f₁ M.M) :=
    baseChangeSemilinearSelf (realC B).π₁ (F2 (Λ := Λ) B)
      (F2Inv (Λ := Λ) B) (F2_comp_π₁_eq (Λ := Λ) B)
      (F2Inv_comp_π₁_eq (Λ := Λ) B) (baseChange_along F.f₁ M.M)
  let T_bc : ((realC B).R₂ ⊗[(realC A).R₂] (π₁s (realC A) M.M)) ≃ₛₗ[F2 (Λ := Λ) B]
      ((realC B).R₂ ⊗[(realC A).R₂] (π₁s (realC A) M.M)) :=
    baseChangeSemilinearMap F.f₂ (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
      (F2 (Λ := Λ) B) (F2Inv (Λ := Λ) B)
      (F2_comp_realCCoeffHom_f₂ f)
      (F2Inv_comp_realCCoeffHom_f₂ f)
      (π₁s (realC A) M.M) (π₁s (realC A) M.M) T_A
  let FM_bc : ((realC B).R₂ ⊗[(realC A).R₂] (π₂s (realC A) M.M)) ≃ₛₗ[F2 (Λ := Λ) B]
      ((realC B).R₂ ⊗[(realC A).R₂] (π₂s (realC A) M.M)) :=
    baseChangeSemilinearMap F.f₂ (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
      (F2 (Λ := Λ) B) (F2Inv (Λ := Λ) B)
      (F2_comp_realCCoeffHom_f₂ f)
      (F2Inv_comp_realCCoeffHom_f₂ f)
      (π₂s (realC A) M.M) (π₂s (realC A) M.M) (FM2 (Λ := Λ) A M)
  let φbc : ((realC B).R₂ ⊗[(realC A).R₂] (π₁s (realC A) M.M)) ≃ₗ[(realC B).R₂]
      ((realC B).R₂ ⊗[(realC A).R₂] (π₂s (realC A) M.M)) :=
    LinearEquiv.baseChange (realC A).R₂ (realC B).R₂
      (π₁s (realC A) M.M) (π₂s (realC A) M.M) M.φ
  rw [FM2_apply]
  simp only [LinearEquiv.trans_apply]
  rw [show (M.baseChange F).φ = F.baseChangePhi M by rfl]
  change F.pullbackBaseChangeπ₂ M.M
      ((F.baseChangePhi M) (T_B ((F.baseChangePhi M).symm x))) =
    FM_bc (F.pullbackBaseChangeπ₂ M.M x)
  rw [show F.pullbackBaseChangeπ₂ M.M
      ((F.baseChangePhi M) (T_B ((F.baseChangePhi M).symm x))) =
      φbc (F.pullbackBaseChangeπ₁ M.M (T_B ((F.baseChangePhi M).symm x))) by
        simp [CosimplicialRingHom.baseChangePhi, φbc]]
  rw [pullbackBaseChangeπ₁_F2 f M]
  change φbc (T_bc (F.pullbackBaseChangeπ₁ M.M ((F.baseChangePhi M).symm x))) =
    FM_bc (F.pullbackBaseChangeπ₂ M.M x)
  rw [show F.pullbackBaseChangeπ₁ M.M ((F.baseChangePhi M).symm x) =
      φbc.symm (F.pullbackBaseChangeπ₂ M.M x) by
        simp [CosimplicialRingHom.baseChangePhi, φbc]]
  generalize F.pullbackBaseChangeπ₂ M.M x = y
  induction y using TensorProduct.induction_on with
  | zero => simp [φbc, T_bc, FM_bc]
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul r z =>
      rw [LinearEquiv.baseChange_symm_tmul]
      rw [baseChangeSemilinearMap_tmul]
      rw [LinearEquiv.baseChange_tmul]
      rw [baseChangeSemilinearMap_tmul]
      rfl

/-- The descended Frobenius commutes with coefficient base change on tensors of
the form `1 ⊗ m`. -/
lemma descentFrobeniusToFun_baseChange_one_tmul
    (f : A →+* B)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A) (m : M.M) :
    let F := realCCoeffHom f
    let N := M.baseChange F
    letI : Algebra (realC A).R₁ (realC B).R₁ := F.f₁.toAlgebra
    descentFrobeniusToFun (Λ := Λ) B N
        ((1 : (realC B).R₁) ⊗ₜ[(realC A).R₁] m) =
      ((1 : (realC B).R₁) ⊗ₜ[(realC A).R₁]
        descentFrobeniusToFun (Λ := Λ) A M m) := by
  dsimp only
  let F := realCCoeffHom f
  let N := M.baseChange F
  letI : Algebra (realC A).R₁ (realC B).R₁ := F.f₁.toAlgebra
  apply oneTmulπ₂_injective (A := B) N.M
  rw [← descentFrobeniusToFun_spec]
  apply (F.pullbackBaseChangeπ₂ M.M).injective
  rw [pullbackBaseChangeπ₂_FM2 f M]
  letI : Algebra (realC A).R₂ (realC B).R₂ := F.f₂.toAlgebra
  letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
  letI : Algebra (realC B).R₁ (realC B).R₂ := (realC B).π₂.toAlgebra
  have hp (q : M.M) :
      F.pullbackBaseChangeπ₂ M.M
          (oneTmulπ₂ (A := B) (M.baseChange F).M
            ((1 : (realC B).R₁) ⊗ₜ[(realC A).R₁] q)) =
        ((1 : (realC B).R₂) ⊗ₜ[(realC A).R₂]
          oneTmulπ₂ (A := A) M.M q) := by
    simpa only [oneTmulπ₂_apply, one_smul] using
      (F.pullbackBaseChangeπ₂_tmul M.M (1 : (realC B).R₂)
        (1 : (realC B).R₁) q)
  dsimp only [N]
  rw [hp]
  rw [baseChangeSemilinearMap_tmul]
  rw [descentFrobeniusToFun_spec]
  rw [hp]
  simp only [map_one]

/-- Pointwise semilinearity of the descended Frobenius, stated with the
one-variable Novikov-series scalar action made explicit. -/
lemma descentFrobeniusToFun_smul
    (A : Type u) [CommRing A]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (r : (realC A).R₁) (m : M.M) :
    letI : Module (RealNovikovSeries A) M.M := by
      dsimp [RealNovikovSeries, OneVarNovikovSeries, realC]
      exact M.instModule
    descentFrobeniusToFun (Λ := Λ) A M
        ((show RealNovikovSeries A from r) • m) =
      (Novikov.frobeniusRingHom (Λ := Λ) (A := A) r) •
        descentFrobeniusToFun (Λ := Λ) A M m := by
  letI : Module (RealNovikovSeries A) M.M := by
    dsimp [RealNovikovSeries, OneVarNovikovSeries, realC]
    exact M.instModule
  exact (descentFrobenius (Λ := Λ) A M).map_smul' r m

/-- The descended Frobenius commutes with coefficient base change on every
pure tensor. -/
lemma descentFrobeniusToFun_baseChange_tmul
    (f : A →+* B)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (r : (realC B).R₁) (m : M.M) :
    let F := realCCoeffHom f
    let N := M.baseChange F
    letI : Algebra (realC A).R₁ (realC B).R₁ := F.f₁.toAlgebra
    descentFrobeniusToFun (Λ := Λ) B N (r ⊗ₜ[(realC A).R₁] m) =
      ((Novikov.frobeniusRingHom (Λ := Λ) (A := B) r) ⊗ₜ[(realC A).R₁]
        descentFrobeniusToFun (Λ := Λ) A M m : N.M) := by
  dsimp only
  let F := realCCoeffHom f
  let N := M.baseChange F
  letI : Algebra (realC A).R₁ (realC B).R₁ := F.f₁.toAlgebra
  let z : N.M := (1 : (realC B).R₁) ⊗ₜ[(realC A).R₁] m
  have h_tensor : (r ⊗ₜ[(realC A).R₁] m : N.M) = r • z := by
    change (r ⊗ₜ[(realC A).R₁] m : baseChange_along F.f₁ M.M) =
      r • ((1 : (realC B).R₁) ⊗ₜ[(realC A).R₁] m)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h_smul : descentFrobeniusToFun (Λ := Λ) B N (r • z) =
      (show (realC B).R₁ from
        Novikov.frobeniusRingHom (Λ := Λ) (A := B) r) •
        descentFrobeniusToFun (Λ := Λ) B N z := by
    letI : Module (RealNovikovSeries B) N.M := by
      dsimp [RealNovikovSeries, OneVarNovikovSeries, realC]
      exact N.instModule
    exact descentFrobeniusToFun_smul B N r z
  rw [h_tensor, h_smul]
  dsimp only [z]
  rw [descentFrobeniusToFun_baseChange_one_tmul f M m]
  change (show (realC B).R₁ from
      Novikov.frobeniusRingHom (Λ := Λ) (A := B) r) •
      ((1 : (realC B).R₁) ⊗ₜ[(realC A).R₁]
        descentFrobeniusToFun (Λ := Λ) A M m) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private lemma descentFrobeniusToFun_zero
    (A : Type u) [CommRing A]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A) :
    descentFrobeniusToFun (Λ := Λ) A M 0 = 0 := by
  letI : Module (RealNovikovSeries A) M.M := by
    dsimp [RealNovikovSeries, OneVarNovikovSeries, realC]
    exact M.instModule
  exact map_zero (descentFrobenius (Λ := Λ) A M)

private lemma descentFrobeniusToFun_add
    (A : Type u) [CommRing A]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A) (x y : M.M) :
    descentFrobeniusToFun (Λ := Λ) A M (x + y) =
      descentFrobeniusToFun (Λ := Λ) A M x +
        descentFrobeniusToFun (Λ := Λ) A M y := by
  letI : Module (RealNovikovSeries A) M.M := by
    dsimp [RealNovikovSeries, OneVarNovikovSeries, realC]
    exact M.instModule
  exact map_add (descentFrobenius (Λ := Λ) A M) x y

/-- On the common underlying tensor product, the descended Frobenius after
coefficient base change is the Frobenius of the base-changed isocrystal. -/
lemma descentFrobenius_baseChange
    (f : A →+* B)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (x : baseChange_along (realCCoeffHom f).f₁ M.M) :
    descentFrobeniusToFun (Λ := Λ) B (M.baseChange (realCCoeffHom f)) x =
      (Novikov.baseChange f ((descentToIsocrystal (Λ := Λ) A).obj M)).F_M x := by
  let F := realCCoeffHom f
  let N := M.baseChange F
  letI : Algebra (realC A).R₁ (realC B).R₁ := F.f₁.toAlgebra
  letI : Module (RealNovikovSeries B) N.M := by
    dsimp [RealNovikovSeries, OneVarNovikovSeries, realC]
    exact N.instModule
  change descentFrobeniusToFun (Λ := Λ) B N x =
    (Novikov.baseChange f ((descentToIsocrystal (Λ := Λ) A).obj M)).F_M x
  induction x using TensorProduct.induction_on with
  | zero =>
      have h₁ : descentFrobeniusToFun (Λ := Λ) B N 0 = 0 :=
        descentFrobeniusToFun_zero B N
      have h₂ :
          (Novikov.baseChange f ((descentToIsocrystal (Λ := Λ) A).obj M)).F_M 0 = 0 :=
        map_zero _
      exact h₁.trans h₂.symm
  | add x y hx hy =>
      have h₁ : descentFrobeniusToFun (Λ := Λ) B N (x + y) =
          descentFrobeniusToFun (Λ := Λ) B N x +
            descentFrobeniusToFun (Λ := Λ) B N y :=
        descentFrobeniusToFun_add B N x y
      have h₂ :
          (Novikov.baseChange f ((descentToIsocrystal (Λ := Λ) A).obj M)).F_M (x + y) =
            (Novikov.baseChange f ((descentToIsocrystal (Λ := Λ) A).obj M)).F_M x +
              (Novikov.baseChange f ((descentToIsocrystal (Λ := Λ) A).obj M)).F_M y :=
        map_add _ x y
      exact h₁.trans ((congrArg₂ HAdd.hAdd hx hy).trans h₂.symm)
  | tmul r m =>
      rw [descentFrobeniusToFun_baseChange_tmul f M r m]
      exact (Novikov.baseChange_F_tmul (Λ := Λ) f
        ((descentToIsocrystal (Λ := Λ) A).obj M) r m).symm

private lemma descentFrobenius_apply
    (A : Type u) [CommRing A]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A) (m : M.M) :
    descentFrobenius (Λ := Λ) A M m =
      descentFrobeniusToFun (Λ := Λ) A M m := rfl

/-- Frobenius compatibility in the object types used by the two isocrystal
constructions. -/
lemma descentToIsocrystal_baseChange_frobenius
    (f : A →+* B)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (x : (Novikov.baseChange f ((descentToIsocrystal (Λ := Λ) A).obj M)).M) :
    ((descentToIsocrystal (Λ := Λ) B).obj
        (M.baseChange (realCCoeffHom f))).F_M x =
      (Novikov.baseChange f ((descentToIsocrystal (Λ := Λ) A).obj M)).F_M x := by
  dsimp only [descentToIsocrystal, descentToIsocrystalObj]
  erw [descentFrobenius_apply (Λ := Λ) B
    (M.baseChange (realCCoeffHom f))]
  let x' : baseChange_along (realCCoeffHom f).f₁ M.M := x
  exact descentFrobenius_baseChange (Λ := Λ) f M x'

/-- Forming the isocrystal associated to descent data commutes, objectwise,
with extension of the coefficient ring. -/
noncomputable def descentToIsocrystal_baseChangeIso
    (f : A →+* B)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A) :
    Novikov.baseChange f ((descentToIsocrystal (Λ := Λ) A).obj M) ≅
      (descentToIsocrystal (Λ := Λ) B).obj
        (M.baseChange (realCCoeffHom f)) := by
  let X := Novikov.baseChange f ((descentToIsocrystal (Λ := Λ) A).obj M)
  let Y := (descentToIsocrystal (Λ := Λ) B).obj
    (M.baseChange (realCCoeffHom f))
  let hom : X ⟶ Y :=
    { toLinearMap := by
        dsimp only [X, Y]
        exact LinearMap.id
      commute_frobenius := by
        intro x
        change Y.F_M x = X.F_M x
        exact descentToIsocrystal_baseChange_frobenius (Λ := Λ) f M x }
  let inv : Y ⟶ X :=
    { toLinearMap := by
        dsimp only [X, Y]
        exact LinearMap.id
      commute_frobenius := by
        intro x
        change X.F_M x = Y.F_M x
        exact (descentToIsocrystal_baseChange_frobenius (Λ := Λ) f M x).symm }
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply Novikov.NovikovIsocrystal.hom_ext
        rfl
      inv_hom_id := by
        apply Novikov.NovikovIsocrystal.hom_ext
        rfl }

end Novikov.Descent
