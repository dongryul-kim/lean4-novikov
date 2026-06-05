import Novikov.Descent.Abstract.BaseChange
import Novikov.Descent.Abstract.Constant
import Mathlib.CategoryTheory.Opposites

open TensorProduct CategoryTheory

namespace Novikov.Descent.Abstract
open Novikov.Miscellany

section Self

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Base change of the ring along a ring homomorphism, identified with the target ring. -/
noncomputable def baseChangeSelfEquiv (f : R →+* S) :
    baseChange_along f R ≃ₗ[S] S := by
  letI : Algebra R S := f.toAlgebra
  exact TensorProduct.AlgebraTensorModule.rid R S S

@[simp]
lemma baseChangeSelfEquiv_tmul (f : R →+* S) (s : S) (r : R) :
    baseChangeSelfEquiv f ((letI : Algebra R S := f.toAlgebra; s ⊗ₜ[R] r)) =
      f r * s := by
  letI : Algebra R S := f.toAlgebra
  change (TensorProduct.AlgebraTensorModule.rid R S S) (s ⊗ₜ[R] r) = f r * s
  rw [TensorProduct.AlgebraTensorModule.rid_tmul]
  rfl

@[simp]
lemma baseChangeSelfEquiv_symm_apply (f : R →+* S) (s : S) :
    (baseChangeSelfEquiv f).symm s =
      (letI : Algebra R S := f.toAlgebra; s ⊗ₜ[R] (1 : R)) := by
  letI : Algebra R S := f.toAlgebra
  change (TensorProduct.AlgebraTensorModule.rid R S S).symm s = s ⊗ₜ[R] (1 : R)
  rw [TensorProduct.AlgebraTensorModule.rid_symm_apply]

/-- Pulling back the canonical self-base-change equivalence remains canonical. -/
lemma pullbackMap_baseChangeSelfEquiv
    {R₁ R₂ R₃ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (f₁ f₂ : R₁ →+* R₂) (g : R₂ →+* R₃)
    {h₁ h₂ : R₁ →+* R₃} (hh₁ : g.comp f₁ = h₁) (hh₂ : g.comp f₂ = h₂) :
    pullbackMap f₁ f₂ g hh₁ hh₂ R₁ R₁
      ((baseChangeSelfEquiv f₁).trans (baseChangeSelfEquiv f₂).symm) =
    (baseChangeSelfEquiv h₁).trans (baseChangeSelfEquiv h₂).symm := by
  subst hh₁
  subst hh₂
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, hx, hy]
  | tmul r a =>
      rw [pullbackMap_tmul_apply]
      simp [baseChangeSelfEquiv_tmul, baseChangeSelfEquiv_symm_apply, Algebra.smul_def,
        RingHom.algebraMap_toAlgebra, mul_comm]

end Self

/-- The unit/structure-sheaf descent datum over a cosimplicial ring. -/
noncomputable def structureSheaf (C : CosimplicialRing) : DescentDatum C := by
  refine
    { M := C.R₁
      instAddCommGroup := inferInstance
      instModule := inferInstance
      instFinite := inferInstance
      instProjective := inferInstance
      φ := (baseChangeSelfEquiv C.π₁).trans (baseChangeSelfEquiv C.π₂).symm
      cocycle := ?_ }
  have h12 := pullbackMap_baseChangeSelfEquiv C.π₁ C.π₂ C.π₁₂
    C.ρ₁_eq_π₁₂_π₁.symm C.ρ₂_eq_π₁₂_π₂.symm
  have h23 := pullbackMap_baseChangeSelfEquiv C.π₁ C.π₂ C.π₂₃ rfl rfl
  have h13 := pullbackMap_baseChangeSelfEquiv C.π₁ C.π₂ C.π₁₃
    C.ρ₁_eq_π₁₃_π₁.symm C.ρ₃_eq_π₁₃_π₂.symm
  unfold pullbackMap_12 pullbackMap_23 pullbackMap_13
  simp only [h12, h23, h13]
  ext x
  change (baseChangeSelfEquiv C.ρ₃).symm
      ((baseChangeSelfEquiv C.ρ₂)
        ((baseChangeSelfEquiv C.ρ₂).symm ((baseChangeSelfEquiv C.ρ₁) x))) =
    (baseChangeSelfEquiv C.ρ₃).symm ((baseChangeSelfEquiv C.ρ₁) x)
  rw [LinearEquiv.apply_symm_apply]

@[simp]
lemma structureSheaf_φ_tmul (C : CosimplicialRing) (r : C.R₂) (a : C.R₁) :
    (structureSheaf C).φ
      (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; r ⊗ₜ[C.R₁] a) =
    (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra; (C.π₁ a * r) ⊗ₜ[C.R₁] (1 : C.R₁)) := by
  change (baseChangeSelfEquiv C.π₂).symm
      (baseChangeSelfEquiv C.π₁ (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; r ⊗ₜ[C.R₁] a)) = _
  rw [baseChangeSelfEquiv_tmul, baseChangeSelfEquiv_symm_apply]

private lemma linearMap_comp_symm_of_comp {R : Type*} [CommSemiring R]
    {M₁ M₂ N₁ N₂ : Type*}
    [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    [AddCommMonoid N₁] [Module R N₁] [AddCommMonoid N₂] [Module R N₂]
    {Φ : M₂ →ₗ[R] N₂} {Ψ : M₁ →ₗ[R] N₁}
    {B : M₁ ≃ₗ[R] M₂} {C : N₁ ≃ₗ[R] N₂}
    (h : Φ ∘ₗ B.toLinearMap = C.toLinearMap ∘ₗ Ψ) :
    Ψ ∘ₗ B.symm.toLinearMap = C.symm.toLinearMap ∘ₗ Φ := by
  ext x
  have hx := LinearMap.congr_fun h (B.symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, B.apply_symm_apply] at hx
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hx, C.symm_apply_apply]

namespace CosimplicialRingHom

variable {C D : CosimplicialRing} (F : CosimplicialRingHom C D)

/-- The structure-sheaf base-change comparison is a morphism of descent data. -/
lemma structureSheafBaseChangeIso_hom_commute :
    (structureSheaf D).φ.toLinearMap ∘ₗ
        (letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
         LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).toLinearMap) =
      (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
       LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).toLinearMap) ∘ₗ
        (F.baseChangePhi (structureSheaf C)).toLinearMap := by
  let e := baseChangeSelfEquiv F.f₁
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, LinearMap.comp_apply] at hx hy ⊢
      rw [hx, hy]
  | tmul r y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
          simp only [TensorProduct.tmul_add, map_add, LinearMap.comp_apply] at hy hz ⊢
          rw [hy, hz]
      | tmul s a =>
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
          letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
          let same : (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra; D.R₂ ⊗[D.R₁] D.R₁) :=
            (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
             (D.π₁ ((baseChangeSelfEquiv F.f₁) (s ⊗ₜ[C.R₁] a)) * r) ⊗ₜ[D.R₁] (1 : D.R₁))
          have hbc1 :
              (letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
               LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).toLinearMap
                (r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] a))) =
              (letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
               r ⊗ₜ[D.R₁] ((baseChangeSelfEquiv F.f₁) (s ⊗ₜ[C.R₁] a))) := by
            letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
            rw [LinearMap.baseChange_tmul]
            rfl
          have hL :
              (structureSheaf D).φ
                ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
                  LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).toLinearMap
                    (r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] a)))) = same := by
            calc
              (structureSheaf D).φ
                  ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
                    LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).toLinearMap
                      (r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] a)))) =
                  (structureSheaf D).φ
                    ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
                      r ⊗ₜ[D.R₁] ((baseChangeSelfEquiv F.f₁) (s ⊗ₜ[C.R₁] a)))) := by
                    exact congrArg (fun z => (structureSheaf D).φ z) hbc1
              _ = same := by
                    dsimp [same]
                    rw [structureSheaf_φ_tmul]
          have hphi := F.baseChangePhi_tmul (structureSheaf C) r s a
          have hR :
              (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
               LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).toLinearMap)
                  (F.baseChangePhi (structureSheaf C)
                    (letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra;
                     r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] a))) = same := by
            calc
              (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
               LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).toLinearMap)
                  (F.baseChangePhi (structureSheaf C)
                    (letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra;
                     r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] a))) =
                (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
                 LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).toLinearMap)
                  ((F.pullbackBaseChangeπ₂ (structureSheaf C).M).symm
                    ((letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
                      letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
                      (s • r) ⊗ₜ[C.R₂]
                        ((structureSheaf C).φ ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra;
                          (1 : C.R₂) ⊗ₜ[C.R₁] a)))))) := by
                    rw [hphi]
              _ = same := by
                    rw [structureSheaf_φ_tmul]
                    let u : D.R₂ := (letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra; s • r)
                    have hpb := F.pullbackBaseChangeπ₂_symm_tmul' (structureSheaf C).M
                      u (C.π₁ a * 1) (1 : C.R₁)
                    have hbc2 (v : D.R₂) :
                        (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
                         LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).toLinearMap
                          (v ⊗ₜ[D.R₁] ((1 : D.R₁) ⊗ₜ[C.R₁] (1 : C.R₁)))) =
                        (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
                         v ⊗ₜ[D.R₁] ((baseChangeSelfEquiv F.f₁)
                          ((1 : D.R₁) ⊗ₜ[C.R₁] (1 : C.R₁)))) := by
                      letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
                      rw [LinearMap.baseChange_tmul]
                      rfl
                    calc
                      (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
                       LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).toLinearMap)
                          ((F.pullbackBaseChangeπ₂ (structureSheaf C).M).symm
                            ((letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
                              u ⊗ₜ[C.R₂]
                                (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
                                 (C.π₁ a * 1) ⊗ₜ[C.R₁] (1 : C.R₁)))) ) =
                        (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
                         LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).toLinearMap)
                          ((letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
                            letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
                            ((C.π₁ a * 1) • u) ⊗ₜ[D.R₁]
                              ((1 : D.R₁) ⊗ₜ[C.R₁] (1 : C.R₁)))) := by
                            exact congrArg (fun z =>
                              (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
                               LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).toLinearMap) z) hpb
                      _ = same := by
                        rw [hbc2]
                        dsimp [same, u]
                        rw [baseChangeSelfEquiv_tmul, baseChangeSelfEquiv_tmul]
                        simp only [CosimplicialRingHom.map_π₁_apply, Algebra.smul_def,
                          RingHom.algebraMap_toAlgebra, map_mul, map_one, mul_one]
                        ring_nf
          exact hL.trans hR.symm

/-- The inverse structure-sheaf base-change comparison is a morphism of descent data. -/
lemma structureSheafBaseChangeIso_inv_commute :
    (F.baseChangePhi (structureSheaf C)).toLinearMap ∘ₗ
        (letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
         LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).symm.toLinearMap) =
      (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
       LinearMap.baseChange D.R₂ (baseChangeSelfEquiv F.f₁).symm.toLinearMap) ∘ₗ
        (structureSheaf D).φ.toLinearMap := by
  let e := baseChangeSelfEquiv F.f₁
  let B := letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
    LinearEquiv.baseChange D.R₁ D.R₂ _ _ e
  let G := letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    LinearEquiv.baseChange D.R₁ D.R₂ _ _ e
  exact linearMap_comp_symm_of_comp (B := B) (C := G)
    (structureSheafBaseChangeIso_hom_commute F)

/-- Base change carries the structure sheaf to the structure sheaf. -/
noncomputable def structureSheafBaseChangeIso :
    (structureSheaf C).baseChange F ≅ structureSheaf D := by
  let e := baseChangeSelfEquiv F.f₁
  refine
    { hom := { toLinearMap := e.toLinearMap
               commute_φ := structureSheafBaseChangeIso_hom_commute F }
      inv := { toLinearMap := e.symm.toLinearMap
               commute_φ := structureSheafBaseChangeIso_inv_commute F }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply DescentDatum.hom_ext
    apply LinearMap.ext
    intro x
    exact e.left_inv x
  · apply DescentDatum.hom_ext
    apply LinearMap.ext
    intro x
    exact e.right_inv x

end CosimplicialRingHom

/-- The constant descent datum attached to the rank-one free module is the structure sheaf:
the forward comparison commutes with descent isomorphisms. -/
lemma constantDescentDatumUnitIso_hom_commute (E : ExtendedCosimplicialRing) :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    (structureSheaf E.toCosimplicialRing).φ.toLinearMap ∘ₗ
        (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
         LinearMap.baseChange E.R₂
          (TensorProduct.AlgebraTensorModule.rid E.R₀ E.R₁ E.R₁).toLinearMap) =
      (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
       LinearMap.baseChange E.R₂
        (TensorProduct.AlgebraTensorModule.rid E.R₀ E.R₁ E.R₁).toLinearMap) ∘ₗ
        (constantDescentDatum E E.R₀).φ.toLinearMap := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  let e := TensorProduct.AlgebraTensorModule.rid E.R₀ E.R₁ E.R₁
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.comp_apply] at hx hy ⊢; rw [hx, hy]
  | tmul r y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
          simp only [TensorProduct.tmul_add, map_add, LinearMap.comp_apply] at hy hz ⊢
          rw [hy, hz]
      | tmul s a =>
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
          let same : (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra; E.R₂ ⊗[E.R₁] E.R₁) :=
            (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
             (E.π₁ (e (s ⊗ₜ[E.R₀] a)) * r) ⊗ₜ[E.R₁] (1 : E.R₁))
          have hbc1 :
              (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
               LinearMap.baseChange E.R₂ e.toLinearMap
                (r ⊗ₜ[E.R₁] (s ⊗ₜ[E.R₀] a))) =
              (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
               r ⊗ₜ[E.R₁] (e (s ⊗ₜ[E.R₀] a))) := by
            letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
            rw [LinearMap.baseChange_tmul]
            rfl
          have hL :
              (structureSheaf E.toCosimplicialRing).φ
                ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
                  LinearMap.baseChange E.R₂ e.toLinearMap
                    (r ⊗ₜ[E.R₁] (s ⊗ₜ[E.R₀] a)))) = same := by
            calc
              (structureSheaf E.toCosimplicialRing).φ
                  ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
                    LinearMap.baseChange E.R₂ e.toLinearMap
                      (r ⊗ₜ[E.R₁] (s ⊗ₜ[E.R₀] a)))) =
                  (structureSheaf E.toCosimplicialRing).φ
                    ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
                      r ⊗ₜ[E.R₁] (e (s ⊗ₜ[E.R₀] a)))) := by
                    exact congrArg (fun z => (structureSheaf E.toCosimplicialRing).φ z) hbc1
              _ = same := by
                    dsimp [same]
                    rw [structureSheaf_φ_tmul]
          have hbc2 (u : E.R₂) :
              (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
               LinearMap.baseChange E.R₂ e.toLinearMap
                (u ⊗ₜ[E.R₁] ((1 : E.R₁) ⊗ₜ[E.R₀] a))) =
              (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
               u ⊗ₜ[E.R₁] (e ((1 : E.R₁) ⊗ₜ[E.R₀] a))) := by
            letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
            rw [LinearMap.baseChange_tmul]
            rfl
          have hR :
              (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
               LinearMap.baseChange E.R₂ e.toLinearMap)
                  ((constantDescentDatum E E.R₀).φ
                    (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
                     r ⊗ₜ[E.R₁] (s ⊗ₜ[E.R₀] a))) = same := by
            calc
              (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
               LinearMap.baseChange E.R₂ e.toLinearMap)
                  ((constantDescentDatum E E.R₀).φ
                    (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
                     r ⊗ₜ[E.R₁] (s ⊗ₜ[E.R₀] a))) =
                (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
                 LinearMap.baseChange E.R₂ e.toLinearMap)
                  ((letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
                    (E.π₁ s * r) ⊗ₜ[E.R₁] ((1 : E.R₁) ⊗ₜ[E.R₀] a))) := by
                    rw [constantDescentDatum_φ_tmul]
              _ = same := by
                    rw [hbc2]
                    dsimp [same, e]
                    letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
                    change (E.π₁ s * r) ⊗ₜ[E.R₁] ((E.π₀ a) • (1 : E.R₁)) =
                      (E.π₁ (E.π₀ a * s) * r) ⊗ₜ[E.R₁] (1 : E.R₁)
                    rw [TensorProduct.tmul_smul]
                    change (E.π₂ (E.π₀ a) * (E.π₁ s * r)) ⊗ₜ[E.R₁] (1 : E.R₁) =
                      (E.π₁ (E.π₀ a * s) * r) ⊗ₜ[E.R₁] (1 : E.R₁)
                    have ha : E.π₂ (E.π₀ a) = E.π₁ (E.π₀ a) :=
                      (RingHom.congr_fun E.π₁_π₀_eq_π₂_π₀ a).symm
                    rw [ha]
                    simp only [map_mul]
                    ring_nf
          exact hL.trans hR.symm

/-- The constant descent datum attached to the rank-one free module is the structure sheaf:
the inverse comparison commutes with descent isomorphisms. -/
lemma constantDescentDatumUnitIso_inv_commute (E : ExtendedCosimplicialRing) :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    (constantDescentDatum E E.R₀).φ.toLinearMap ∘ₗ
        (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
         LinearMap.baseChange E.R₂
          (TensorProduct.AlgebraTensorModule.rid E.R₀ E.R₁ E.R₁).symm.toLinearMap) =
      (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
       LinearMap.baseChange E.R₂
        (TensorProduct.AlgebraTensorModule.rid E.R₀ E.R₁ E.R₁).symm.toLinearMap) ∘ₗ
        (structureSheaf E.toCosimplicialRing).φ.toLinearMap := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  let e := TensorProduct.AlgebraTensorModule.rid E.R₀ E.R₁ E.R₁
  let B := letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
    LinearEquiv.baseChange E.R₁ E.R₂ _ _ e
  let G := letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
    LinearEquiv.baseChange E.R₁ E.R₂ _ _ e
  exact linearMap_comp_symm_of_comp (B := B) (C := G)
    (constantDescentDatumUnitIso_hom_commute E)

/-- The constant descent datum associated to `R₀` is the structure sheaf. -/
noncomputable def constantDescentDatumUnitIso (E : ExtendedCosimplicialRing) :
    constantDescentDatum E E.R₀ ≅ structureSheaf E.toCosimplicialRing := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  let e := TensorProduct.AlgebraTensorModule.rid E.R₀ E.R₁ E.R₁
  refine
    { hom := { toLinearMap := e.toLinearMap
               commute_φ := constantDescentDatumUnitIso_hom_commute E }
      inv := { toLinearMap := e.symm.toLinearMap
               commute_φ := constantDescentDatumUnitIso_inv_commute E }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply DescentDatum.hom_ext
    apply LinearMap.ext
    intro x
    exact e.left_inv x
  · apply DescentDatum.hom_ext
    apply LinearMap.ext
    intro x
    exact e.right_inv x

section HomBaseChangePrecomp

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {M N P : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.Projective R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
  [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]

/-- Compatibility of `homBaseChangeEquiv` with precomposition. -/
lemma homBaseChangeEquiv_precomp (f : M →ₗ[R] N)
    (x : S ⊗[R] (N →ₗ[R] P)) :
    (Novikov.Miscellany.homBaseChangeEquiv (R := R) (M := M) (N := P) S)
      ((LinearMap.baseChange S
        ({ toFun := fun g : N →ₗ[R] P => g.comp f
           map_add' := by intro g h; ext m; simp
           map_smul' := by intro r g; ext m; simp } :
          (N →ₗ[R] P) →ₗ[R] (M →ₗ[R] P))) x) =
    (Novikov.Miscellany.homBaseChangeEquiv (R := R) (M := N) (N := P) S x) ∘ₗ
      LinearMap.baseChange S f := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy, LinearMap.add_comp]
  | tmul s g =>
      apply LinearMap.ext
      intro y
      simp [LinearMap.baseChange_tmul, LinearMap.baseChange_comp, LinearMap.smul_apply]

/-- Compatibility of `homBaseChangeEquiv` with postcomposition. -/
lemma homBaseChangeEquiv_postcomp (f : N →ₗ[R] P)
    (x : S ⊗[R] (M →ₗ[R] N)) :
    (Novikov.Miscellany.homBaseChangeEquiv (R := R) (M := M) (N := P) S)
      ((LinearMap.baseChange S
        ({ toFun := fun g : M →ₗ[R] N => f.comp g
           map_add' := by intro g h; ext m; simp
           map_smul' := by intro r g; ext m; simp } :
          (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] P))) x) =
    LinearMap.baseChange S f ∘ₗ
      (Novikov.Miscellany.homBaseChangeEquiv (R := R) (M := M) (N := N) S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy, LinearMap.comp_add]
  | tmul s g =>
      apply LinearMap.ext
      intro y
      simp [LinearMap.baseChange_tmul, LinearMap.baseChange_comp, LinearMap.smul_apply]

/-- Applying `homBaseChangeEquiv` after `homConj` is conjugation by the two
base-change equivalences. -/
lemma homBaseChangeEquiv_homConj
    {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂]
    (f₁ f₂ : R₁ →+* R₂)
    (M N : Type*) [AddCommGroup M] [Module R₁ M]
    [Module.Finite R₁ M] [Module.Projective R₁ M]
    [AddCommGroup N] [Module R₁ N]
    [Module.Finite R₁ N] [Module.Projective R₁ N]
    (φM : baseChange_along f₁ M ≃ₗ[R₂] baseChange_along f₂ M)
    (φN : baseChange_along f₁ N ≃ₗ[R₂] baseChange_along f₂ N)
    (x : baseChange_along f₁ (M →ₗ[R₁] N)) :
    (letI : Algebra R₁ R₂ := f₂.toAlgebra
     Novikov.Miscellany.homBaseChangeEquiv (R := R₁) (M := M) (N := N) R₂)
        (homConj f₁ f₂ M N φM φN x) =
      φN.toLinearMap ∘ₗ
        ((letI : Algebra R₁ R₂ := f₁.toAlgebra
          Novikov.Miscellany.homBaseChangeEquiv (R := R₁) (M := M) (N := N) R₂) x) ∘ₗ
        φM.symm.toLinearMap := by
  ext y
  simp [homConj, LinearEquiv.arrowCongr_apply]

end HomBaseChangePrecomp

namespace CosimplicialRingHom

variable {C D : CosimplicialRing} (F : CosimplicialRingHom C D)

set_option linter.unusedSimpArgs false in
/-- Compatibility of `homBaseChangeEquiv` with the `π₁` pullback/base-change
associativity comparison for a cosimplicial-ring homomorphism. -/
lemma homBaseChangeEquiv_pullbackBaseChangeπ₁Assoc
    (M N : Type*) [AddCommGroup M] [Module C.R₁ M]
    [Module.Finite C.R₁ M] [Module.Projective C.R₁ M]
    [AddCommGroup N] [Module C.R₁ N]
    [Module.Finite C.R₁ N] [Module.Projective C.R₁ N]
    (x : baseChange_along D.π₁ (baseChange_along F.f₁ (M →ₗ[C.R₁] N))) :
    letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
    letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
    letI : Algebra C.R₁ D.R₂ := (D.π₁.comp F.f₁).toAlgebra
    letI : Module.Finite D.R₁ (baseChange_along F.f₁ M) :=
      Module.Finite.base_change C.R₁ D.R₁ M
    letI : Module.Projective D.R₁ (baseChange_along F.f₁ M) :=
      Novikov.Miscellany.baseChange_projective M
    letI : Module.Finite D.R₁ (baseChange_along F.f₁ N) :=
      Module.Finite.base_change C.R₁ D.R₁ N
    letI : Module.Projective D.R₁ (baseChange_along F.f₁ N) :=
      Novikov.Miscellany.baseChange_projective N
    (F.pullbackBaseChangeπ₁Assoc N).toLinearMap ∘ₗ
        (homBaseChangeEquiv (R := D.R₁) (M := baseChange_along F.f₁ M)
          (N := baseChange_along F.f₁ N) D.R₂)
          ((LinearMap.baseChange D.R₂
            (homBaseChangeEquiv (R := C.R₁) (M := M) (N := N) D.R₁).toLinearMap) x) =
      (homBaseChangeEquiv (R := C.R₁) (M := M) (N := N) D.R₂)
          ((F.pullbackBaseChangeπ₁Assoc (M →ₗ[C.R₁] N)).toLinearMap x) ∘ₗ
        (F.pullbackBaseChangeπ₁Assoc M).toLinearMap := by
  apply LinearMap.ext
  intro y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
      simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_apply]
      rw [hx₁, hx₂]
  | tmul a x0 =>
      induction x0 using TensorProduct.induction_on with
      | zero => simp
      | add x₁ x₂ hx₁ hx₂ =>
          letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
          rw [TensorProduct.tmul_add]
          simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_apply]
          rw [hx₁, hx₂]
      | tmul b η =>
          induction y using TensorProduct.induction_on with
          | zero => simp
          | add y₁ y₂ hy₁ hy₂ =>
              simp only [map_add, LinearMap.add_apply]
              rw [hy₁, hy₂]
          | tmul c y0 =>
              induction y0 using TensorProduct.induction_on with
              | zero => simp
              | add y₁ y₂ hy₁ hy₂ =>
                  letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
                  rw [TensorProduct.tmul_add]
                  simp only [map_add, LinearMap.add_apply]
                  rw [hy₁, hy₂]
              | tmul d m =>
                  simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
                    homBaseChangeEquiv_tmul, LinearMap.baseChange_smul,
                    LinearMap.coe_comp, LinearMap.coe_smul, Function.comp_apply,
                    Pi.smul_apply, map_smul, pullbackBaseChangeπ₁Assoc_tmul]
                  letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
                  have hp := F.pullbackBaseChangeπ₁Assoc_tmul N (b • c) d (η m)
                  exact (congrArg (fun z => a • z) hp).trans (by
                    letI : Algebra C.R₁ D.R₂ := (D.π₁.comp F.f₁).toAlgebra
                    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
                    congr 1
                    simp [Algebra.smul_def]
                    ring_nf)

set_option linter.unusedSimpArgs false in
/-- Compatibility of `homBaseChangeEquiv` with the `π₂` pullback/base-change
associativity comparison for a cosimplicial-ring homomorphism. -/
lemma homBaseChangeEquiv_pullbackBaseChangeπ₂Assoc
    (M N : Type*) [AddCommGroup M] [Module C.R₁ M]
    [Module.Finite C.R₁ M] [Module.Projective C.R₁ M]
    [AddCommGroup N] [Module C.R₁ N]
    [Module.Finite C.R₁ N] [Module.Projective C.R₁ N]
    (x : baseChange_along D.π₂ (baseChange_along F.f₁ (M →ₗ[C.R₁] N))) :
    letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
    letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    letI : Algebra C.R₁ D.R₂ := (D.π₂.comp F.f₁).toAlgebra
    letI : Module.Finite D.R₁ (baseChange_along F.f₁ M) :=
      Module.Finite.base_change C.R₁ D.R₁ M
    letI : Module.Projective D.R₁ (baseChange_along F.f₁ M) :=
      Novikov.Miscellany.baseChange_projective M
    letI : Module.Finite D.R₁ (baseChange_along F.f₁ N) :=
      Module.Finite.base_change C.R₁ D.R₁ N
    letI : Module.Projective D.R₁ (baseChange_along F.f₁ N) :=
      Novikov.Miscellany.baseChange_projective N
    (F.pullbackBaseChangeπ₂Assoc N).toLinearMap ∘ₗ
        (homBaseChangeEquiv (R := D.R₁) (M := baseChange_along F.f₁ M)
          (N := baseChange_along F.f₁ N) D.R₂)
          ((LinearMap.baseChange D.R₂
            (homBaseChangeEquiv (R := C.R₁) (M := M) (N := N) D.R₁).toLinearMap) x) =
      (homBaseChangeEquiv (R := C.R₁) (M := M) (N := N) D.R₂)
          ((F.pullbackBaseChangeπ₂Assoc (M →ₗ[C.R₁] N)).toLinearMap x) ∘ₗ
        (F.pullbackBaseChangeπ₂Assoc M).toLinearMap := by
  apply LinearMap.ext
  intro y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
      simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_apply]
      rw [hx₁, hx₂]
  | tmul a x0 =>
      induction x0 using TensorProduct.induction_on with
      | zero => simp
      | add x₁ x₂ hx₁ hx₂ =>
          letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
          rw [TensorProduct.tmul_add]
          simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_apply]
          rw [hx₁, hx₂]
      | tmul b η =>
          induction y using TensorProduct.induction_on with
          | zero => simp
          | add y₁ y₂ hy₁ hy₂ =>
              simp only [map_add, LinearMap.add_apply]
              rw [hy₁, hy₂]
          | tmul c y0 =>
              induction y0 using TensorProduct.induction_on with
              | zero => simp
              | add y₁ y₂ hy₁ hy₂ =>
                  letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
                  rw [TensorProduct.tmul_add]
                  simp only [map_add, LinearMap.add_apply]
                  rw [hy₁, hy₂]
              | tmul d m =>
                  simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
                    homBaseChangeEquiv_tmul, LinearMap.baseChange_smul,
                    LinearMap.coe_comp, LinearMap.coe_smul, Function.comp_apply,
                    Pi.smul_apply, map_smul, pullbackBaseChangeπ₂Assoc_tmul]
                  letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
                  have hp := F.pullbackBaseChangeπ₂Assoc_tmul N (b • c) d (η m)
                  exact (congrArg (fun z => a • z) hp).trans (by
                    letI : Algebra C.R₁ D.R₂ := (D.π₂.comp F.f₁).toAlgebra
                    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
                    congr 1
                    simp [Algebra.smul_def]
                    ring_nf)

/-- The underlying linear map from the base change of an internal Hom to the
internal Hom of the base-changed descent data. -/
noncomputable def baseChangeInternalHomLinearMap (M N : DescentDatum C) :
    ((DescentDatum.internalHom M N).baseChange F).M →ₗ[D.R₁]
      (DescentDatum.internalHom (M.baseChange F) (N.baseChange F)).M := by
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  dsimp [DescentDatum.internalHom, DescentDatum.baseChange]
  exact (Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M) (N := N.M) D.R₁).toLinearMap

@[simp]
lemma baseChangeInternalHomLinearMap_apply (M N : DescentDatum C)
    (x : ((DescentDatum.internalHom M N).baseChange F).M)
    (y : (M.baseChange F).M) :
    (show (M.baseChange F).M →ₗ[D.R₁] (N.baseChange F).M from
      F.baseChangeInternalHomLinearMap M N x) y =
      ((letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
        Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M) (N := N.M) D.R₁) x) y := by
  rfl

set_option linter.unusedSimpArgs false in
/-- The underlying linear map `baseChangeInternalHomLinearMap` commutes with the
internal-Hom descent isomorphisms. -/
lemma baseChangeInternalHomLinearMap_commute_φ (M N : DescentDatum C) :
    (DescentDatum.internalHom (M.baseChange F) (N.baseChange F)).φ.toLinearMap ∘ₗ
        (letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
         LinearMap.baseChange D.R₂ (F.baseChangeInternalHomLinearMap M N)) =
      (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
       LinearMap.baseChange D.R₂ (F.baseChangeInternalHomLinearMap M N)) ∘ₗ
        ((DescentDatum.internalHom M N).baseChange F).φ.toLinearMap := by
    letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
    let A : DescentDatum D := M.baseChange F
    let B : DescentDatum D := N.baseChange F
    let MN : DescentDatum C := DescentDatum.internalHom M N
    let H1C := letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
      Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M) (N := N.M) D.R₁
    let H1D := letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
      Novikov.Miscellany.homBaseChangeEquiv (R := D.R₁) (M := A.M) (N := B.M) D.R₂
    let H2D := letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
      Novikov.Miscellany.homBaseChangeEquiv (R := D.R₁) (M := A.M) (N := B.M) D.R₂
    let Hπ₁C := letI : Algebra C.R₁ D.R₂ := (D.π₁.comp F.f₁).toAlgebra
      Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M) (N := N.M) D.R₂
    let Hπ₂C := letI : Algebra C.R₁ D.R₂ := (D.π₂.comp F.f₁).toAlgebra
      Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M) (N := N.M) D.R₂
    let P_M := pullbackMap C.π₁ C.π₂ F.f₂ F.comm_π₁ F.comm_π₂ M.M M.M M.φ
    let P_N := pullbackMap C.π₁ C.π₂ F.f₂ F.comm_π₁ F.comm_π₂ N.M N.M N.φ
    let P_H := pullbackMap C.π₁ C.π₂ F.f₂ F.comm_π₁ F.comm_π₂
      (M.M →ₗ[C.R₁] N.M) (M.M →ₗ[C.R₁] N.M) (DescentDatum.internalHom M N).φ
    change (DescentDatum.internalHom A B).φ.toLinearMap ∘ₗ
        (letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
         LinearMap.baseChange D.R₂ H1C.toLinearMap) =
      (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
       LinearMap.baseChange D.R₂ H1C.toLinearMap) ∘ₗ
        (F.baseChangePhi MN).toLinearMap
    apply LinearMap.ext
    intro x
    apply H2D.injective
    apply LinearMap.ext
    intro y
    apply (F.pullbackBaseChangeπ₂Assoc N.M).injective
    simp only [LinearMap.comp_apply]
    have hleftConj := homBaseChangeEquiv_homConj D.π₁ D.π₂ A.M B.M A.φ B.φ
      ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra;
        LinearMap.baseChange D.R₂ H1C.toLinearMap) x)
    change H2D ((DescentDatum.internalHom A B).φ
        ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra;
          LinearMap.baseChange D.R₂ H1C.toLinearMap) x)) =
      B.φ.toLinearMap ∘ₗ H1D ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra;
          LinearMap.baseChange D.R₂ H1C.toLinearMap) x) ∘ₗ A.φ.symm.toLinearMap at hleftConj
    have hleft_y := LinearMap.congr_fun hleftConj y
    simp only [LinearMap.comp_apply] at hleft_y
    change (F.pullbackBaseChangeπ₂Assoc N.M)
        ((H2D ((DescentDatum.internalHom A B).φ
          ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra;
            LinearMap.baseChange D.R₂ H1C.toLinearMap) x))) y) =
      (F.pullbackBaseChangeπ₂Assoc N.M)
        ((H2D ((letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra;
          LinearMap.baseChange D.R₂ H1C.toLinearMap) (F.baseChangePhi MN x))) y)
    rw [hleft_y]
    have hB := LinearMap.congr_fun (F.baseChangePhi_assoc N)
      ((H1D ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra;
          LinearMap.baseChange D.R₂ H1C.toLinearMap) x)) (A.φ.symm y))
    change (F.pullbackBaseChangeπ₂Assoc N.M)
        (B.φ ((H1D ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra;
          LinearMap.baseChange D.R₂ H1C.toLinearMap) x)) (A.φ.symm y))) =
      P_N ((F.pullbackBaseChangeπ₁Assoc N.M)
        ((H1D ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra;
          LinearMap.baseChange D.R₂ H1C.toLinearMap) x)) (A.φ.symm y))) at hB
    change (F.pullbackBaseChangeπ₂Assoc N.M)
        (B.φ ((H1D ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra;
          LinearMap.baseChange D.R₂ H1C.toLinearMap) x)) (A.φ.symm y))) =
      (F.pullbackBaseChangeπ₂Assoc N.M)
        ((H2D ((letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra;
          LinearMap.baseChange D.R₂ H1C.toLinearMap) (F.baseChangePhi MN x))) y)
    rw [hB]
    have hH1 := LinearMap.congr_fun
      (F.homBaseChangeEquiv_pullbackBaseChangeπ₁Assoc M.M N.M x) (A.φ.symm y)
    change (F.pullbackBaseChangeπ₁Assoc N.M)
        ((H1D ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra;
          LinearMap.baseChange D.R₂ H1C.toLinearMap) x)) (A.φ.symm y)) =
      (Hπ₁C ((F.pullbackBaseChangeπ₁Assoc (M.M →ₗ[C.R₁] N.M)) x))
        ((F.pullbackBaseChangeπ₁Assoc M.M) (A.φ.symm y)) at hH1
    rw [hH1]
    have hMsymm := LinearMap.congr_fun (F.baseChangePhi_assoc_symm M) y
    change (F.pullbackBaseChangeπ₁Assoc M.M) (A.φ.symm y) =
      P_M.symm ((F.pullbackBaseChangeπ₂Assoc M.M) y) at hMsymm
    rw [hMsymm]
    have hH2 := LinearMap.congr_fun
      (F.homBaseChangeEquiv_pullbackBaseChangeπ₂Assoc M.M N.M (F.baseChangePhi MN x)) y
    change (F.pullbackBaseChangeπ₂Assoc N.M)
      ((H2D ((letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra;
        LinearMap.baseChange D.R₂ H1C.toLinearMap) (F.baseChangePhi MN x))) y) =
      (Hπ₂C ((F.pullbackBaseChangeπ₂Assoc (M.M →ₗ[C.R₁] N.M)) (F.baseChangePhi MN x)))
        ((F.pullbackBaseChangeπ₂Assoc M.M) y) at hH2
    rw [hH2]
    have hMN := LinearMap.congr_fun (F.baseChangePhi_assoc MN) x
    change (F.pullbackBaseChangeπ₂Assoc (M.M →ₗ[C.R₁] N.M)) (F.baseChangePhi MN x) =
      P_H ((F.pullbackBaseChangeπ₁Assoc (M.M →ₗ[C.R₁] N.M)) x) at hMN
    rw [hMN]
    have hconj := conj_lemma C.π₁ C.π₂ F.f₂ F.comm_π₁ F.comm_π₂ M.M N.M M.φ N.φ
      ((F.pullbackBaseChangeπ₁Assoc (M.M →ₗ[C.R₁] N.M)) x)
    change Hπ₂C (P_H ((F.pullbackBaseChangeπ₁Assoc (M.M →ₗ[C.R₁] N.M)) x)) =
      P_N.toLinearMap ∘ₗ
        Hπ₁C ((F.pullbackBaseChangeπ₁Assoc (M.M →ₗ[C.R₁] N.M)) x) ∘ₗ
        P_M.symm.toLinearMap at hconj
    rw [hconj]
    rfl

/-- Base change of internal Homs maps to the internal Hom of the base changes. -/
noncomputable def baseChangeInternalHomHom (M N : DescentDatum C) :
    DescentDatum.Hom ((DescentDatum.internalHom M N).baseChange F)
      (DescentDatum.internalHom (M.baseChange F) (N.baseChange F)) where
  toLinearMap := F.baseChangeInternalHomLinearMap M N
  commute_φ := F.baseChangeInternalHomLinearMap_commute_φ M N

end CosimplicialRingHom

namespace DescentDatum

/-- The dual descent datum, defined as the internal Hom into the structure sheaf. -/
noncomputable def dual {C : CosimplicialRing} (M : DescentDatum C) : DescentDatum C :=
  DescentDatum.internalHom M (structureSheaf C)

@[simp]
lemma dual_M {C : CosimplicialRing} (M : DescentDatum C) :
    M.dual.M = (M.M →ₗ[C.R₁] C.R₁) := rfl

/-- Applying the Hom/base-change equivalence to the descent isomorphism on the
dual datum unwraps it as conjugation by the descent isomorphism of `M` and the
structure sheaf.  This is a lightweight rewrite lemma for later duality
compatibility proofs. -/
lemma dual_φ_homBaseChangeEquiv {C : CosimplicialRing} (M : DescentDatum C)
    (x : π₁s C M.dual.M) :
    (let H2 := letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
        Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M)
          (N := (structureSheaf C).M) C.R₂;
      H2 (M.dual.φ x)) =
    (let H1 := letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
        Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M)
          (N := (structureSheaf C).M) C.R₂;
      (M.φ.arrowCongr (structureSheaf C).φ) (H1 x)) := by
  let H1 := letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M)
      (N := (structureSheaf C).M) C.R₂
  let H2 := letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M)
      (N := (structureSheaf C).M) C.R₂
  change H2 (M.dual.φ x) = (M.φ.arrowCongr (structureSheaf C).φ) (H1 x)
  dsimp [DescentDatum.dual, DescentDatum.internalHom]
  change H2 ((H1.trans ((M.φ.arrowCongr (structureSheaf C).φ).trans H2.symm)) x) = _
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

end DescentDatum

namespace CosimplicialRingHom

variable {C D : CosimplicialRing} (F : CosimplicialRingHom C D)

/-- The underlying linear equivalence comparing base change of a dual descent
module with the dual of the base-changed descent module. -/
noncomputable def baseChangeDualLinearEquiv (M : DescentDatum C) :
    (M.dual.baseChange F).M ≃ₗ[D.R₁] (M.baseChange F).dual.M := by
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  let H := Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M) (N := C.R₁) D.R₁
  let e := baseChangeSelfEquiv F.f₁
  let L : (M.dual.baseChange F).M →ₗ[D.R₁] (M.baseChange F).dual.M := {
    toFun := fun x => e.toLinearMap.comp (H x)
    map_add' := by
      intro x y
      apply LinearMap.ext
      intro z
      change e.toLinearMap ((H (x + y)) z) =
        e.toLinearMap ((H x) z) + e.toLinearMap ((H y) z)
      have h := LinearMap.congr_fun (map_add H x y) z
      change (H (x + y)) z = (H x + H y) z at h
      rw [h]
      simp only [LinearMap.add_apply]
      exact e.toLinearMap.map_add ((H x) z) ((H y) z)
    map_smul' := by
      intro a x
      apply LinearMap.ext
      intro z
      change e.toLinearMap ((H (a • x)) z) = a • e.toLinearMap ((H x) z)
      have h := LinearMap.congr_fun (map_smul H a x) z
      change (H (a • x)) z = (a • H x) z at h
      rw [h]
      simp only [LinearMap.smul_apply]
      exact e.toLinearMap.map_smul a ((H x) z) }
  let G : (M.baseChange F).dual.M →ₗ[D.R₁] (M.dual.baseChange F).M := {
    toFun := fun y => H.symm (e.symm.toLinearMap.comp y)
    map_add' := by
      intro x y
      change (D.R₁ ⊗[C.R₁] M.M →ₗ[D.R₁] D.R₁) at x y
      apply H.injective
      apply LinearMap.ext
      intro z
      rw [H.apply_symm_apply]
      have hright := LinearMap.congr_fun
        (map_add H (H.symm (e.symm.toLinearMap.comp x))
          (H.symm (e.symm.toLinearMap.comp y))) z
      have hleft : (e.symm.toLinearMap.comp (x + y)) z =
          (e.symm.toLinearMap.comp x + e.symm.toLinearMap.comp y) z := by
        simp only [LinearMap.add_apply, LinearMap.comp_apply]
        exact e.symm.toLinearMap.map_add (x z) (y z)
      have hright' : (H (H.symm (e.symm.toLinearMap.comp x) +
          H.symm (e.symm.toLinearMap.comp y))) z =
          (e.symm.toLinearMap.comp x + e.symm.toLinearMap.comp y) z := by
        rw [hright, H.apply_symm_apply, H.apply_symm_apply]
      exact hleft.trans hright'.symm
    map_smul' := by
      intro a x
      change (D.R₁ ⊗[C.R₁] M.M →ₗ[D.R₁] D.R₁) at x
      apply H.injective
      apply LinearMap.ext
      intro z
      rw [H.apply_symm_apply]
      have hright := LinearMap.congr_fun
        (map_smul H a (H.symm (e.symm.toLinearMap.comp x))) z
      have hleft : (e.symm.toLinearMap.comp (a • x)) z =
          (a • e.symm.toLinearMap.comp x) z := by
        simp only [LinearMap.smul_apply, LinearMap.comp_apply]
        exact e.symm.toLinearMap.map_smul a (x z)
      have hright' : (H (a • H.symm (e.symm.toLinearMap.comp x))) z =
          (a • e.symm.toLinearMap.comp x) z := by
        rw [hright, H.apply_symm_apply]
      exact hleft.trans hright'.symm }
  refine LinearEquiv.ofLinear L G ?_ ?_
  · apply LinearMap.ext
    intro y
    let y' : D.R₁ ⊗[C.R₁] M.M →ₗ[D.R₁] D.R₁ := y
    change e.toLinearMap.comp (H (H.symm (e.symm.toLinearMap.comp y'))) = y'
    rw [H.apply_symm_apply]
    apply LinearMap.ext
    intro z
    change e.toLinearMap (e.symm.toLinearMap (y' z)) = y' z
    exact e.right_inv (y' z)
  · apply LinearMap.ext
    intro x
    apply H.injective
    change H (H.symm (e.symm.toLinearMap.comp (e.toLinearMap.comp (H x)))) = H x
    rw [H.apply_symm_apply]
    change e.symm.toLinearMap.comp (e.toLinearMap.comp (H x)) = H x
    apply LinearMap.ext
    intro z
    change e.symm.toLinearMap (e.toLinearMap ((H x) z)) = (H x) z
    exact e.left_inv ((H x) z)

@[simp]
lemma baseChangeDualLinearEquiv_apply (M : DescentDatum C)
    (x : (M.dual.baseChange F).M) (y : (M.baseChange F).M) :
    (let h : (M.baseChange F).M →ₗ[D.R₁] D.R₁ := baseChangeDualLinearEquiv F M x;
      h y) =
      (baseChangeSelfEquiv F.f₁)
        (((letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra;
          Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M)
            (N := C.R₁) D.R₁) x) y) := rfl

/-- Compatibility of the base-change/dual comparison with double-dual evaluation:
base-changing the inverse of `Module.evalEquiv` and then pairing with a
base-changed functional agrees with first viewing the double-dual element via
`baseChangeDualLinearEquiv`. -/
lemma baseChangeDualLinearEquiv_doubleDual_symm_apply (M : DescentDatum C)
    (z : (M.dual.dual.baseChange F).M) (x : (M.dual.baseChange F).M) :
    (let β : (M.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M x
     β ((letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
       LinearMap.baseChange D.R₁ (Module.evalEquiv C.R₁ M.M).symm.toLinearMap) z)) =
    (let γ : (M.dual.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M.dual z
     γ x) := by
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  let bcEval : (M.dual.dual.baseChange F).M →ₗ[D.R₁] (M.baseChange F).M :=
    LinearMap.baseChange D.R₁ (Module.evalEquiv C.R₁ M.M).symm.toLinearMap
  change (show (M.baseChange F).M →ₗ[D.R₁] D.R₁ from F.baseChangeDualLinearEquiv M x)
      (bcEval z) =
    (show (M.dual.baseChange F).M →ₗ[D.R₁] D.R₁ from F.baseChangeDualLinearEquiv M.dual z) x
  induction z using TensorProduct.induction_on generalizing x with
  | zero =>
      let L : (M.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M x
      let γ0 : (M.dual.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M.dual 0
      change L (bcEval 0) = γ0 x
      calc
        L (bcEval 0) = L 0 := by rw [map_zero bcEval]
        _ = 0 := map_zero L
        _ = γ0 x := by
          have hγ0 : γ0 = 0 := by
            exact map_zero (F.baseChangeDualLinearEquiv M.dual)
          rw [hγ0]
          rfl
  | add z₁ z₂ hz₁ hz₂ =>
      let L : (M.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M x
      let γsum : (M.dual.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M.dual (z₁ + z₂)
      let γ₁ : (M.dual.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M.dual z₁
      let γ₂ : (M.dual.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M.dual z₂
      change L (bcEval (z₁ + z₂)) = γsum x
      calc
        L (bcEval (z₁ + z₂)) = L (bcEval z₁ + bcEval z₂) := by
          exact congrArg L (map_add bcEval z₁ z₂)
        _ = L (bcEval z₁) + L (bcEval z₂) := map_add L _ _
        _ = γ₁ x + γ₂ x := by
          rw [show L (bcEval z₁) = γ₁ x by simpa [L, γ₁, bcEval] using hz₁ x]
          rw [show L (bcEval z₂) = γ₂ x by simpa [L, γ₂, bcEval] using hz₂ x]
        _ = (γ₁ + γ₂) x := rfl
        _ = γsum x := by
          have hγ : γsum = γ₁ + γ₂ := by
            simpa [γsum, γ₁, γ₂] using map_add (F.baseChangeDualLinearEquiv M.dual) z₁ z₂
          exact (LinearMap.congr_fun hγ x).symm
  | tmul a z0 =>
      induction x using TensorProduct.induction_on with
      | zero =>
          let L0 : (M.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M 0
          let γ : (M.dual.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M.dual (a ⊗ₜ[C.R₁] z0)
          change L0 (bcEval (a ⊗ₜ[C.R₁] z0)) = γ 0
          calc
            L0 (bcEval (a ⊗ₜ[C.R₁] z0)) = 0 := by
              have hL0 : L0 = 0 := by
                exact map_zero (F.baseChangeDualLinearEquiv M)
              rw [hL0]
              rfl
            _ = γ 0 := (map_zero γ).symm
      | add x₁ x₂ hx₁ hx₂ =>
          let Lsum : (M.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M (x₁ + x₂)
          let L₁ : (M.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M x₁
          let L₂ : (M.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M x₂
          let γ : (M.dual.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M.dual (a ⊗ₜ[C.R₁] z0)
          change Lsum (bcEval (a ⊗ₜ[C.R₁] z0)) = γ (x₁ + x₂)
          calc
            Lsum (bcEval (a ⊗ₜ[C.R₁] z0)) = (L₁ + L₂) (bcEval (a ⊗ₜ[C.R₁] z0)) := by
              have hL : Lsum = L₁ + L₂ := by
                simpa [Lsum, L₁, L₂] using map_add (F.baseChangeDualLinearEquiv M) x₁ x₂
              exact LinearMap.congr_fun hL _
            _ = L₁ (bcEval (a ⊗ₜ[C.R₁] z0)) + L₂ (bcEval (a ⊗ₜ[C.R₁] z0)) := rfl
            _ = γ x₁ + γ x₂ := by
              rw [show L₁ (bcEval (a ⊗ₜ[C.R₁] z0)) = γ x₁ by simpa [L₁, γ, bcEval] using hx₁]
              rw [show L₂ (bcEval (a ⊗ₜ[C.R₁] z0)) = γ x₂ by simpa [L₂, γ, bcEval] using hx₂]
            _ = γ (x₁ + x₂) := (map_add γ x₁ x₂).symm
      | tmul b x0 =>
          change (show (M.baseChange F).M →ₗ[D.R₁] D.R₁ from
              F.baseChangeDualLinearEquiv M (b ⊗ₜ[C.R₁] x0))
              (bcEval (a ⊗ₜ[C.R₁] z0)) =
            (show (M.dual.baseChange F).M →ₗ[D.R₁] D.R₁ from
              F.baseChangeDualLinearEquiv M.dual (a ⊗ₜ[C.R₁] z0)) (b ⊗ₜ[C.R₁] x0)
          dsimp [bcEval]
          have hbc :
              (LinearMap.baseChange D.R₁ (Module.evalEquiv C.R₁ M.M).symm.toLinearMap)
                (a ⊗ₜ[C.R₁] z0) =
              a ⊗ₜ[C.R₁] ((Module.evalEquiv C.R₁ M.M).symm.toLinearMap z0) := by
            exact LinearMap.baseChange_tmul (Module.evalEquiv C.R₁ M.M).symm.toLinearMap a z0
          calc
            (show (M.baseChange F).M →ₗ[D.R₁] D.R₁ from
                F.baseChangeDualLinearEquiv M (b ⊗ₜ[C.R₁] x0))
                ((LinearMap.baseChange D.R₁ (Module.evalEquiv C.R₁ M.M).symm.toLinearMap)
                  (a ⊗ₜ[C.R₁] z0)) =
              (show (M.baseChange F).M →ₗ[D.R₁] D.R₁ from
                F.baseChangeDualLinearEquiv M (b ⊗ₜ[C.R₁] x0))
                (a ⊗ₜ[C.R₁] ((Module.evalEquiv C.R₁ M.M).symm.toLinearMap z0)) := by
                exact congrArg (fun u =>
                  (show (M.baseChange F).M →ₗ[D.R₁] D.R₁ from
                    F.baseChangeDualLinearEquiv M (b ⊗ₜ[C.R₁] x0)) u) hbc
            _ = (show (M.dual.baseChange F).M →ₗ[D.R₁] D.R₁ from
                F.baseChangeDualLinearEquiv M.dual (a ⊗ₜ[C.R₁] z0)) (b ⊗ₜ[C.R₁] x0) := by
              rw [baseChangeDualLinearEquiv_apply, baseChangeDualLinearEquiv_apply]
              change (baseChangeSelfEquiv F.f₁)
                  (((homBaseChangeEquiv D.R₁) (b ⊗ₜ[C.R₁] x0))
                    (a ⊗ₜ[C.R₁] ((Module.evalEquiv C.R₁ M.M).symm z0))) =
                (baseChangeSelfEquiv F.f₁)
                  (((homBaseChangeEquiv D.R₁) (a ⊗ₜ[C.R₁] z0)) (b ⊗ₜ[C.R₁] x0))
              rw [homBaseChangeEquiv_tmul, homBaseChangeEquiv_tmul]
              simp only [LinearMap.smul_apply, LinearMap.baseChange_tmul]
              change (baseChangeSelfEquiv F.f₁)
                  (b • a ⊗ₜ[C.R₁]
                    ((show Module.Dual C.R₁ M.M from x0)
                      ((Module.evalEquiv C.R₁ M.M).symm
                        (show Module.Dual C.R₁ (Module.Dual C.R₁ M.M) from z0)))) =
                (baseChangeSelfEquiv F.f₁)
                  (a • b ⊗ₜ[C.R₁]
                    ((show Module.Dual C.R₁ (Module.Dual C.R₁ M.M) from z0)
                      (show Module.Dual C.R₁ M.M from x0)))
              rw [Module.apply_evalEquiv_symm_apply C.R₁ M.M
                (show Module.Dual C.R₁ M.M from x0)
                (show Module.Dual C.R₁ (Module.Dual C.R₁ M.M) from z0)]
              simp [baseChangeSelfEquiv_tmul, Algebra.smul_def]
              ring

end CosimplicialRingHom

namespace DescentDatum

/-- Postcomposition by a morphism of descent data induces a morphism on internal Homs. -/
noncomputable def internalHomCongrRightHom {C : CosimplicialRing}
    (A B D : DescentDatum C) (i : B ≅ D) :
    DescentDatum.internalHom A B ⟶ DescentDatum.internalHom A D := by
  let postcomp : (A.M →ₗ[C.R₁] B.M) →ₗ[C.R₁] (A.M →ₗ[C.R₁] D.M) :=
    { toFun := fun g => i.hom.toLinearMap.comp g
      map_add' := by intro g h; ext x; simp
      map_smul' := by intro r g; ext x; simp }
  refine { toLinearMap := postcomp, commute_φ := ?_ }
  let H1B := letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := A.M) (N := B.M) C.R₂
  let H2B := letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := A.M) (N := B.M) C.R₂
  let H1D := letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := A.M) (N := D.M) C.R₂
  let H2D := letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := A.M) (N := D.M) C.R₂
  let bc1i := letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
    LinearMap.baseChange C.R₂ i.hom.toLinearMap
  let bc2i := letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
    LinearMap.baseChange C.R₂ i.hom.toLinearMap
  apply LinearMap.ext
  intro x
  apply H2D.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hpost1 : H1D ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
        LinearMap.baseChange C.R₂ postcomp) x) = bc1i ∘ₗ H1B x := by
    letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
    exact homBaseChangeEquiv_postcomp (S := C.R₂) i.hom.toLinearMap x
  have hpost2 (y : π₂s C (A.M →ₗ[C.R₁] B.M)) :
      H2D ((letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
        LinearMap.baseChange C.R₂ postcomp) y) = bc2i ∘ₗ H2B y := by
    letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
    exact homBaseChangeEquiv_postcomp (S := C.R₂) i.hom.toLinearMap y
  dsimp [DescentDatum.internalHom]
  have hleft := homBaseChangeEquiv_homConj C.π₁ C.π₂ A.M D.M A.φ D.φ
    ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; LinearMap.baseChange C.R₂ postcomp) x)
  change H2D ((homConj C.π₁ C.π₂ A.M D.M A.φ D.φ)
      ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; LinearMap.baseChange C.R₂ postcomp) x)) =
    D.φ.toLinearMap ∘ₗ
      H1D ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; LinearMap.baseChange C.R₂ postcomp) x) ∘ₗ
      A.φ.symm.toLinearMap at hleft
  change H2D ((homConj C.π₁ C.π₂ A.M D.M A.φ D.φ)
      ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; LinearMap.baseChange C.R₂ postcomp) x)) =
    H2D ((letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra; LinearMap.baseChange C.R₂ postcomp)
      ((homConj C.π₁ C.π₂ A.M B.M A.φ B.φ) x))
  rw [hleft, hpost1]
  have hright0 := hpost2 ((homConj C.π₁ C.π₂ A.M B.M A.φ B.φ) x)
  rw [hright0]
  have hright := homBaseChangeEquiv_homConj C.π₁ C.π₂ A.M B.M A.φ B.φ x
  change H2B ((homConj C.π₁ C.π₂ A.M B.M A.φ B.φ) x) =
    B.φ.toLinearMap ∘ₗ H1B x ∘ₗ A.φ.symm.toLinearMap at hright
  rw [hright]
  ext y
  simp only [LinearMap.comp_apply]
  have hcomm := LinearMap.congr_fun i.hom.commute_φ ((H1B x) (A.φ.symm y))
  simp only [LinearMap.comp_apply] at hcomm
  exact hcomm

/-- An isomorphism in the codomain induces an isomorphism on internal Homs. -/
noncomputable def internalHomCongrRight {C : CosimplicialRing}
    (A B D : DescentDatum C) (i : B ≅ D) :
    DescentDatum.internalHom A B ≅ DescentDatum.internalHom A D where
  hom := internalHomCongrRightHom A B D i
  inv := internalHomCongrRightHom A D B i.symm
  hom_inv_id := by
    apply DescentDatum.hom_ext
    apply LinearMap.ext
    intro f
    change A.M →ₗ[C.R₁] B.M at f
    apply LinearMap.ext
    intro x
    change i.inv.toLinearMap (i.hom.toLinearMap (f x)) = f x
    have hlin : i.inv.toLinearMap ∘ₗ i.hom.toLinearMap = LinearMap.id :=
      congrArg DescentDatum.Hom.toLinearMap i.hom_inv_id
    exact LinearMap.congr_fun hlin (f x)
  inv_hom_id := by
    apply DescentDatum.hom_ext
    apply LinearMap.ext
    intro f
    change A.M →ₗ[C.R₁] D.M at f
    apply LinearMap.ext
    intro x
    change i.hom.toLinearMap (i.inv.toLinearMap (f x)) = f x
    have hlin : i.hom.toLinearMap ∘ₗ i.inv.toLinearMap = LinearMap.id :=
      congrArg DescentDatum.Hom.toLinearMap i.inv_hom_id
    exact LinearMap.congr_fun hlin (f x)

end DescentDatum

/-- The dual of a constant descent datum is the constant descent datum of the
ordinary dual module. -/
noncomputable def constantDescentDatum_dual (E : ExtendedCosimplicialRing)
    (M : Type*) [AddCommGroup M] [Module E.R₀ M]
    [Module.Finite E.R₀ M] [Module.Projective E.R₀ M] :
    constantDescentDatum E (M →ₗ[E.R₀] E.R₀) ≅ (constantDescentDatum E M).dual :=
  Iso.trans (constantDescentDatum_internalHom E M E.R₀)
    (DescentDatum.internalHomCongrRight (constantDescentDatum E M)
      (constantDescentDatum E E.R₀) (structureSheaf E.toCosimplicialRing)
      (constantDescentDatumUnitIso E))

namespace DescentDatum.Hom

variable {C : CosimplicialRing} {M N : DescentDatum C}

/-- Dual of a morphism of descent data, obtained by precomposition. -/
noncomputable def dual (f : M ⟶ N) : N.dual ⟶ M.dual := by
  let precomp : (N.M →ₗ[C.R₁] C.R₁) →ₗ[C.R₁] (M.M →ₗ[C.R₁] C.R₁) :=
    { toFun := fun g => g.comp f.toLinearMap
      map_add' := by intro g h; ext x; simp
      map_smul' := by intro r g; ext x; simp }
  refine { toLinearMap := precomp, commute_φ := ?_ }
  let O : DescentDatum C := structureSheaf C
  let H1M := letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M) (N := O.M) C.R₂
  let H2M := letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M) (N := O.M) C.R₂
  let H1N := letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := N.M) (N := O.M) C.R₂
  let H2N := letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := N.M) (N := O.M) C.R₂
  let bc1f := letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
    LinearMap.baseChange C.R₂ f.toLinearMap
  let bc2f := letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
    LinearMap.baseChange C.R₂ f.toLinearMap
  apply LinearMap.ext
  intro x
  apply H2M.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hpre1 : H1M ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
        LinearMap.baseChange C.R₂ precomp) x) = H1N x ∘ₗ bc1f := by
    letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
    exact homBaseChangeEquiv_precomp (S := C.R₂) f.toLinearMap x
  have hpre2 (y : π₂s C (N.M →ₗ[C.R₁] C.R₁)) :
      H2M ((letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
          LinearMap.baseChange C.R₂ precomp) y) = H2N y ∘ₗ bc2f := by
    letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
    exact homBaseChangeEquiv_precomp (S := C.R₂) f.toLinearMap y
  have hf_symm : bc1f ∘ₗ M.φ.symm.toLinearMap =
      N.φ.symm.toLinearMap ∘ₗ bc2f := by
    apply LinearMap.ext
    intro y
    have h := LinearMap.congr_fun f.commute_φ (M.φ.symm y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h, LinearEquiv.symm_apply_apply]
  dsimp [DescentDatum.dual, DescentDatum.internalHom]
  have hleft := homBaseChangeEquiv_homConj C.π₁ C.π₂ M.M O.M M.φ O.φ
    ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; LinearMap.baseChange C.R₂ precomp) x)
  change H2M ((homConj C.π₁ C.π₂ M.M O.M M.φ O.φ)
      ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; LinearMap.baseChange C.R₂ precomp) x)) =
    O.φ.toLinearMap ∘ₗ
      (H1M ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; LinearMap.baseChange C.R₂ precomp) x)) ∘ₗ
      M.φ.symm.toLinearMap at hleft
  change H2M ((homConj C.π₁ C.π₂ M.M O.M M.φ O.φ)
      ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; LinearMap.baseChange C.R₂ precomp) x)) =
    H2M ((letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra; LinearMap.baseChange C.R₂ precomp)
      ((homConj C.π₁ C.π₂ N.M O.M N.φ O.φ) x))
  rw [hleft, hpre1]
  have hright0 := hpre2 ((homConj C.π₁ C.π₂ N.M O.M N.φ O.φ) x)
  rw [hright0]
  have hright := homBaseChangeEquiv_homConj C.π₁ C.π₂ N.M O.M N.φ O.φ x
  change H2N ((homConj C.π₁ C.π₂ N.M O.M N.φ O.φ) x) =
    O.φ.toLinearMap ∘ₗ H1N x ∘ₗ N.φ.symm.toLinearMap at hright
  rw [hright]
  ext y
  simp only [LinearMap.comp_apply]
  have h_eval := LinearMap.congr_fun hf_symm y
  simp only [LinearMap.comp_apply] at h_eval
  rw [← h_eval]

@[simp]
lemma dual_toLinearMap_apply {C : CosimplicialRing} {M N : DescentDatum C}
    (f : M ⟶ N) (g : N.M →ₗ[C.R₁] C.R₁) :
    f.dual.toLinearMap g = g.comp f.toLinearMap := rfl

end DescentDatum.Hom

namespace CosimplicialRingHom

variable {C D : CosimplicialRing} (F : CosimplicialRingHom C D)

/-- Base change of a dual descent datum maps canonically to the dual of the
base-changed descent datum. -/
noncomputable def baseChangeDualHom (M : DescentDatum C) :
    DescentDatum.Hom (M.dual.baseChange F) ((M.baseChange F).dual) :=
  F.baseChangeInternalHomHom M (structureSheaf C) ≫
    DescentDatum.internalHomCongrRightHom (M.baseChange F)
      ((structureSheaf C).baseChange F) (structureSheaf D)
      (F.structureSheafBaseChangeIso)

@[simp]
lemma baseChangeDualHom_toLinearMap (M : DescentDatum C) :
    (F.baseChangeDualHom M).toLinearMap =
      (F.baseChangeDualLinearEquiv M).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

/-- The inverse morphism to `baseChangeDualHom`, with underlying linear map the
inverse of `baseChangeDualLinearEquiv`.  We keep this as a `DescentDatum.Hom`
rather than an abstract `Iso`, since the two abstract descent objects can live in
slightly different universe levels even though their Hom type is well formed. -/
noncomputable def baseChangeDualInvHom (M : DescentDatum C) :
    DescentDatum.Hom ((M.baseChange F).dual) (M.dual.baseChange F) := by
  let e := F.baseChangeDualLinearEquiv M
  refine { toLinearMap := e.symm.toLinearMap, commute_φ := ?_ }
  let B := letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
    LinearEquiv.baseChange D.R₁ D.R₂ _ _ e
  let G := letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    LinearEquiv.baseChange D.R₁ D.R₂ _ _ e
  have h := (F.baseChangeDualHom M).commute_φ
  rw [F.baseChangeDualHom_toLinearMap M] at h
  exact linearMap_comp_symm_of_comp (B := B) (C := G) h

@[simp]
lemma baseChangeDualInvHom_toLinearMap (M : DescentDatum C) :
    (F.baseChangeDualInvHom M).toLinearMap =
      (F.baseChangeDualLinearEquiv M).symm.toLinearMap := rfl

/-- The base-change/dual linear equivalence is natural for dual morphisms, at
 the level of pairings. -/
lemma baseChangeDualLinearEquiv_dual_apply {A B : DescentDatum C} (f : A ⟶ B)
    (x : (B.dual.baseChange F).M) (y : (A.baseChange F).M) :
    (let β : (A.baseChange F).M →ₗ[D.R₁] D.R₁ :=
      baseChangeDualLinearEquiv F A
        ((DescentDatum.Hom.baseChange F f.dual).toLinearMap x)
     β y) =
    (let α : (B.baseChange F).M →ₗ[D.R₁] D.R₁ :=
      baseChangeDualLinearEquiv F B x
     α ((DescentDatum.Hom.baseChange F f).toLinearMap y)) := by
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  let H_A := Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := A.M)
    (N := C.R₁) D.R₁
  let H_B := Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := B.M)
    (N := C.R₁) D.R₁
  let precomp : (B.M →ₗ[C.R₁] C.R₁) →ₗ[C.R₁] (A.M →ₗ[C.R₁] C.R₁) :=
    { toFun := fun g => g.comp f.toLinearMap
      map_add' := by intro g h; ext m; simp
      map_smul' := by intro r g; ext m; simp }
  have hpre : H_A ((LinearMap.baseChange D.R₁ precomp) x) =
      H_B x ∘ₗ LinearMap.baseChange D.R₁ f.toLinearMap := by
    simpa [H_A, H_B, precomp] using
      (homBaseChangeEquiv_precomp (S := D.R₁) f.toLinearMap x)
  rw [baseChangeDualLinearEquiv_apply, baseChangeDualLinearEquiv_apply]
  change (baseChangeSelfEquiv F.f₁)
      (H_A ((LinearMap.baseChange D.R₁ precomp) x) y) =
    (baseChangeSelfEquiv F.f₁)
      ((H_B x) ((LinearMap.baseChange D.R₁ f.toLinearMap) y))
  rw [hpre]
  rfl

/-- Evaluation form of naturality for a dualized morphism out of a dual object:
after applying the inverse double-dual evaluation for `M`, pairing with a
base-changed functional agrees with pairing the source functional against the
base-changed original morphism. -/
lemma baseChangeDualLinearEquiv_dual_eval_symm_apply (M : DescentDatum C) {B : DescentDatum C}
    (f : M.dual ⟶ B)
    (x : (B.dual.baseChange F).M) (y : (M.dual.baseChange F).M) :
    (let β : (M.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv M y
     β ((letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
       LinearMap.baseChange D.R₁ (Module.evalEquiv C.R₁ M.M).symm.toLinearMap)
        ((DescentDatum.Hom.baseChange F f.dual).toLinearMap x))) =
    (let α : (B.baseChange F).M →ₗ[D.R₁] D.R₁ := F.baseChangeDualLinearEquiv B x
     α ((DescentDatum.Hom.baseChange F f).toLinearMap y)) := by
  rw [F.baseChangeDualLinearEquiv_doubleDual_symm_apply M]
  exact F.baseChangeDualLinearEquiv_dual_apply f x y

end CosimplicialRingHom

namespace DescentDatum

/-- Taking duals sends an isomorphism of descent data to an isomorphism in the
opposite direction. -/
noncomputable def dualIso {C : CosimplicialRing} {M N : DescentDatum C} (i : M ≅ N) :
    N.dual ≅ M.dual where
  hom := i.hom.dual
  inv := i.inv.dual
  hom_inv_id := by
    apply DescentDatum.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro n
    change (show N.M →ₗ[C.R₁] C.R₁ from f)
        (i.hom.toLinearMap (i.inv.toLinearMap n)) =
      (show N.M →ₗ[C.R₁] C.R₁ from f) n
    have hlin : i.hom.toLinearMap.comp i.inv.toLinearMap = LinearMap.id := by
      exact congrArg DescentDatum.Hom.toLinearMap i.inv_hom_id
    have h := LinearMap.congr_fun hlin n
    exact congrArg (show N.M →ₗ[C.R₁] C.R₁ from f) h
  inv_hom_id := by
    apply DescentDatum.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro m
    change (show M.M →ₗ[C.R₁] C.R₁ from f)
        (i.inv.toLinearMap (i.hom.toLinearMap m)) =
      (show M.M →ₗ[C.R₁] C.R₁ from f) m
    have hlin : i.inv.toLinearMap.comp i.hom.toLinearMap = LinearMap.id := by
      exact congrArg DescentDatum.Hom.toLinearMap i.hom_inv_id
    have h := LinearMap.congr_fun hlin m
    exact congrArg (show M.M →ₗ[C.R₁] C.R₁ from f) h

/-- The canonical double-dual evaluation map as a morphism of descent data. -/
noncomputable def doubleDualHom {C : CosimplicialRing} (M : DescentDatum C) :
    M ⟶ M.dual.dual where
  toLinearMap := (Module.evalEquiv C.R₁ M.M).toLinearMap
  commute_φ := by
    let H1M := letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
      Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M)
        (N := (structureSheaf C).M) C.R₂
    let H2M := letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
      Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M)
        (N := (structureSheaf C).M) C.R₂
    let H1D := letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
      Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.dual.M)
        (N := (structureSheaf C).M) C.R₂
    let H2D := letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
      Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.dual.M)
        (N := (structureSheaf C).M) C.R₂
    apply LinearMap.ext
    intro x
    apply H2D.injective
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply]
    have hleft := homBaseChangeEquiv_homConj C.π₁ C.π₂ M.dual.M (structureSheaf C).M
      M.dual.φ (structureSheaf C).φ
      ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra;
        LinearMap.baseChange C.R₂ (Module.evalEquiv C.R₁ M.M).toLinearMap) x)
    rw [Module.evalEquiv_toLinearMap] at hleft
    have hleft_y := congrArg (fun f :
        (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra;
          C.R₂ ⊗[C.R₁] M.dual.M →ₗ[C.R₂]
            C.R₂ ⊗[C.R₁] (structureSheaf C).M) => f y) hleft
    rw [Module.evalEquiv_toLinearMap]
    change (fun f : (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra;
        C.R₂ ⊗[C.R₁] M.dual.M →ₗ[C.R₂] C.R₂ ⊗[C.R₁] (structureSheaf C).M) => f y)
      (((letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra;
        Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.dual.M)
          (N := (structureSheaf C).M) C.R₂)
        ((homConj C.π₁ C.π₂ M.dual.M (structureSheaf C).M M.dual.φ
          (structureSheaf C).φ)
          ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra;
            LinearMap.baseChange C.R₂ (Module.Dual.eval C.R₁ M.M)) x)))) = _
    rw [hleft_y]
    simp only [LinearMap.comp_apply]
    let q := M.dual.φ.symm y
    have heval1 :
        ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra;
          Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.dual.M)
            (N := (structureSheaf C).M) C.R₂)
          ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra;
            LinearMap.baseChange C.R₂ (Module.Dual.eval C.R₁ M.M)) x)) q = H1M q x := by
      letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
      exact Novikov.Miscellany.homBaseChangeEquiv_baseChange_eval_apply (R := C.R₁)
        (S := C.R₂) (M := M.M) x q
    have heval2 :
        ((letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra;
          Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.dual.M)
            (N := (structureSheaf C).M) C.R₂)
          ((letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra;
            LinearMap.baseChange C.R₂ (Module.Dual.eval C.R₁ M.M)) (M.φ x))) y =
        H2M y (M.φ x) := by
      letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
      exact Novikov.Miscellany.homBaseChangeEquiv_baseChange_eval_apply (R := C.R₁)
        (S := C.R₂) (M := M.M) (M.φ x) y
    change (structureSheaf C).φ.toLinearMap
        (((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra;
          Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.dual.M)
            (N := (structureSheaf C).M) C.R₂)
          ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra;
            LinearMap.baseChange C.R₂ (Module.Dual.eval C.R₁ M.M)) x)) q) =
      ((letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra;
        Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.dual.M)
          (N := (structureSheaf C).M) C.R₂)
        ((letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra;
          LinearMap.baseChange C.R₂ (Module.Dual.eval C.R₁ M.M)) (M.φ x))) y
    rw [heval1, heval2]
    have hdual := homBaseChangeEquiv_homConj C.π₁ C.π₂ M.M (structureSheaf C).M M.φ
      (structureSheaf C).φ q
    change H2M ((homConj C.π₁ C.π₂ M.M (structureSheaf C).M M.φ (structureSheaf C).φ) q) =
      (structureSheaf C).φ.toLinearMap ∘ₗ H1M q ∘ₗ M.φ.symm.toLinearMap at hdual
    have hqy : (homConj C.π₁ C.π₂ M.M (structureSheaf C).M M.φ (structureSheaf C).φ) q = y := by
      dsimp [q]
      exact M.dual.φ.apply_symm_apply y
    rw [hqy] at hdual
    have happ := LinearMap.congr_fun hdual (M.φ x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at happ
    exact happ.symm

@[simp]
lemma doubleDualHom_toLinearMap_apply {C : CosimplicialRing} (M : DescentDatum C) (x : M.M) :
    (doubleDualHom M).toLinearMap x = (Module.evalEquiv C.R₁ M.M) x := rfl

private lemma linearMap_comp_symm_of_comp {R : Type*} [CommSemiring R]
    {M₁ M₂ N₁ N₂ : Type*}
    [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    [AddCommMonoid N₁] [Module R N₁] [AddCommMonoid N₂] [Module R N₂]
    {Φ : M₂ →ₗ[R] N₂} {Ψ : M₁ →ₗ[R] N₁}
    {B : M₁ ≃ₗ[R] M₂} {D : N₁ ≃ₗ[R] N₂}
    (h : Φ ∘ₗ B.toLinearMap = D.toLinearMap ∘ₗ Ψ) :
    Ψ ∘ₗ B.symm.toLinearMap = D.symm.toLinearMap ∘ₗ Φ := by
  ext x
  have hx := LinearMap.congr_fun h (B.symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, B.apply_symm_apply] at hx
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hx, D.symm_apply_apply]

/-- A morphism of descent data whose underlying linear map is an equivalence
induces an isomorphism of descent data. -/
noncomputable def isoOfLinearEquiv {C : CosimplicialRing}
    {M N : DescentDatum C} (f : M ⟶ N) (e : M.M ≃ₗ[C.R₁] N.M)
    (h : f.toLinearMap = e.toLinearMap) : M ≅ N where
  hom := f
  inv :=
    { toLinearMap := e.symm.toLinearMap
      commute_φ := by
        let B := letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
          LinearEquiv.baseChange C.R₁ C.R₂ _ _ e
        let D := letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
          LinearEquiv.baseChange C.R₁ C.R₂ _ _ e
        have hf := f.commute_φ
        rw [h] at hf
        exact linearMap_comp_symm_of_comp (B := B) (D := D) hf }
  hom_inv_id := by
    apply DescentDatum.hom_ext
    change e.symm.toLinearMap ∘ₗ f.toLinearMap = LinearMap.id
    rw [h]
    exact e.symm_comp
  inv_hom_id := by
    apply DescentDatum.hom_ext
    change f.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id
    rw [h]
    exact e.comp_symm

/-- Canonical double-dual reflexivity for a finite-projective descent datum. -/
noncomputable def doubleDualIso {C : CosimplicialRing} (M : DescentDatum C) :=
  isoOfLinearEquiv (doubleDualHom M) (Module.evalEquiv C.R₁ M.M) rfl

open Opposite

/-- Duality as a contravariant functor on abstract descent data. -/
noncomputable def dualFunctor (C : CosimplicialRing) : (DescentDatum C)ᵒᵖ ⥤ DescentDatum C where
  obj M := (unop M).dual
  map {M N} f := DescentDatum.Hom.dual f.unop
  map_id M := by
    apply DescentDatum.hom_ext
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro x
    rfl
  map_comp {X Y Z} f g := by
    apply DescentDatum.hom_ext
    apply LinearMap.ext
    intro h
    apply LinearMap.ext
    intro x
    rfl

end DescentDatum

end Novikov.Descent.Abstract
