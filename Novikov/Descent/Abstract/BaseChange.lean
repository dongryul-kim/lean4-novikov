import Novikov.Descent.Abstract.Descent
import Mathlib.CategoryTheory.Functor.Basic

/-! # Homomorphisms of cosimplicial rings and base change of descent data

A `CosimplicialRingHom C D` is a level-by-level ring homomorphism commuting with
all face maps.  Such a homomorphism lets us base change a descent datum over `C`
to a descent datum over `D` (developed later in this file).

The two main applications are:
* the coefficientwise embedding `realC (∀ i, K i) → prodRealC K`, and
* the projections `prodRealC K → realC (K i)`,

used to reduce descent over a product of fields to descent over each field. -/

namespace Novikov.Descent.Abstract

/-- A homomorphism of (truncated) cosimplicial rings: ring maps on each level
commuting with all five face maps. -/
structure CosimplicialRingHom (C D : CosimplicialRing) where
  /-- Component on the level-one ring. -/
  f₁ : C.R₁ →+* D.R₁
  /-- Component on the level-two ring. -/
  f₂ : C.R₂ →+* D.R₂
  /-- Component on the level-three ring. -/
  f₃ : C.R₃ →+* D.R₃
  comm_π₁ : f₂.comp C.π₁ = D.π₁.comp f₁
  comm_π₂ : f₂.comp C.π₂ = D.π₂.comp f₁
  comm_π₁₂ : f₃.comp C.π₁₂ = D.π₁₂.comp f₂
  comm_π₁₃ : f₃.comp C.π₁₃ = D.π₁₃.comp f₂
  comm_π₂₃ : f₃.comp C.π₂₃ = D.π₂₃.comp f₂

namespace CosimplicialRingHom

variable {C D E : CosimplicialRing}

/-- Two cosimplicial-ring homomorphisms are equal when their three level maps
are equal. -/
@[ext]
lemma ext {F G : CosimplicialRingHom C D}
    (h₁ : F.f₁ = G.f₁) (h₂ : F.f₂ = G.f₂) (h₃ : F.f₃ = G.f₃) : F = G := by
  cases F
  cases G
  cases h₁
  cases h₂
  cases h₃
  rfl

@[simp] lemma map_π₁_apply (F : CosimplicialRingHom C D) (x : C.R₁) :
    F.f₂ (C.π₁ x) = D.π₁ (F.f₁ x) := RingHom.congr_fun F.comm_π₁ x

@[simp] lemma map_π₂_apply (F : CosimplicialRingHom C D) (x : C.R₁) :
    F.f₂ (C.π₂ x) = D.π₂ (F.f₁ x) := RingHom.congr_fun F.comm_π₂ x

@[simp] lemma map_π₁₂_apply (F : CosimplicialRingHom C D) (x : C.R₂) :
    F.f₃ (C.π₁₂ x) = D.π₁₂ (F.f₂ x) := RingHom.congr_fun F.comm_π₁₂ x

@[simp] lemma map_π₁₃_apply (F : CosimplicialRingHom C D) (x : C.R₂) :
    F.f₃ (C.π₁₃ x) = D.π₁₃ (F.f₂ x) := RingHom.congr_fun F.comm_π₁₃ x

@[simp] lemma map_π₂₃_apply (F : CosimplicialRingHom C D) (x : C.R₂) :
    F.f₃ (C.π₂₃ x) = D.π₂₃ (F.f₂ x) := RingHom.congr_fun F.comm_π₂₃ x

/-- The identity cosimplicial ring homomorphism. -/
def id (C : CosimplicialRing) : CosimplicialRingHom C C where
  f₁ := RingHom.id _
  f₂ := RingHom.id _
  f₃ := RingHom.id _
  comm_π₁ := by ext x; rfl
  comm_π₂ := by ext x; rfl
  comm_π₁₂ := by ext x; rfl
  comm_π₁₃ := by ext x; rfl
  comm_π₂₃ := by ext x; rfl

/-- Composition of cosimplicial ring homomorphisms. -/
def comp (G : CosimplicialRingHom D E) (F : CosimplicialRingHom C D) :
    CosimplicialRingHom C E where
  f₁ := G.f₁.comp F.f₁
  f₂ := G.f₂.comp F.f₂
  f₃ := G.f₃.comp F.f₃
  comm_π₁ := by ext x; simp [RingHom.comp_apply]
  comm_π₂ := by ext x; simp [RingHom.comp_apply]
  comm_π₁₂ := by ext x; simp [RingHom.comp_apply]
  comm_π₁₃ := by ext x; simp [RingHom.comp_apply]
  comm_π₂₃ := by ext x; simp [RingHom.comp_apply]

@[simp] lemma comp_f₁ (G : CosimplicialRingHom D E) (F : CosimplicialRingHom C D) :
    (G.comp F).f₁ = G.f₁.comp F.f₁ := rfl
@[simp] lemma comp_f₂ (G : CosimplicialRingHom D E) (F : CosimplicialRingHom C D) :
    (G.comp F).f₂ = G.f₂.comp F.f₂ := rfl
@[simp] lemma comp_f₃ (G : CosimplicialRingHom D E) (F : CosimplicialRingHom C D) :
    (G.comp F).f₃ = G.f₃.comp F.f₃ := rfl

end CosimplicialRingHom

open Novikov.Miscellany TensorProduct

section PullbackMapTmul

variable {R₁ R₂ R₃ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₃]

/-- Pure-tensor formula for `pullbackMap`. -/
lemma pullbackMap_tmul_apply (f₁ f₂ : R₁ →+* R₂) (g : R₂ →+* R₃)
    {h₁ h₂ : R₁ →+* R₃} (hh₁ : g.comp f₁ = h₁) (hh₂ : g.comp f₂ = h₂)
    (M₁ : Type*) [AddCommGroup M₁] [Module R₁ M₁]
    (M₂ : Type*) [AddCommGroup M₂] [Module R₁ M₂]
    (φ : baseChange_along f₁ M₁ ≃ₗ[R₂] baseChange_along f₂ M₂)
    (r : R₃) (m : M₁) :
    pullbackMap f₁ f₂ g hh₁ hh₂ M₁ M₂ φ
      (letI : Algebra R₁ R₃ := h₁.toAlgebra; r ⊗ₜ[R₁] m) =
      (letI : Algebra R₁ R₂ := f₂.toAlgebra
       letI : Algebra R₂ R₃ := g.toAlgebra
       letI : Algebra R₁ R₃ := h₂.toAlgebra
       (baseChange_assoc_eq f₂ g hh₂ M₂)
        (r ⊗ₜ[R₂] (φ ((letI : Algebra R₁ R₂ := f₁.toAlgebra;
          (1 : R₂) ⊗ₜ[R₁] m))))) := by
  subst hh₁
  subst hh₂
  change pullbackMap f₁ f₂ g rfl rfl M₁ M₂ φ
      (letI : Algebra R₁ R₃ := (g.comp f₁).toAlgebra; r ⊗ₜ[R₁] m) =
    (letI : Algebra R₁ R₂ := f₂.toAlgebra
     letI : Algebra R₂ R₃ := g.toAlgebra
     letI : Algebra R₁ R₃ := (g.comp f₂).toAlgebra
     (baseChange_assoc f₂ g M₂)
      (r ⊗ₜ[R₂] (φ ((letI : Algebra R₁ R₂ := f₁.toAlgebra;
        (1 : R₂) ⊗ₜ[R₁] m)))))
  simp [pullbackMap]

end PullbackMapTmul

/-! ### Pure-tensor formulas for the level-3 pullbacks

These restate `pullbackMap_tmul_apply` for the concrete `pullbackMap_12/13/23`,
presenting the source with the `ρ₁`/`ρ₂` algebra instance (rather than the raw
composite) so that `rw` can match against `ρ₁s`/`ρ₂s` elements.  Each is a
definitional consequence of `pullbackMap_tmul_apply`. -/

section PullbackMapLevel3Tmul

variable {E : CosimplicialRing}

/-- Pure-tensor formula for `pullbackMap_12`. -/
lemma pullbackMap_12_tmul (M : Type*) [AddCommGroup M] [Module E.R₁ M]
    (φ : π₁s E M ≃ₗ[E.R₂] π₂s E M) (r : E.R₃) (m : M) :
    pullbackMap_12 E M φ
      (letI : Algebra E.R₁ E.R₃ := E.ρ₁.toAlgebra; r ⊗ₜ[E.R₁] m) =
    (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
     letI : Algebra E.R₂ E.R₃ := E.π₁₂.toAlgebra
     letI : Algebra E.R₁ E.R₃ := E.ρ₂.toAlgebra
     (baseChange_assoc_eq E.π₂ E.π₁₂ E.ρ₂_eq_π₁₂_π₂.symm M)
      (r ⊗ₜ[E.R₂] (φ (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra; (1 : E.R₂) ⊗ₜ[E.R₁] m)))) :=
  pullbackMap_tmul_apply E.π₁ E.π₂ E.π₁₂ E.ρ₁_eq_π₁₂_π₁.symm E.ρ₂_eq_π₁₂_π₂.symm M M φ r m

/-- Pure-tensor formula for `pullbackMap_13`. -/
lemma pullbackMap_13_tmul (M : Type*) [AddCommGroup M] [Module E.R₁ M]
    (φ : π₁s E M ≃ₗ[E.R₂] π₂s E M) (r : E.R₃) (m : M) :
    pullbackMap_13 E M φ
      (letI : Algebra E.R₁ E.R₃ := E.ρ₁.toAlgebra; r ⊗ₜ[E.R₁] m) =
    (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
     letI : Algebra E.R₂ E.R₃ := E.π₁₃.toAlgebra
     letI : Algebra E.R₁ E.R₃ := E.ρ₃.toAlgebra
     (baseChange_assoc_eq E.π₂ E.π₁₃ E.ρ₃_eq_π₁₃_π₂.symm M)
      (r ⊗ₜ[E.R₂] (φ (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra; (1 : E.R₂) ⊗ₜ[E.R₁] m)))) :=
  pullbackMap_tmul_apply E.π₁ E.π₂ E.π₁₃ E.ρ₁_eq_π₁₃_π₁.symm E.ρ₃_eq_π₁₃_π₂.symm M M φ r m

/-- Pure-tensor formula for `pullbackMap_23`. -/
lemma pullbackMap_23_tmul (M : Type*) [AddCommGroup M] [Module E.R₁ M]
    (φ : π₁s E M ≃ₗ[E.R₂] π₂s E M) (r : E.R₃) (m : M) :
    pullbackMap_23 E M φ
      (letI : Algebra E.R₁ E.R₃ := E.ρ₂.toAlgebra; r ⊗ₜ[E.R₁] m) =
    (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
     letI : Algebra E.R₂ E.R₃ := E.π₂₃.toAlgebra
     letI : Algebra E.R₁ E.R₃ := E.ρ₃.toAlgebra
     (baseChange_assoc_eq E.π₂ E.π₂₃ E.ρ₃_eq_π₂₃_π₂.symm M)
      (r ⊗ₜ[E.R₂] (φ (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra; (1 : E.R₂) ⊗ₜ[E.R₁] m)))) :=
  pullbackMap_tmul_apply E.π₁ E.π₂ E.π₂₃ rfl rfl M M φ r m

end PullbackMapLevel3Tmul

namespace CosimplicialRingHom

variable {C D : CosimplicialRing} (F : CosimplicialRingHom C D)

lemma comm_ρ₁ : D.ρ₁.comp F.f₁ = F.f₃.comp C.ρ₁ := by
  ext x
  simp [CosimplicialRing.ρ₁, RingHom.comp_apply]

lemma comm_ρ₂ : D.ρ₂.comp F.f₁ = F.f₃.comp C.ρ₂ := by
  ext x
  simp [CosimplicialRing.ρ₂, RingHom.comp_apply]

lemma comm_ρ₃ : D.ρ₃.comp F.f₁ = F.f₃.comp C.ρ₃ := by
  ext x
  simp [CosimplicialRing.ρ₃, RingHom.comp_apply]

/-- Compare pulling back the base-changed module along `D.π₁` with first
pulling back along `C.π₁` and then extending scalars along `F.f₂`. -/
noncomputable def pullbackBaseChangeπ₁
    (M : Type*) [AddCommGroup M] [Module C.R₁ M] :
    baseChange_along D.π₁ (baseChange_along F.f₁ M) ≃ₗ[D.R₂]
      letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
      D.R₂ ⊗[C.R₂] (π₁s C M) :=
  baseChangeSquare F.f₁ C.π₁ D.π₁ F.f₂ F.comm_π₁.symm M

/-- Compare pulling back the base-changed module along `D.π₂` with first
pulling back along `C.π₂` and then extending scalars along `F.f₂`. -/
noncomputable def pullbackBaseChangeπ₂
    (M : Type*) [AddCommGroup M] [Module C.R₁ M] :
    baseChange_along D.π₂ (baseChange_along F.f₁ M) ≃ₗ[D.R₂]
      letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
      D.R₂ ⊗[C.R₂] (π₂s C M) :=
  baseChangeSquare F.f₁ C.π₂ D.π₂ F.f₂ F.comm_π₂.symm M

/-- Compare pulling back the base-changed module along `D.ρ₁` with first
pulling back along `C.ρ₁` and then extending scalars along `F.f₃`. -/
noncomputable def pullbackBaseChangeρ₁
    (M : Type*) [AddCommGroup M] [Module C.R₁ M] :
    baseChange_along D.ρ₁ (baseChange_along F.f₁ M) ≃ₗ[D.R₃]
      letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
      D.R₃ ⊗[C.R₃] (ρ₁s C M) :=
  baseChangeSquare F.f₁ C.ρ₁ D.ρ₁ F.f₃ F.comm_ρ₁ M

/-- Compare pulling back the base-changed module along `D.ρ₂` with first
pulling back along `C.ρ₂` and then extending scalars along `F.f₃`. -/
noncomputable def pullbackBaseChangeρ₂
    (M : Type*) [AddCommGroup M] [Module C.R₁ M] :
    baseChange_along D.ρ₂ (baseChange_along F.f₁ M) ≃ₗ[D.R₃]
      letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
      D.R₃ ⊗[C.R₃] (ρ₂s C M) :=
  baseChangeSquare F.f₁ C.ρ₂ D.ρ₂ F.f₃ F.comm_ρ₂ M

/-- Compare pulling back the base-changed module along `D.ρ₃` with first
pulling back along `C.ρ₃` and then extending scalars along `F.f₃`. -/
noncomputable def pullbackBaseChangeρ₃
    (M : Type*) [AddCommGroup M] [Module C.R₁ M] :
    baseChange_along D.ρ₃ (baseChange_along F.f₁ M) ≃ₗ[D.R₃]
      letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
      D.R₃ ⊗[C.R₃] (ρ₃s C M) :=
  baseChangeSquare F.f₁ C.ρ₃ D.ρ₃ F.f₃ F.comm_ρ₃ M

/-- The descent isomorphism obtained by base-changing a descent datum along a
homomorphism of cosimplicial rings. -/
noncomputable def baseChangePhi (M : DescentDatum C) :
    π₁s D (baseChange_along F.f₁ M.M) ≃ₗ[D.R₂]
      π₂s D (baseChange_along F.f₁ M.M) := by
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  exact (F.pullbackBaseChangeπ₁ M.M).trans
    ((LinearEquiv.baseChange C.R₂ D.R₂ (π₁s C M.M) (π₂s C M.M) M.φ).trans
      (F.pullbackBaseChangeπ₂ M.M).symm)

@[simp]
lemma pullbackBaseChangeπ₁_tmul
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : D.R₂) (s : D.R₁) (m : M) :
    F.pullbackBaseChangeπ₁ M
      ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
        letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
        r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] m))) =
      (letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
       letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
       letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
       (s • r) ⊗ₜ[C.R₂] ((1 : C.R₂) ⊗ₜ[C.R₁] m)) := by
  simp [pullbackBaseChangeπ₁]

@[simp]
lemma pullbackBaseChangeπ₂_tmul
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : D.R₂) (s : D.R₁) (m : M) :
    F.pullbackBaseChangeπ₂ M
      ((letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
        letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
        r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] m))) =
      (letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
       letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
       letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
       (s • r) ⊗ₜ[C.R₂] ((1 : C.R₂) ⊗ₜ[C.R₁] m)) := by
  simp [pullbackBaseChangeπ₂]

/-- Pure-tensor formula for the base-changed descent isomorphism. -/
lemma baseChangePhi_tmul (M : DescentDatum C)
    (r : D.R₂) (s : D.R₁) (m : M.M) :
    F.baseChangePhi M
      ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
        letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
        r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] m))) =
      (F.pullbackBaseChangeπ₂ M.M).symm
        ((letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
          letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
          (s • r) ⊗ₜ[C.R₂]
            (M.φ ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra;
              (1 : C.R₂) ⊗ₜ[C.R₁] m))))) := by
  simp only [baseChangePhi, LinearEquiv.trans_apply]
  rw [pullbackBaseChangeπ₁_tmul, LinearEquiv.baseChange_tmul]

/-- Pure-tensor formula for the inverse of the base-changed descent
isomorphism. -/
lemma baseChangePhi_symm_tmul (M : DescentDatum C)
    (r : D.R₂) (s : D.R₁) (m : M.M) :
    (F.baseChangePhi M).symm
      ((letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
        letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
        r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] m))) =
      (F.pullbackBaseChangeπ₁ M.M).symm
        ((letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
          letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
          (s • r) ⊗ₜ[C.R₂]
            (M.φ.symm ((letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra;
              (1 : C.R₂) ⊗ₜ[C.R₁] m))))) := by
  dsimp [baseChangePhi]
  rw [pullbackBaseChangeπ₂_tmul]
  rw [LinearEquiv.baseChange_symm_tmul]

/-- Compare pulling back the base-changed module along `D.π₁` directly with
extension of scalars along the composite `D.π₁.comp F.f₁`. -/
noncomputable def pullbackBaseChangeπ₁Assoc
    (M : Type*) [AddCommGroup M] [Module C.R₁ M] :
    baseChange_along D.π₁ (baseChange_along F.f₁ M) ≃ₗ[D.R₂]
      baseChange_along (D.π₁.comp F.f₁) M :=
  (F.pullbackBaseChangeπ₁ M).trans
    (baseChange_assoc_eq C.π₁ F.f₂ F.comm_π₁ M)

/-- Compare pulling back the base-changed module along `D.π₂` directly with
extension of scalars along the composite `D.π₂.comp F.f₁`. -/
noncomputable def pullbackBaseChangeπ₂Assoc
    (M : Type*) [AddCommGroup M] [Module C.R₁ M] :
    baseChange_along D.π₂ (baseChange_along F.f₁ M) ≃ₗ[D.R₂]
      baseChange_along (D.π₂.comp F.f₁) M :=
  (F.pullbackBaseChangeπ₂ M).trans
    (baseChange_assoc_eq C.π₂ F.f₂ F.comm_π₂ M)

@[simp]
lemma pullbackBaseChangeπ₁Assoc_tmul
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : D.R₂) (s : D.R₁) (m : M) :
    F.pullbackBaseChangeπ₁Assoc M
      ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
        letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
        r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] m))) =
      (letI : Algebra C.R₁ D.R₂ := (D.π₁.comp F.f₁).toAlgebra
       (letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra; s • r) ⊗ₜ[C.R₁] m) := by
  rw [pullbackBaseChangeπ₁Assoc]
  simp only [LinearEquiv.trans_apply]
  rw [pullbackBaseChangeπ₁_tmul]
  rw [baseChange_assoc_eq_tmul C.π₁ F.f₂ F.comm_π₁ M
    ((letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra; s • r)) (1 : C.R₂) m]
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  rw [one_smul]

@[simp]
lemma pullbackBaseChangeπ₂Assoc_tmul
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : D.R₂) (s : D.R₁) (m : M) :
    F.pullbackBaseChangeπ₂Assoc M
      ((letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
        letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
        r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] m))) =
      (letI : Algebra C.R₁ D.R₂ := (D.π₂.comp F.f₁).toAlgebra
       (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra; s • r) ⊗ₜ[C.R₁] m) := by
  rw [pullbackBaseChangeπ₂Assoc]
  simp only [LinearEquiv.trans_apply]
  rw [pullbackBaseChangeπ₂_tmul]
  rw [baseChange_assoc_eq_tmul C.π₂ F.f₂ F.comm_π₂ M
    ((letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra; s • r)) (1 : C.R₂) m]
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  rw [one_smul]

/-- The descent isomorphism on `M.baseChange F`, transported along the two
associativity identifications above, is the pullback of the descent isomorphism
of `M` along `F.f₂`. -/
lemma baseChangePhi_assoc (M : DescentDatum C) :
    (F.pullbackBaseChangeπ₂Assoc M.M).toLinearMap ∘ₗ
      (F.baseChangePhi M).toLinearMap =
    (pullbackMap C.π₁ C.π₂ F.f₂ F.comm_π₁ F.comm_π₂ M.M M.M M.φ).toLinearMap ∘ₗ
      (F.pullbackBaseChangeπ₁Assoc M.M).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add]
      simpa only [LinearMap.comp_apply] using congrArg₂ HAdd.hAdd hx hy
  | tmul r y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
          letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
          rw [TensorProduct.tmul_add]
          simp only [map_add]
          simpa only [LinearMap.comp_apply] using congrArg₂ HAdd.hAdd hy hz
      | tmul s m =>
          letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
          rw [CosimplicialRingHom.baseChangePhi_tmul]
          rw [pullbackBaseChangeπ₁Assoc, pullbackBaseChangeπ₂Assoc]
          simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
          rw [pullbackBaseChangeπ₁_tmul]
          rw [baseChange_assoc_eq_tmul C.π₁ F.f₂ F.comm_π₁ M.M (s • r) (1 : C.R₂) m]
          rw [pullbackMap_tmul_apply]
          simp [Algebra.smul_def]

/-- Inverse form of `baseChangePhi_assoc`: after the same associativity
identifications, the inverse of the base-changed descent isomorphism is the
inverse pullback of the original descent isomorphism. -/
lemma baseChangePhi_assoc_symm (M : DescentDatum C) :
    (F.pullbackBaseChangeπ₁Assoc M.M).toLinearMap ∘ₗ
      (F.baseChangePhi M).symm.toLinearMap =
    (pullbackMap C.π₁ C.π₂ F.f₂ F.comm_π₁ F.comm_π₂ M.M M.M M.φ).symm.toLinearMap ∘ₗ
      (F.pullbackBaseChangeπ₂Assoc M.M).toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  let A := F.pullbackBaseChangeπ₁Assoc M.M
  let B := F.pullbackBaseChangeπ₂Assoc M.M
  let P := pullbackMap C.π₁ C.π₂ F.f₂ F.comm_π₁ F.comm_π₂ M.M M.M M.φ
  have h := LinearMap.congr_fun (F.baseChangePhi_assoc M) ((F.baseChangePhi M).symm x)
  change B (F.baseChangePhi M ((F.baseChangePhi M).symm x)) =
    P (A ((F.baseChangePhi M).symm x)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  have h' := congrArg P.symm h
  simpa only [LinearEquiv.symm_apply_apply] using h'.symm

@[simp]
lemma pullbackBaseChangeπ₁_symm_tmul
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : D.R₂) (m : M) :
    (F.pullbackBaseChangeπ₁ M).symm
      ((letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
        letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
        r ⊗ₜ[C.R₂] ((1 : C.R₂) ⊗ₜ[C.R₁] m))) =
      (letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
       letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
       r ⊗ₜ[D.R₁] ((1 : D.R₁) ⊗ₜ[C.R₁] m)) := by
  rw [pullbackBaseChangeπ₁, baseChangeSquare_symm_tmul]
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  rw [one_smul]

@[simp]
lemma pullbackBaseChangeπ₂_symm_tmul
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : D.R₂) (m : M) :
    (F.pullbackBaseChangeπ₂ M).symm
      ((letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
        letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
        r ⊗ₜ[C.R₂] ((1 : C.R₂) ⊗ₜ[C.R₁] m))) =
      (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
       letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
       r ⊗ₜ[D.R₁] ((1 : D.R₁) ⊗ₜ[C.R₁] m)) := by
  rw [pullbackBaseChangeπ₂, baseChangeSquare_symm_tmul]
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  rw [one_smul]

@[simp]
lemma pullbackBaseChangeπ₁Assoc_symm_tmul
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : D.R₂) (m : M) :
    (F.pullbackBaseChangeπ₁Assoc M).symm
      ((letI : Algebra C.R₁ D.R₂ := (D.π₁.comp F.f₁).toAlgebra
        r ⊗ₜ[C.R₁] m)) =
      (letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
       letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
       r ⊗ₜ[D.R₁] ((1 : D.R₁) ⊗ₜ[C.R₁] m)) := by
  rw [pullbackBaseChangeπ₁Assoc]
  simp only [LinearEquiv.symm_trans_apply]
  rw [baseChange_assoc_eq_symm_tmul C.π₁ F.f₂ F.comm_π₁ M r m]
  rw [pullbackBaseChangeπ₁_symm_tmul]

@[simp]
lemma pullbackBaseChangeπ₂Assoc_symm_tmul
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : D.R₂) (m : M) :
    (F.pullbackBaseChangeπ₂Assoc M).symm
      ((letI : Algebra C.R₁ D.R₂ := (D.π₂.comp F.f₁).toAlgebra
        r ⊗ₜ[C.R₁] m)) =
      (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
       letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
       r ⊗ₜ[D.R₁] ((1 : D.R₁) ⊗ₜ[C.R₁] m)) := by
  rw [pullbackBaseChangeπ₂Assoc]
  simp only [LinearEquiv.symm_trans_apply]
  rw [baseChange_assoc_eq_symm_tmul C.π₂ F.f₂ F.comm_π₂ M r m]
  rw [pullbackBaseChangeπ₂_symm_tmul]

@[simp]
lemma pullbackBaseChangeρ₁_tmul
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : D.R₃) (s : D.R₁) (m : M) :
    F.pullbackBaseChangeρ₁ M
      ((letI : Algebra D.R₁ D.R₃ := D.ρ₁.toAlgebra
        letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
        r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] m))) =
      (letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
       letI : Algebra C.R₁ C.R₃ := C.ρ₁.toAlgebra
       letI : Algebra D.R₁ D.R₃ := D.ρ₁.toAlgebra
       (s • r) ⊗ₜ[C.R₃] ((1 : C.R₃) ⊗ₜ[C.R₁] m)) := by
  simp [pullbackBaseChangeρ₁]

@[simp]
lemma pullbackBaseChangeρ₂_tmul
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : D.R₃) (s : D.R₁) (m : M) :
    F.pullbackBaseChangeρ₂ M
      ((letI : Algebra D.R₁ D.R₃ := D.ρ₂.toAlgebra
        letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
        r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] m))) =
      (letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
       letI : Algebra C.R₁ C.R₃ := C.ρ₂.toAlgebra
       letI : Algebra D.R₁ D.R₃ := D.ρ₂.toAlgebra
       (s • r) ⊗ₜ[C.R₃] ((1 : C.R₃) ⊗ₜ[C.R₁] m)) := by
  simp [pullbackBaseChangeρ₂]

@[simp]
lemma pullbackBaseChangeρ₃_tmul
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : D.R₃) (s : D.R₁) (m : M) :
    F.pullbackBaseChangeρ₃ M
      ((letI : Algebra D.R₁ D.R₃ := D.ρ₃.toAlgebra
        letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
        r ⊗ₜ[D.R₁] (s ⊗ₜ[C.R₁] m))) =
      (letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
       letI : Algebra C.R₁ C.R₃ := C.ρ₃.toAlgebra
       letI : Algebra D.R₁ D.R₃ := D.ρ₃.toAlgebra
       (s • r) ⊗ₜ[C.R₃] ((1 : C.R₃) ⊗ₜ[C.R₁] m)) := by
  simp [pullbackBaseChangeρ₃]

/-- Inverse-pullback formula for `pullbackBaseChangeπ₂` on a tensor whose inner
factor is `c ⊗ₜ m` (not necessarily `1 ⊗ₜ m`); used in the cocycle calculation. -/
lemma pullbackBaseChangeπ₂_symm_tmul'
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : D.R₂) (c : C.R₂) (m : M) :
    (F.pullbackBaseChangeπ₂ M).symm
      ((letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
        letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
        r ⊗ₜ[C.R₂] (c ⊗ₜ[C.R₁] m))) =
      (letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
       letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
       letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
       (c • r) ⊗ₜ[D.R₁] ((1 : D.R₁) ⊗ₜ[C.R₁] m)) := by
  simp [pullbackBaseChangeπ₂]

/-- Coherence between the level-3 pullback `pullbackMap_12` of the base-changed
descent isomorphism and the base change of `pullbackMap_12` of the original one. -/
lemma pullbackMap_12_baseChangePhi (M : DescentDatum C) :
    (F.pullbackBaseChangeρ₂ M.M).toLinearMap ∘ₗ
      (pullbackMap_12 D (baseChange_along F.f₁ M.M) (F.baseChangePhi M)).toLinearMap =
    (letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
     LinearEquiv.baseChange C.R₃ D.R₃ (ρ₁s C M.M) (ρ₂s C M.M)
       (pullbackMap_12 C M.M M.φ)).toLinearMap ∘ₗ
      (F.pullbackBaseChangeρ₁ M.M).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.comp_apply] at ha hb ⊢; rw [ha, hb]
  | tmul r y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      simp only [tmul_add, map_add, LinearMap.comp_apply] at ha hb ⊢; rw [ha, hb]
    | tmul s m =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [pullbackMap_12_tmul, baseChangePhi_tmul, pullbackBaseChangeρ₁_tmul,
          LinearEquiv.baseChange_tmul, pullbackMap_12_tmul]
      generalize M.φ (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] m) = y
      induction y using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero]
      | add a b ha hb => simp only [tmul_add, map_add]; rw [ha, hb]
      | tmul c m' =>
        letI : Algebra C.R₂ C.R₃ := C.π₁₂.toAlgebra
        letI : Algebra C.R₁ C.R₃ := C.ρ₂.toAlgebra
        letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
        rw [pullbackBaseChangeπ₂_symm_tmul', baseChange_assoc_eq_tmul,
            pullbackBaseChangeρ₂_tmul]
        simp only [baseChange_assoc_eq_tmul, Algebra.smul_def, map_one, mul_one, one_mul]
        rw [tmul_eq_smul_one_tmul ((algebraMap C.R₂ C.R₃) c) m', tmul_smul, smul_tmul']
        congr 1
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, map_π₁₂_apply,
          RingHom.comp_apply, CosimplicialRing.ρ₁]
        ring

/-- Coherence between the level-3 pullback `pullbackMap_23` of the base-changed
descent isomorphism and the base change of `pullbackMap_23` of the original one. -/
lemma pullbackMap_23_baseChangePhi (M : DescentDatum C) :
    (F.pullbackBaseChangeρ₃ M.M).toLinearMap ∘ₗ
      (pullbackMap_23 D (baseChange_along F.f₁ M.M) (F.baseChangePhi M)).toLinearMap =
    (letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
     LinearEquiv.baseChange C.R₃ D.R₃ (ρ₂s C M.M) (ρ₃s C M.M)
       (pullbackMap_23 C M.M M.φ)).toLinearMap ∘ₗ
      (F.pullbackBaseChangeρ₂ M.M).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.comp_apply] at ha hb ⊢; rw [ha, hb]
  | tmul r y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      simp only [tmul_add, map_add, LinearMap.comp_apply] at ha hb ⊢; rw [ha, hb]
    | tmul s m =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [pullbackMap_23_tmul, baseChangePhi_tmul, pullbackBaseChangeρ₂_tmul,
          LinearEquiv.baseChange_tmul, pullbackMap_23_tmul]
      generalize M.φ (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] m) = y
      induction y using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero]
      | add a b ha hb => simp only [tmul_add, map_add]; rw [ha, hb]
      | tmul c m' =>
        letI : Algebra C.R₂ C.R₃ := C.π₂₃.toAlgebra
        letI : Algebra C.R₁ C.R₃ := C.ρ₃.toAlgebra
        letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
        rw [pullbackBaseChangeπ₂_symm_tmul', baseChange_assoc_eq_tmul,
            pullbackBaseChangeρ₃_tmul]
        simp only [baseChange_assoc_eq_tmul, Algebra.smul_def, map_one, mul_one, one_mul]
        rw [tmul_eq_smul_one_tmul ((algebraMap C.R₂ C.R₃) c) m', tmul_smul, smul_tmul']
        congr 1
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, map_π₂₃_apply,
          RingHom.comp_apply, CosimplicialRing.ρ₂]
        ring

/-- Coherence between the level-3 pullback `pullbackMap_13` of the base-changed
descent isomorphism and the base change of `pullbackMap_13` of the original one. -/
lemma pullbackMap_13_baseChangePhi (M : DescentDatum C) :
    (F.pullbackBaseChangeρ₃ M.M).toLinearMap ∘ₗ
      (pullbackMap_13 D (baseChange_along F.f₁ M.M) (F.baseChangePhi M)).toLinearMap =
    (letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
     LinearEquiv.baseChange C.R₃ D.R₃ (ρ₁s C M.M) (ρ₃s C M.M)
       (pullbackMap_13 C M.M M.φ)).toLinearMap ∘ₗ
      (F.pullbackBaseChangeρ₁ M.M).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.comp_apply] at ha hb ⊢; rw [ha, hb]
  | tmul r y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      simp only [tmul_add, map_add, LinearMap.comp_apply] at ha hb ⊢; rw [ha, hb]
    | tmul s m =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [pullbackMap_13_tmul, baseChangePhi_tmul, pullbackBaseChangeρ₁_tmul,
          LinearEquiv.baseChange_tmul, pullbackMap_13_tmul]
      generalize M.φ (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] m) = y
      induction y using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero]
      | add a b ha hb => simp only [tmul_add, map_add]; rw [ha, hb]
      | tmul c m' =>
        letI : Algebra C.R₂ C.R₃ := C.π₁₃.toAlgebra
        letI : Algebra C.R₁ C.R₃ := C.ρ₃.toAlgebra
        letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
        rw [pullbackBaseChangeπ₂_symm_tmul', baseChange_assoc_eq_tmul,
            pullbackBaseChangeρ₃_tmul]
        simp only [baseChange_assoc_eq_tmul, Algebra.smul_def, map_one, mul_one, one_mul]
        rw [tmul_eq_smul_one_tmul ((algebraMap C.R₂ C.R₃) c) m', tmul_smul, smul_tmul']
        congr 1
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, map_π₁₃_apply,
          RingHom.comp_apply, CosimplicialRing.ρ₁]
        rw [show D.π₁₃ (D.π₁ s) = D.π₁₂ (D.π₁ s) from RingHom.congr_fun D.π₁₃_π₁_eq_π₁₂_π₁ s]
        ring

/-- Naturality of the comparison equivalence `pullbackBaseChangeπ₁` with respect to
base change of a morphism of descent data. -/
lemma pbπ₁_naturality {M N : DescentDatum C} (f : M ⟶ N) :
    (F.pullbackBaseChangeπ₁ N.M).toLinearMap ∘ₗ
        baseChangeMap D.π₁ (baseChangeMap F.f₁ f.toLinearMap) =
      baseChangeMap F.f₂ (baseChangeMap C.π₁ f.toLinearMap) ∘ₗ
        (F.pullbackBaseChangeπ₁ M.M).toLinearMap :=
  baseChangeSquare_naturality F.f₁ C.π₁ D.π₁ F.f₂ F.comm_π₁.symm f.toLinearMap

/-- Naturality of the comparison equivalence `pullbackBaseChangeπ₂` with respect to
base change of a morphism of descent data. -/
lemma pbπ₂_naturality {M N : DescentDatum C} (f : M ⟶ N) :
    (F.pullbackBaseChangeπ₂ N.M).toLinearMap ∘ₗ
        baseChangeMap D.π₂ (baseChangeMap F.f₁ f.toLinearMap) =
      baseChangeMap F.f₂ (baseChangeMap C.π₂ f.toLinearMap) ∘ₗ
        (F.pullbackBaseChangeπ₂ M.M).toLinearMap :=
  baseChangeSquare_naturality F.f₁ C.π₂ D.π₂ F.f₂ F.comm_π₂.symm f.toLinearMap

/-- Naturality of the base-changed descent isomorphism `baseChangePhi` with respect
to base change of a morphism of descent data.  This is `commute_φ` for the
base-changed morphism (the three squares: `pbπ₁`, `f.commute_φ` base-changed, `pbπ₂`). -/
lemma baseChangePhi_naturality {M N : DescentDatum C} (f : M ⟶ N) :
    (F.baseChangePhi N).toLinearMap ∘ₗ
        baseChangeMap D.π₁ (baseChangeMap F.f₁ f.toLinearMap) =
      baseChangeMap D.π₂ (baseChangeMap F.f₁ f.toLinearMap) ∘ₗ
        (F.baseChangePhi M).toLinearMap := by
  letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
  have hbsq : (LinearEquiv.baseChange C.R₂ D.R₂ (π₁s C N.M) (π₂s C N.M) N.φ).toLinearMap ∘ₗ
        baseChangeMap F.f₂ (baseChangeMap C.π₁ f.toLinearMap) =
      baseChangeMap F.f₂ (baseChangeMap C.π₂ f.toLinearMap) ∘ₗ
        (LinearEquiv.baseChange C.R₂ D.R₂ (π₁s C M.M) (π₂s C M.M) M.φ).toLinearMap := by
    rw [LinearEquiv.coe_baseChange, LinearEquiv.coe_baseChange]
    simp only [baseChangeMap]
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, f.commute_φ]
  have hp2sq : (F.pullbackBaseChangeπ₂ N.M).symm.toLinearMap ∘ₗ
        baseChangeMap F.f₂ (baseChangeMap C.π₂ f.toLinearMap) =
      baseChangeMap D.π₂ (baseChangeMap F.f₁ f.toLinearMap) ∘ₗ
        (F.pullbackBaseChangeπ₂ M.M).symm.toLinearMap := by
    apply LinearMap.ext; intro y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    have h := LinearMap.congr_fun (F.pbπ₂_naturality f)
      ((F.pullbackBaseChangeπ₂ M.M).symm y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  apply LinearMap.ext; intro x
  have hp1 := LinearMap.congr_fun (F.pbπ₁_naturality f) x
  have hb := LinearMap.congr_fun hbsq ((F.pullbackBaseChangeπ₁ M.M) x)
  have hp2 := LinearMap.congr_fun hp2sq
    ((LinearEquiv.baseChange C.R₂ D.R₂ (π₁s C M.M) (π₂s C M.M) M.φ)
      ((F.pullbackBaseChangeπ₁ M.M) x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hp1 hb hp2 ⊢
  simp only [baseChangePhi, LinearEquiv.trans_apply]
  rw [hp1, hb, hp2]

end CosimplicialRingHom

/-- Base change of a descent datum along a homomorphism of cosimplicial rings.
The underlying module is `D.R₁ ⊗[C.R₁] M.M` and the descent isomorphism is
`baseChangePhi`; the cocycle condition is transported from `M`'s via the three
`pullbackMap_*_baseChangePhi` coherences and `LinearEquiv.baseChange_trans`. -/
noncomputable def DescentDatum.baseChange
    {C D : CosimplicialRing} (F : CosimplicialRingHom C D)
    (M : DescentDatum C) : DescentDatum D := by
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  haveI : Module.Finite D.R₁ (baseChange_along F.f₁ M.M) :=
    Module.Finite.base_change C.R₁ D.R₁ M.M
  haveI : Module.Projective D.R₁ (baseChange_along F.f₁ M.M) :=
    Novikov.Miscellany.baseChange_projective M.M
  refine
    { M := baseChange_along F.f₁ M.M
      φ := F.baseChangePhi M
      cocycle := ?_ }
  letI : Algebra C.R₃ D.R₃ := F.f₃.toAlgebra
  funext z
  simp only [Function.comp_apply, LinearEquiv.coe_coe]
  apply (F.pullbackBaseChangeρ₃ M.M).injective
  have e23 := LinearMap.congr_fun (F.pullbackMap_23_baseChangePhi M)
    (pullbackMap_12 D (baseChange_along F.f₁ M.M) (F.baseChangePhi M) z)
  have e12 := LinearMap.congr_fun (F.pullbackMap_12_baseChangePhi M) z
  have e13 := LinearMap.congr_fun (F.pullbackMap_13_baseChangePhi M) z
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at e23 e12 e13 ⊢
  rw [e23, e12, e13]
  generalize (F.pullbackBaseChangeρ₁ M.M) z = w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul d v =>
    simp only [LinearEquiv.baseChange_tmul]
    congr 1
    exact congrFun M.cocycle v

/-- Base change of a morphism of descent data along a homomorphism of cosimplicial
rings.  The underlying linear map is `LinearMap.baseChange D.R₁ f.toLinearMap`; the
`commute_φ` condition is `baseChangePhi_naturality`. -/
noncomputable def DescentDatum.Hom.baseChange
    {C D : CosimplicialRing} (F : CosimplicialRingHom C D)
    {M N : DescentDatum C} (f : M ⟶ N) :
    M.baseChange F ⟶ N.baseChange F := by
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  refine { toLinearMap := LinearMap.baseChange D.R₁ f.toLinearMap, commute_φ := ?_ }
  exact F.baseChangePhi_naturality f

open CategoryTheory in
/-- Base change of descent data along a homomorphism of cosimplicial rings, as a
functor `DescentDatum C ⥤ DescentDatum D`. -/
noncomputable def baseChangeFunctor {C D : CosimplicialRing} (F : CosimplicialRingHom C D) :
    DescentDatum C ⥤ DescentDatum D where
  obj M := M.baseChange F
  map f := DescentDatum.Hom.baseChange F f
  map_id M := by
    apply DescentDatum.hom_ext
    letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
    change LinearMap.baseChange D.R₁ (LinearMap.id) = LinearMap.id
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply DescentDatum.hom_ext
    letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
    change LinearMap.baseChange D.R₁ (g.toLinearMap ∘ₗ f.toLinearMap) =
      LinearMap.baseChange D.R₁ g.toLinearMap ∘ₗ LinearMap.baseChange D.R₁ f.toLinearMap
    exact LinearMap.baseChange_comp _ _

/-! ### Composition of base change -/

section BaseChangeComp

open CategoryTheory

universe u

variable {C D E : CosimplicialRing.{u, u, u}}

private lemma pullbackBaseChangeπ₂_comp
    (F : CosimplicialRingHom C D) (G : CosimplicialRingHom D E)
    (M : DescentDatum.{u, u, u, u} C)
    (r : E.R₂) (s : E.R₁) (t : D.R₁) (y : π₂s C M.M) :
    let H := G.comp F
    let e := baseChange_assoc F.f₁ G.f₁ M.M
    let aD : D.R₂ := D.π₁ t
    let aE : E.R₂ := E.π₁ s * r
    let rH : E.R₂ := E.π₁ (G.f₁ t * s) * r
    H.pullbackBaseChangeπ₂ M.M |>.symm
        (letI : Algebra C.R₂ E.R₂ := H.f₂.toAlgebra
         rH ⊗ₜ[C.R₂] y) =
      (baseChangeMap E.π₂ e.toLinearMap)
        (G.pullbackBaseChangeπ₂ (M.baseChange F).M |>.symm
          (letI : Algebra D.R₂ E.R₂ := G.f₂.toAlgebra
           aE ⊗ₜ[D.R₂]
            (F.pullbackBaseChangeπ₂ M.M |>.symm
              (letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
               aD ⊗ₜ[C.R₂] y)))) := by
  dsimp only
  let H := G.comp F
  let e := baseChange_assoc F.f₁ G.f₁ M.M
  let aD : D.R₂ := D.π₁ t
  let aE : E.R₂ := E.π₁ s * r
  let rH : E.R₂ := E.π₁ (G.f₁ t * s) * r
  let mkH :=
    letI : Algebra C.R₂ E.R₂ := H.f₂.toAlgebra
    TensorProduct.mk C.R₂ E.R₂ (π₂s C M.M) rH
  let lhs : π₂s C M.M →+ π₂s E (M.baseChange H).M :=
    (H.pullbackBaseChangeπ₂ M.M).symm.toLinearMap.toAddMonoidHom.comp
      mkH.toAddMonoidHom
  let mkF :=
    letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
    TensorProduct.mk C.R₂ D.R₂ (π₂s C M.M) aD
  let fMap : π₂s C M.M →+ π₂s D (M.baseChange F).M :=
    (F.pullbackBaseChangeπ₂ M.M).symm.toLinearMap.toAddMonoidHom.comp
      mkF.toAddMonoidHom
  let mkG :=
    letI : Algebra D.R₂ E.R₂ := G.f₂.toAlgebra
    TensorProduct.mk D.R₂ E.R₂ (π₂s D (M.baseChange F).M) aE
  let gMap : π₂s D (M.baseChange F).M →+
      π₂s E ((M.baseChange F).baseChange G).M :=
    (G.pullbackBaseChangeπ₂ (M.baseChange F).M).symm.toLinearMap.toAddMonoidHom.comp
      mkG.toAddMonoidHom
  let bcMap := (baseChangeMap E.π₂ e.toLinearMap).toAddMonoidHom
  let rhs : π₂s C M.M →+ π₂s E (M.baseChange H).M :=
    bcMap.comp (gMap.comp fMap)
  change lhs y = rhs y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul c m =>
      simp only [lhs, rhs, bcMap, gMap, mkG, fMap, mkF, mkH]
      change (H.pullbackBaseChangeπ₂ M.M).symm
          (letI : Algebra C.R₂ E.R₂ := H.f₂.toAlgebra
           rH ⊗ₜ[C.R₂]
            (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
             c ⊗ₜ[C.R₁] m)) =
        (baseChangeMap E.π₂ e.toLinearMap)
          ((G.pullbackBaseChangeπ₂ (M.baseChange F).M).symm
            (letI : Algebra D.R₂ E.R₂ := G.f₂.toAlgebra
             aE ⊗ₜ[D.R₂]
              ((F.pullbackBaseChangeπ₂ M.M).symm
                (letI : Algebra C.R₂ D.R₂ := F.f₂.toAlgebra
                 aD ⊗ₜ[C.R₂]
                  (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
                   c ⊗ₜ[C.R₁] m)))))
      have hF := F.pullbackBaseChangeπ₂_symm_tmul' M.M (D.π₁ t) c m
      with_reducible erw [hF]
      let mD : (M.baseChange F).M :=
        letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
        (1 : D.R₁) ⊗ₜ[C.R₁] m
      let cD : D.R₂ := F.f₂ c * D.π₁ t
      have hG := G.pullbackBaseChangeπ₂_symm_tmul'
        (M.baseChange F).M (E.π₁ s * r) cD mD
      dsimp only [cD, mD] at hG
      with_reducible erw [hG]
      let H := G.comp F
      have hH := H.pullbackBaseChangeπ₂_symm_tmul' M.M
        (E.π₁ (G.f₁ t * s) * r) c m
      dsimp only [H] at hH
      with_reducible erw [hH]
      erw [baseChangeMap_tmul]
      have ha := baseChange_assoc_tmul F.f₁ G.f₁
        (1 : E.R₁) (1 : D.R₁) m
      with_reducible erw [ha]
      with_reducible
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
          map_one, one_mul]
      congr 1
      change G.f₂ (F.f₂ c) * (E.π₁ (G.f₁ t * s) * r) =
        G.f₂ (F.f₂ c * D.π₁ t) * (E.π₁ s * r)
      rw [map_mul, map_mul, G.map_π₁_apply]
      ring

/-- Iterated base change of a descent datum agrees with base change along the
composite cosimplicial ring homomorphism. -/
noncomputable def DescentDatum.baseChangeCompIso
    (F : CosimplicialRingHom C D) (G : CosimplicialRingHom D E)
    (M : DescentDatum.{u, u, u, u} C) :
    (M.baseChange F).baseChange G ≅ M.baseChange (G.comp F) := by
  let e := baseChange_assoc F.f₁ G.f₁ M.M
  let f : (M.baseChange F).baseChange G ⟶ M.baseChange (G.comp F) :=
    { toLinearMap := e.toLinearMap
      commute_φ := by
        change (M.baseChange (G.comp F)).φ.toLinearMap ∘ₗ
            baseChangeMap E.π₁ e.toLinearMap =
          baseChangeMap E.π₂ e.toLinearMap ∘ₗ
            ((M.baseChange F).baseChange G).φ.toLinearMap
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add x y hx hy =>
            simpa only [map_add, LinearMap.comp_apply] using
              congrArg₂ HAdd.hAdd hx hy
        | tmul r y =>
            induction y using TensorProduct.induction_on with
            | zero =>
                simp only [TensorProduct.tmul_zero, map_zero]
            | add y z hy hz =>
                simpa only [TensorProduct.tmul_add, map_add,
                  LinearMap.comp_apply] using congrArg₂ HAdd.hAdd hy hz
            | tmul s z =>
                induction z using TensorProduct.induction_on with
                | zero =>
                    simp only [TensorProduct.tmul_zero, map_zero]
                | add z w hz hw =>
                    simpa only [TensorProduct.tmul_add, map_add,
                      LinearMap.comp_apply] using congrArg₂ HAdd.hAdd hz hw
                | tmul t m =>
                    simp only [LinearMap.comp_apply]
                    dsimp only [e]
                    rw [baseChangeMap_tmul]
                    have he := baseChange_assoc_tmul F.f₁ G.f₁ s t m
                    with_reducible erw [he]
                    change (G.comp F).baseChangePhi M _ =
                      baseChangeMap E.π₂
                        (baseChange_assoc F.f₁ G.f₁ M.M).toLinearMap
                        (G.baseChangePhi (M.baseChange F) _)
                    have hH := (G.comp F).baseChangePhi_tmul M r
                      (G.f₁ t * s) m
                    with_reducible erw [hH]
                    have hG := G.baseChangePhi_tmul (M.baseChange F) r s
                      (letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
                       t ⊗ₜ[C.R₁] m)
                    with_reducible erw [hG]
                    have hF := F.baseChangePhi_tmul M (1 : D.R₂) t m
                    with_reducible erw [hF]
                    let y : π₂s C M.M := M.φ
                      (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
                       (1 : C.R₂) ⊗ₜ[C.R₁] m)
                    have hcomp := pullbackBaseChangeπ₂_comp F G M r s t y
                    dsimp only at hcomp
                    with_reducible
                      simpa only [y, Algebra.smul_def,
                        RingHom.algebraMap_toAlgebra, mul_one] using hcomp }
  exact DescentDatum.isoOfLinearEquiv f e rfl

end BaseChangeComp

end Novikov.Descent.Abstract
