import Novikov.Descent.Abstract.BaseChange
import Mathlib.CategoryTheory.Iso

/-!
# Transport of descent data

This file transports a descent datum across a linear equivalence of its
underlying finite projective module.  The transported descent isomorphism is
obtained by conjugating with the two pullbacks of the equivalence.
-/

open CategoryTheory TensorProduct

namespace Novikov.Descent.Abstract

open Novikov.Miscellany

section

variable {R₁ R₂ R₃ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₃]

private lemma pullbackMap_naturality
    (f₁ f₂ : R₁ →+* R₂) (g : R₂ →+* R₃)
    {h₁ h₂ : R₁ →+* R₃} (hh₁ : g.comp f₁ = h₁) (hh₂ : g.comp f₂ = h₂)
    (M₁ M₂ N₁ N₂ : Type*)
    [AddCommGroup M₁] [Module R₁ M₁]
    [AddCommGroup M₂] [Module R₁ M₂]
    [AddCommGroup N₁] [Module R₁ N₁]
    [AddCommGroup N₂] [Module R₁ N₂]
    (φM : baseChange_along f₁ M₁ ≃ₗ[R₂] baseChange_along f₂ M₂)
    (φN : baseChange_along f₁ N₁ ≃ₗ[R₂] baseChange_along f₂ N₂)
    (u₁ : M₁ →ₗ[R₁] N₁) (u₂ : M₂ →ₗ[R₁] N₂)
    (hφ : φN.toLinearMap ∘ₗ baseChangeMap f₁ u₁ =
      baseChangeMap f₂ u₂ ∘ₗ φM.toLinearMap) :
    (pullbackMap f₁ f₂ g hh₁ hh₂ N₁ N₂ φN).toLinearMap ∘ₗ
        baseChangeMap h₁ u₁ =
      baseChangeMap h₂ u₂ ∘ₗ
        (pullbackMap f₁ f₂ g hh₁ hh₂ M₁ M₂ φM).toLinearMap := by
  subst h₁
  subst h₂
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, LinearMap.comp_apply] at hx hy ⊢
      rw [hx, hy]
  | tmul r m =>
      simp only [LinearMap.comp_apply]
      rw [baseChangeMap_tmul]
      erw [pullbackMap_tmul_apply f₁ f₂ g rfl rfl N₁ N₂ φN r (u₁ m)]
      erw [pullbackMap_tmul_apply f₁ f₂ g rfl rfl M₁ M₂ φM r m]
      have hm := LinearMap.congr_fun hφ
        (letI : Algebra R₁ R₂ := f₁.toAlgebra; (1 : R₂) ⊗ₜ[R₁] m)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, baseChangeMap_tmul] at hm
      rw [hm]
      have hnat := baseChange_assoc_naturality f₂ g u₂
      have hnat_apply := LinearMap.congr_fun hnat
        (letI : Algebra R₁ R₂ := f₂.toAlgebra
         letI : Algebra R₂ R₃ := g.toAlgebra
         r ⊗ₜ[R₂] (φM (letI : Algebra R₁ R₂ := f₁.toAlgebra;
           (1 : R₂) ⊗ₜ[R₁] m)))
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at hnat_apply
      exact hnat_apply.symm

end

namespace DescentDatum

variable {C : CosimplicialRing}
variable (M : DescentDatum C)
variable {N : Type*} [AddCommGroup N] [Module C.R₁ N]
  [Module.Finite C.R₁ N] [Module.Projective C.R₁ N]

/-- Pullback along `π₁` of an equivalence used to transport a descent datum. -/
noncomputable def transportπ₁Equiv (e : M.M ≃ₗ[C.R₁] N) :
    π₁s C M.M ≃ₗ[C.R₂] π₁s C N := by
  letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
  exact LinearEquiv.baseChange C.R₁ C.R₂ M.M N e

/-- Pullback along `π₂` of an equivalence used to transport a descent datum. -/
noncomputable def transportπ₂Equiv (e : M.M ≃ₗ[C.R₁] N) :
    π₂s C M.M ≃ₗ[C.R₂] π₂s C N := by
  letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
  exact LinearEquiv.baseChange C.R₁ C.R₂ M.M N e

/-- The descent isomorphism obtained by conjugating `M.φ` across `e`. -/
noncomputable def transportPhi (e : M.M ≃ₗ[C.R₁] N) :
    π₁s C N ≃ₗ[C.R₂] π₂s C N :=
  (transportπ₁Equiv M e).symm.trans (M.φ.trans (transportπ₂Equiv M e))

/-- Transport a descent datum across an equivalence of its underlying module. -/
noncomputable def transport (e : M.M ≃ₗ[C.R₁] N) : DescentDatum C := by
  let φN := transportPhi M e
  refine
    { M := N
      φ := φN
      cocycle := ?_ }
  have hφ : φN.toLinearMap ∘ₗ baseChangeMap C.π₁ e.toLinearMap =
      baseChangeMap C.π₂ e.toLinearMap ∘ₗ M.φ.toLinearMap := by
    apply LinearMap.ext
    intro x
    change (transportπ₂Equiv M e)
        (M.φ ((transportπ₁Equiv M e).symm ((transportπ₁Equiv M e) x))) =
      (transportπ₂Equiv M e) (M.φ x)
    simp
  have h12 :
      (pullbackMap_12 C N φN).toLinearMap ∘ₗ
          baseChangeMap C.ρ₁ e.toLinearMap =
        baseChangeMap C.ρ₂ e.toLinearMap ∘ₗ
          (pullbackMap_12 C M.M M.φ).toLinearMap :=
    pullbackMap_naturality C.π₁ C.π₂ C.π₁₂
      C.ρ₁_eq_π₁₂_π₁.symm C.ρ₂_eq_π₁₂_π₂.symm
      M.M M.M N N M.φ φN e.toLinearMap e.toLinearMap hφ
  have h23 :
      (pullbackMap_23 C N φN).toLinearMap ∘ₗ
          baseChangeMap C.ρ₂ e.toLinearMap =
        baseChangeMap C.ρ₃ e.toLinearMap ∘ₗ
          (pullbackMap_23 C M.M M.φ).toLinearMap :=
    pullbackMap_naturality C.π₁ C.π₂ C.π₂₃ rfl rfl
      M.M M.M N N M.φ φN e.toLinearMap e.toLinearMap hφ
  have h13 :
      (pullbackMap_13 C N φN).toLinearMap ∘ₗ
          baseChangeMap C.ρ₁ e.toLinearMap =
        baseChangeMap C.ρ₃ e.toLinearMap ∘ₗ
          (pullbackMap_13 C M.M M.φ).toLinearMap :=
    pullbackMap_naturality C.π₁ C.π₂ C.π₁₃
      C.ρ₁_eq_π₁₃_π₁.symm C.ρ₃_eq_π₁₃_π₂.symm
      M.M M.M N N M.φ φN e.toLinearMap e.toLinearMap hφ
  let eρ₁ : ρ₁s C M.M ≃ₗ[C.R₃] ρ₁s C N := by
    letI : Algebra C.R₁ C.R₃ := C.ρ₁.toAlgebra
    exact LinearEquiv.baseChange C.R₁ C.R₃ M.M N e
  funext x
  obtain ⟨y, rfl⟩ := eρ₁.surjective x
  simp only [Function.comp_apply, LinearEquiv.coe_coe]
  have h12y := LinearMap.congr_fun h12 y
  have h23y := LinearMap.congr_fun h23 ((pullbackMap_12 C M.M M.φ) y)
  have h13y := LinearMap.congr_fun h13 y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h12y h23y h13y
  have heρ₁ (z : ρ₁s C M.M) :
      baseChangeMap C.ρ₁ e.toLinearMap z = eρ₁ z := rfl
  rw [heρ₁] at h12y h13y
  rw [h12y, h23y]
  rw [show (pullbackMap_23 C M.M M.φ)
      ((pullbackMap_12 C M.M M.φ) y) =
      (pullbackMap_13 C M.M M.φ) y by
        exact congrFun M.cocycle y]
  exact h13y.symm

@[simp]
lemma transport_M (e : M.M ≃ₗ[C.R₁] N) : (M.transport e).M = N := rfl

@[simp]
lemma transport_φ (e : M.M ≃ₗ[C.R₁] N) :
    (M.transport e).φ = transportPhi M e := rfl

@[simp]
lemma transport_φ_apply (e : M.M ≃ₗ[C.R₁] N) (x : π₁s C N) :
    (M.transport e).φ x =
      transportπ₂Equiv M e (M.φ ((transportπ₁Equiv M e).symm x)) := rfl

/-- The canonical isomorphism from a descent datum to its transport. -/
noncomputable def transportIso (e : M.M ≃ₗ[C.R₁] N) :
    M ≅ M.transport e where
  hom :=
    { toLinearMap := e.toLinearMap
      commute_φ := by
        apply LinearMap.ext
        intro x
        change (transportπ₂Equiv M e)
            (M.φ ((transportπ₁Equiv M e).symm ((transportπ₁Equiv M e) x))) =
          (transportπ₂Equiv M e) (M.φ x)
        simp }
  inv :=
    { toLinearMap := e.symm.toLinearMap
      commute_φ := by
        apply LinearMap.ext
        intro x
        change M.φ ((transportπ₁Equiv M e).symm x) =
          (transportπ₂Equiv M e).symm
            ((transportπ₂Equiv M e)
              (M.φ ((transportπ₁Equiv M e).symm x)))
        simp }
  hom_inv_id := by
    apply hom_ext
    change e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    apply hom_ext
    change e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id
    ext x
    exact e.apply_symm_apply x

@[simp]
lemma transportIso_hom_toLinearMap (e : M.M ≃ₗ[C.R₁] N) :
    (M.transportIso e).hom.toLinearMap = e.toLinearMap := rfl

@[simp]
lemma transportIso_inv_toLinearMap (e : M.M ≃ₗ[C.R₁] N) :
    (M.transportIso e).inv.toLinearMap = e.symm.toLinearMap := rfl

/-- The underlying linear equivalence of an isomorphism of descent data. -/
noncomputable def isoLinearEquiv
    {C : CosimplicialRing} {M N : DescentDatum C} (e : M ≅ N) :
    M.M ≃ₗ[C.R₁] N.M :=
  LinearEquiv.ofLinear e.hom.toLinearMap e.inv.toLinearMap
    (congrArg DescentDatum.Hom.toLinearMap e.inv_hom_id)
    (congrArg DescentDatum.Hom.toLinearMap e.hom_inv_id)

private theorem baseChangeMap_iso_hom_surjective
    {C : CosimplicialRing} {M N : DescentDatum C}
    (i : M ≅ N) {S : Type*} [CommRing S] (q : C.R₁ →+* S) :
    Function.Surjective (baseChangeMap q i.hom.toLinearMap) := by
  letI : Algebra C.R₁ S := q.toAlgebra
  let e := isoLinearEquiv i
  change Function.Surjective (LinearMap.baseChange S e.toLinearMap)
  exact (LinearEquiv.baseChange C.R₁ S M.M N.M e).surjective

private theorem linearMap_eq_of_commute
    {R X Y X' Y' : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup X'] [Module R X'] [AddCommGroup Y'] [Module R Y']
    (φM : X →ₗ[R] Y) (φ₁ φ₂ : X' →ₗ[R] Y')
    (f₁ g₁ : X →ₗ[R] X') (f₂ g₂ : Y →ₗ[R] Y')
    (h₁ : φ₁.comp f₁ = f₂.comp φM)
    (h₂ : φ₂.comp g₁ = g₂.comp φM)
    (hfg₁ : f₁ = g₁) (hfg₂ : f₂ = g₂)
    (hg₁ : Function.Surjective g₁) : φ₁ = φ₂ := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := hg₁ x
  have hz₁ := LinearMap.congr_fun h₁ z
  have hz₂ := LinearMap.congr_fun h₂ z
  simp only [LinearMap.comp_apply] at hz₁ hz₂
  rw [hfg₁, hfg₂] at hz₁
  exact hz₁.trans hz₂.symm

/-- If an isomorphism after base change has underlying equivalence equal to the
base change of `e`, then base change of the datum transported along `e` has the
same descent isomorphism as the target datum. -/
theorem baseChange_transport_φ
    {C D : CosimplicialRing} (F : CosimplicialRingHom C D)
    (M K : DescentDatum C) (e : M.M ≃ₗ[C.R₁] K.M)
    (i : M.baseChange F ≅ K.baseChange F)
    (hi :
      (letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
       LinearEquiv.baseChange C.R₁ D.R₁ M.M K.M e) =
        isoLinearEquiv i) :
    ((M.transport e).baseChange F).φ = (K.baseChange F).φ := by
  have himap : baseChangeMap F.f₁ e.toLinearMap = i.hom.toLinearMap := by
    exact congrArg LinearEquiv.toLinearMap hi
  have hY := F.baseChangePhi_naturality (M.transportIso e).hom
  rw [transportIso_hom_toLinearMap] at hY
  have hi₁ := congrArg (fun f => baseChangeMap D.π₁ f) himap
  have hi₂ := congrArg (fun f => baseChangeMap D.π₂ f) himap
  have hK := i.hom.commute_φ
  have hsurj : Function.Surjective
      (baseChangeMap D.π₁ i.hom.toLinearMap) :=
    baseChangeMap_iso_hom_surjective i D.π₁
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (linearMap_eq_of_commute
    (M.baseChange F).φ.toLinearMap
    ((M.transport e).baseChange F).φ.toLinearMap
    (K.baseChange F).φ.toLinearMap
    (baseChangeMap D.π₁ (baseChangeMap F.f₁ e.toLinearMap))
    (baseChangeMap D.π₁ i.hom.toLinearMap)
    (baseChangeMap D.π₂ (baseChangeMap F.f₁ e.toLinearMap))
    (baseChangeMap D.π₂ i.hom.toLinearMap)
    hY hK hi₁ hi₂ hsurj) x

/-- Under the hypotheses of `baseChange_transport_φ`, direct scalar extension
of the transported and target descent isomorphisms to level two agrees. -/
theorem baseChangeMap_transport_φ_eq
    {C D : CosimplicialRing} (F : CosimplicialRingHom C D)
    (M K : DescentDatum C) (e : M.M ≃ₗ[C.R₁] K.M)
    (i : M.baseChange F ≅ K.baseChange F)
    (hi :
      (letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
       LinearEquiv.baseChange C.R₁ D.R₁ M.M K.M e) =
        isoLinearEquiv i) :
    baseChangeMap F.f₂ (M.transport e).φ.toLinearMap =
      baseChangeMap F.f₂ K.φ.toLinearMap := by
  have hbar := congrArg LinearEquiv.toLinearMap
    (baseChange_transport_φ F M K e i hi)
  let p₁ := F.pullbackBaseChangeπ₁ K.M
  let p₂ := F.pullbackBaseChangeπ₂ K.M
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hbar (p₁.symm x)
  change p₂.symm
      (baseChangeMap F.f₂ (M.transport e).φ.toLinearMap
        (p₁ (p₁.symm x))) =
    p₂.symm
      (baseChangeMap F.f₂ K.φ.toLinearMap (p₁ (p₁.symm x))) at hx
  rw [p₁.apply_symm_apply] at hx
  exact p₂.symm.injective hx

end DescentDatum

end Novikov.Descent.Abstract
