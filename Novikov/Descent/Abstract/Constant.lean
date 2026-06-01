import Novikov.Miscellany.BaseChange
import Novikov.Descent.Abstract.Descent
import Novikov.Miscellany.Projective
import Mathlib.CategoryTheory.Iso

open TensorProduct CategoryTheory

/-!
# Constant descent data

An *extended cosimplicial ring* is a cosimplicial ring together with an extra ring
`R₀` and a map `π₀ : R₀ → R₁` such that `π₁ ∘ π₀ = π₂ ∘ π₀`.

Given an extended cosimplicial ring and a finite projective `R₀`-module `M`,
tensoring up along `π₀` yields a descent datum (a "constant" descent datum).
-/

namespace Novikov.Descent.Abstract

open Novikov.Miscellany

/-- An extended cosimplicial ring adds a ring `R₀` and a map `R₀ → R₁`
such that the two extensions `R₀ → R₁ → R₂` agree. -/
structure ExtendedCosimplicialRing extends CosimplicialRing where
  R₀ : Type*
  [instR₀ : CommRing R₀]
  π₀ : R₀ →+* R₁
  π₁_π₀_eq_π₂_π₀ : π₁.comp π₀ = π₂.comp π₀

attribute [instance] ExtendedCosimplicialRing.instR₀

variable (E : ExtendedCosimplicialRing)

/-- For an extended cosimplicial ring, the composite `ρ₂ ∘ π₀` agrees with
`ρ₁ ∘ π₀`: both reduce to `π₁₂ ∘ π₁ ∘ π₀` using `π₁ ∘ π₀ = π₂ ∘ π₀`. -/
lemma ExtendedCosimplicialRing.ρ₂_comp_π₀_eq :
    E.toCosimplicialRing.ρ₂.comp E.π₀ = E.toCosimplicialRing.ρ₁.comp E.π₀ := by
  dsimp [CosimplicialRing.ρ₁, CosimplicialRing.ρ₂]
  calc
    (E.toCosimplicialRing.π₂₃.comp E.toCosimplicialRing.π₁).comp E.π₀
        = (E.toCosimplicialRing.π₁₂.comp E.toCosimplicialRing.π₂).comp E.π₀ := by
      rw [E.toCosimplicialRing.π₁₂_π₂_eq_π₂₃_π₁.symm]
    _ = E.toCosimplicialRing.π₁₂.comp (E.toCosimplicialRing.π₂.comp E.π₀) := by
      rw [RingHom.comp_assoc]
    _ = E.toCosimplicialRing.π₁₂.comp (E.toCosimplicialRing.π₁.comp E.π₀) := by
      rw [E.π₁_π₀_eq_π₂_π₀]
    _ = (E.toCosimplicialRing.π₁₂.comp E.toCosimplicialRing.π₁).comp E.π₀ := by
      rw [RingHom.comp_assoc]

/-- For an extended cosimplicial ring, the composite `ρ₃ ∘ π₀` agrees with
`ρ₁ ∘ π₀`: both reduce to `π₁₂ ∘ π₁ ∘ π₀` using `π₁ ∘ π₀ = π₂ ∘ π₀` and the
cosimplicial identities. -/
lemma ExtendedCosimplicialRing.ρ₃_comp_π₀_eq :
    E.toCosimplicialRing.ρ₃.comp E.π₀ = E.toCosimplicialRing.ρ₁.comp E.π₀ := by
  dsimp [CosimplicialRing.ρ₁, CosimplicialRing.ρ₃]
  calc
    (E.toCosimplicialRing.π₂₃.comp E.toCosimplicialRing.π₂).comp E.π₀
        = (E.toCosimplicialRing.π₁₃.comp E.toCosimplicialRing.π₂).comp E.π₀ := by
      rw [E.toCosimplicialRing.π₁₃_π₂_eq_π₂₃_π₂.symm]
    _ = E.toCosimplicialRing.π₁₃.comp (E.toCosimplicialRing.π₂.comp E.π₀) := by
      rw [RingHom.comp_assoc]
    _ = E.toCosimplicialRing.π₁₃.comp (E.toCosimplicialRing.π₁.comp E.π₀) := by
      rw [E.π₁_π₀_eq_π₂_π₀]
    _ = (E.toCosimplicialRing.π₁₃.comp E.toCosimplicialRing.π₁).comp E.π₀ := by
      rw [RingHom.comp_assoc]
    _ = (E.toCosimplicialRing.π₁₂.comp E.toCosimplicialRing.π₁).comp E.π₀ := by
      rw [E.toCosimplicialRing.π₁₃_π₁_eq_π₁₂_π₁]

/-- Key naturality fact: for `π₁ ∘ π₀ = π₂ ∘ π₀`, conjugating the base change
of `LinearMap.baseChange R₁ f` by the associativity equivalences yields the
same result regardless of which face map (`π₁` or `π₂`) is used.

Uses `baseChangeMap` to avoid `letI` binders for `Algebra R₁ R₂` in the
conclusion. -/
lemma baseChangeMap_conj_baseChange_assoc
    {R₀ R₁ R₂ : Type*} [CommRing R₀] [CommRing R₁] [CommRing R₂]
    (π₀ : R₀ →+* R₁) (π₁ π₂ : R₁ →+* R₂)
    (h : π₁.comp π₀ = π₂.comp π₀)
    (M N : Type*) [AddCommGroup M] [Module R₀ M]
    [AddCommGroup N] [Module R₀ N]
    (f : M →ₗ[R₀] N) :
    letI : Algebra R₀ R₁ := π₀.toAlgebra
    letI : Algebra R₀ R₂ := (π₁.comp π₀).toAlgebra
    let e₁M : baseChange_along π₁ (R₁ ⊗[R₀] M) ≃ₗ[R₂] (R₂ ⊗[R₀] M) :=
      baseChange_assoc_eq π₀ π₁ (rfl : π₁.comp π₀ = _) M
    let e₂M : baseChange_along π₂ (R₁ ⊗[R₀] M) ≃ₗ[R₂] (R₂ ⊗[R₀] M) :=
      baseChange_assoc_eq π₀ π₂ h.symm M
    let φM : baseChange_along π₁ (R₁ ⊗[R₀] M) ≃ₗ[R₂] baseChange_along π₂ (R₁ ⊗[R₀] M) :=
      e₁M.trans e₂M.symm
    let e₁N : baseChange_along π₁ (R₁ ⊗[R₀] N) ≃ₗ[R₂] (R₂ ⊗[R₀] N) :=
      baseChange_assoc_eq π₀ π₁ (rfl : π₁.comp π₀ = _) N
    let e₂N : baseChange_along π₂ (R₁ ⊗[R₀] N) ≃ₗ[R₂] (R₂ ⊗[R₀] N) :=
      baseChange_assoc_eq π₀ π₂ h.symm N
    let φN : baseChange_along π₁ (R₁ ⊗[R₀] N) ≃ₗ[R₂] baseChange_along π₂ (R₁ ⊗[R₀] N) :=
      e₁N.trans e₂N.symm
    φN ∘ₗ baseChangeMap π₁ (LinearMap.baseChange R₁ f) ∘ₗ φM.symm =
      baseChangeMap π₂ (LinearMap.baseChange R₁ f) := by
  letI : Algebra R₀ R₁ := π₀.toAlgebra
  letI : Algebra R₀ R₂ := (π₁.comp π₀).toAlgebra
  intro e₁M e₂M φM e₁N e₂N φN
  let L₁ : baseChange_along π₁ (R₁ ⊗[R₀] M) →ₗ[R₂] baseChange_along π₁ (R₁ ⊗[R₀] N) := by
    letI : Algebra R₁ R₂ := π₁.toAlgebra
    exact baseChangeMap π₁ (LinearMap.baseChange R₁ f)
  let L₂ : baseChange_along π₂ (R₁ ⊗[R₀] M) →ₗ[R₂] baseChange_along π₂ (R₁ ⊗[R₀] N) := by
    letI : Algebra R₁ R₂ := π₂.toAlgebra
    exact baseChangeMap π₂ (LinearMap.baseChange R₁ f)
  have h₁ : (LinearMap.baseChange R₂ f) ∘ₗ e₁M.toLinearMap = e₁N.toLinearMap ∘ₗ L₁ := by
    letI : Algebra R₁ R₂ := π₁.toAlgebra
    exact baseChange_assoc_naturality π₀ π₁ f
  have h₂ : (LinearMap.baseChange R₂ f) ∘ₗ e₂M.toLinearMap = e₂N.toLinearMap ∘ₗ L₂ := by
    letI : Algebra R₁ R₂ := π₂.toAlgebra
    have aux {ρ : R₀ →+* R₂} (hρ : π₂.comp π₀ = ρ) :
        letI : Algebra R₀ R₁ := π₀.toAlgebra
        letI : Algebra R₁ R₂ := π₂.toAlgebra
        letI : Algebra R₀ R₂ := ρ.toAlgebra
        (LinearMap.baseChange R₂ f) ∘ₗ (baseChange_assoc_eq π₀ π₂ hρ M).toLinearMap =
          (baseChange_assoc_eq π₀ π₂ hρ N).toLinearMap ∘ₗ
            (LinearMap.baseChange R₂ (LinearMap.baseChange R₁ f)) := by
      subst hρ
      exact baseChange_assoc_naturality π₀ π₂ f
    exact aux h.symm
  have hkey : e₁N.toLinearMap ∘ₗ L₁ ∘ₗ e₁M.symm.toLinearMap = LinearMap.baseChange R₂ f := by
    calc
      e₁N.toLinearMap ∘ₗ L₁ ∘ₗ e₁M.symm.toLinearMap
          = (e₁N.toLinearMap ∘ₗ L₁) ∘ₗ e₁M.symm.toLinearMap := by
            rw [← LinearMap.comp_assoc]
      _ = ((LinearMap.baseChange R₂ f) ∘ₗ e₁M.toLinearMap) ∘ₗ e₁M.symm.toLinearMap := by
            rw [← h₁]
      _ = (LinearMap.baseChange R₂ f) ∘ₗ (e₁M.toLinearMap ∘ₗ e₁M.symm.toLinearMap) := rfl
      _ = (LinearMap.baseChange R₂ f) ∘ₗ LinearMap.id := by simp
      _ = LinearMap.baseChange R₂ f := by simp
  have hφN : (φN : baseChange_along π₁ (R₁ ⊗[R₀] N) →ₗ[R₂] baseChange_along π₂ (R₁ ⊗[R₀] N)) =
      (e₂N.symm : R₂ ⊗[R₀] N →ₗ[R₂] baseChange_along π₂ (R₁ ⊗[R₀] N)) ∘ₗ
      (e₁N : baseChange_along π₁ (R₁ ⊗[R₀] N) →ₗ[R₂] R₂ ⊗[R₀] N) := by
    ext x; simp [φN]
  have hφMsymm : (φM.symm : baseChange_along π₂ (R₁ ⊗[R₀] M) →ₗ[R₂] baseChange_along π₁ (R₁ ⊗[R₀] M)) =
      (e₁M.symm : R₂ ⊗[R₀] M →ₗ[R₂] baseChange_along π₁ (R₁ ⊗[R₀] M)) ∘ₗ
      (e₂M : baseChange_along π₂ (R₁ ⊗[R₀] M) →ₗ[R₂] R₂ ⊗[R₀] M) := by
    ext x; simp [φM]
  have hcalc : e₂N.symm.toLinearMap ∘ₗ e₁N.toLinearMap ∘ₗ L₁ ∘ₗ e₁M.symm.toLinearMap ∘ₗ e₂M.toLinearMap = L₂ := by
    calc
      e₂N.symm.toLinearMap ∘ₗ e₁N.toLinearMap ∘ₗ L₁ ∘ₗ e₁M.symm.toLinearMap ∘ₗ e₂M.toLinearMap
          = e₂N.symm.toLinearMap ∘ₗ (e₁N.toLinearMap ∘ₗ L₁ ∘ₗ e₁M.symm.toLinearMap) ∘ₗ
            e₂M.toLinearMap := by
        simp only [LinearMap.comp_assoc]
      _ = e₂N.symm.toLinearMap ∘ₗ (LinearMap.baseChange R₂ f) ∘ₗ e₂M.toLinearMap := by rw [hkey]
      _ = e₂N.symm.toLinearMap ∘ₗ (e₂N.toLinearMap ∘ₗ L₂) := by rw [h₂]
      _ = (e₂N.symm.toLinearMap ∘ₗ e₂N.toLinearMap) ∘ₗ L₂ := by
        simp only [LinearMap.comp_assoc]
      _ = LinearMap.id ∘ₗ L₂ := by simp
      _ = L₂ := by simp
  simpa [hφN, hφMsymm, L₂] using hcalc

private lemma constantDescentDatum_pullback_tmul
    (M : Type*) [AddCommGroup M] [Module E.R₀ M]
    (g : E.R₂ →+* E.R₃)
    (ρ_left ρ_right : E.R₁ →+* E.R₃)
    (hh_left : g.comp E.π₁ = ρ_left)
    (hh_right : g.comp E.π₂ = ρ_right)
    (σ : E.R₀ →+* E.R₃)
    (hσ_right : ρ_right.comp E.π₀ = σ)
    (r : E.R₃) (s : E.R₁) (m : M) :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
    letI : Algebra E.R₀ E.R₃ := σ.toAlgebra
    pullbackMap E.π₁ E.π₂ g hh_left hh_right
      (E.R₁ ⊗[E.R₀] M) (E.R₁ ⊗[E.R₀] M)
      ((baseChange_assoc_eq E.π₀ E.π₁ (rfl : E.π₁.comp E.π₀ = _) M).trans
       (baseChange_assoc_eq E.π₀ E.π₂ E.π₁_π₀_eq_π₂_π₀.symm M).symm)
      (letI : Algebra E.R₁ E.R₃ := ρ_left.toAlgebra; r ⊗ₜ[E.R₁] (s ⊗ₜ[E.R₀] m)) =
    (baseChange_assoc_eq E.π₀ ρ_right hσ_right M).symm
      ((g (E.π₁ s) * r) ⊗ₜ[E.R₀] m) := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra E.R₀ E.R₃ := σ.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
  rw [baseChange_assoc_eq_symm_tmul E.π₀ ρ_right hσ_right M _ _]
  apply pullbackMap_tmul_eq_tmul
  simp only [pullbackMap]
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  rw [Novikov.Miscellany.baseChange_assoc_symm_tmul E.π₁ g r (s ⊗ₜ[E.R₀] m)]
  rw [LinearEquiv.baseChange_tmul]
  dsimp only [LinearEquiv.trans_apply]
  rw [baseChange_assoc_eq_tmul E.π₀ E.π₁ (rfl : E.π₁.comp E.π₀ = _) M (1 : E.R₂) s m]
  letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
  rw [baseChange_assoc_eq_symm_tmul E.π₀ E.π₂ E.π₁_π₀_eq_π₂_π₀.symm M (s • (1 : E.R₂)) m]
  rw [Novikov.Miscellany.baseChange_assoc_tmul E.π₂ g r (s • (1 : E.R₂)) ((1 : E.R₁) ⊗ₜ[E.R₀] m)]
  congr 1
  change g (E.π₁ s * 1) * r = g (E.π₁ s) * r
  simp only [mul_one]

/-- Pullback of the canonical `φ'` factors through the associativity equivalences.

`φ'` is the composition of `baseChange_assoc π₀ π₁` and `(baseChange_assoc π₀ π₂)⁻¹`.
After base change along `g : R₂ → R₃`, tetrahedron coherence shows this equals the
composition of `baseChange_assoc π₀ ρ_a` and `(baseChange_assoc π₀ ρ_b)⁻¹` where
`ρ_a = g ∘ π₁`, `ρ_b = g ∘ π₂`. -/
private lemma constantDescentDatum_pullback_factor
    (E : ExtendedCosimplicialRing)
    (M : Type*) [AddCommGroup M] [Module E.R₀ M]
    (g : E.R₂ →+* E.R₃)
    {ρ_a ρ_b : E.R₁ →+* E.R₃}
    (ha : g.comp E.π₁ = ρ_a) (hb : g.comp E.π₂ = ρ_b)
    {σ : E.R₀ →+* E.R₃}
    (hσa : ρ_a.comp E.π₀ = σ) (hσb : ρ_b.comp E.π₀ = σ) :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    pullbackMap E.π₁ E.π₂ g ha hb (E.R₁ ⊗[E.R₀] M) (E.R₁ ⊗[E.R₀] M)
      ((baseChange_assoc_eq E.π₀ E.π₁ (rfl : E.π₁.comp E.π₀ = _) M).trans
        (baseChange_assoc_eq E.π₀ E.π₂ E.π₁_π₀_eq_π₂_π₀.symm M).symm) =
    (baseChange_assoc_eq E.π₀ ρ_a hσa M).trans
      (baseChange_assoc_eq E.π₀ ρ_b hσb M).symm := by
  subst ha
  subst hb
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra E.R₀ E.R₃ := σ.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
  letI A13 : Algebra E.R₁ E.R₃ := (g.comp E.π₁).toAlgebra
  ext x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r y
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp
    · intro s m
      have htmul := constantDescentDatum_pullback_tmul E M g _ _ rfl rfl σ hσb r s m
      simp only [LinearEquiv.trans_apply]
      rw [htmul]
      rw [baseChange_assoc_eq_tmul E.π₀ (g.comp E.π₁) hσa M r s m]
      rfl
    · intro a b ha' hb'
      simp only [TensorProduct.tmul_add, map_add] at ha' hb' ⊢
      rw [ha', hb']
  · intro a b ha' hb'
    simp only [map_add] at ha' hb' ⊢
    rw [ha', hb']

/-- The constant descent datum associated to a finite projective `R₀`-module `M`.

The underlying `R₁`-module is `R₁ ⊗[R₀] M`, and the cocycle isomorphism `φ` is
obtained by composing the associativity equivalences with the identification
`π₁ ∘ π₀ = π₂ ∘ π₀`. -/
noncomputable def constantDescentDatum (M : Type*) [AddCommGroup M] [Module E.R₀ M]
    [Module.Finite E.R₀ M] [Module.Projective E.R₀ M] :
    DescentDatum E.toCosimplicialRing := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  -- Choose a single Algebra E.R₀ E.R₂ as the canonical middle algebra.
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  -- Each side: assoc to the common middle `E.R₂ ⊗[E.R₀] M` with algebra `A02`.
  let e1 :
      π₁s E.toCosimplicialRing (E.R₁ ⊗[E.R₀] M) ≃ₗ[E.R₂] (E.R₂ ⊗[E.R₀] M) := by
    change (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
          E.R₂ ⊗[E.R₁] (E.R₁ ⊗[E.R₀] M)) ≃ₗ[E.R₂] (E.R₂ ⊗[E.R₀] M)
    exact Novikov.Miscellany.baseChange_assoc_eq E.π₀ E.π₁
      (rfl : E.π₁.comp E.π₀ = _) M
  let e2 :
      π₂s E.toCosimplicialRing (E.R₁ ⊗[E.R₀] M) ≃ₗ[E.R₂] (E.R₂ ⊗[E.R₀] M) := by
    change (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
          E.R₂ ⊗[E.R₁] (E.R₁ ⊗[E.R₀] M)) ≃ₗ[E.R₂] (E.R₂ ⊗[E.R₀] M)
    exact Novikov.Miscellany.baseChange_assoc_eq E.π₀ E.π₂
      E.π₁_π₀_eq_π₂_π₀.symm M
  let φ' :
      π₁s E.toCosimplicialRing (E.R₁ ⊗[E.R₀] M) ≃ₗ[E.R₂]
      π₂s E.toCosimplicialRing (E.R₁ ⊗[E.R₀] M) :=
    e1.trans e2.symm
  exact
  { M := E.R₁ ⊗[E.R₀] M
    instAddCommGroup := inferInstance
    instModule := inferInstance
    instFinite := Module.Finite.base_change E.R₀ E.R₁ M
    instProjective := Novikov.Miscellany.baseChange_projective M
    φ := φ'
    cocycle := by
      letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
      letI : Algebra E.R₂ E.R₃ := E.π₁₂.toAlgebra
      -- Common composition σ : R₀ → R₃ used as the canonical Algebra R₀ → R₃.
      set σ : E.R₀ →+* E.R₃ := E.toCosimplicialRing.ρ₁.comp E.π₀ with hσ
      have hρ₁_σ : E.toCosimplicialRing.ρ₁.comp E.π₀ = σ := rfl
      have hρ₂_σ : E.toCosimplicialRing.ρ₂.comp E.π₀ = σ := E.ρ₂_comp_π₀_eq
      have hρ₃_σ : E.toCosimplicialRing.ρ₃.comp E.π₀ = σ := E.ρ₃_comp_π₀_eq
      letI A03 : Algebra E.R₀ E.R₃ := σ.toAlgebra
      -- Each `pullbackMap_ij φ'` factors through the associativity equivalences.
      have h12 := constantDescentDatum_pullback_factor (E := E) (M := M)
        E.toCosimplicialRing.π₁₂
        E.toCosimplicialRing.ρ₁_eq_π₁₂_π₁.symm
        E.toCosimplicialRing.ρ₂_eq_π₁₂_π₂.symm
        hρ₁_σ hρ₂_σ
      have h23 := constantDescentDatum_pullback_factor (E := E) (M := M)
        E.toCosimplicialRing.π₂₃ rfl rfl hρ₂_σ hρ₃_σ
      have h13 := constantDescentDatum_pullback_factor (E := E) (M := M)
        E.toCosimplicialRing.π₁₃
        E.toCosimplicialRing.ρ₁_eq_π₁₃_π₁.symm
        E.toCosimplicialRing.ρ₃_eq_π₁₃_π₂.symm
        hρ₁_σ hρ₃_σ
      -- φ' is let-bound; expose its expanded form for rewriting.
      have hφ : φ' = (baseChange_assoc_eq E.π₀ E.π₁ (rfl : E.π₁.comp E.π₀ = _) M).trans
          (baseChange_assoc_eq E.π₀ E.π₂ E.π₁_π₀_eq_π₂_π₀.symm M).symm := rfl
      unfold pullbackMap_12 pullbackMap_23 pullbackMap_13
      simp only [hφ, h12, h23, h13]
      -- Goal: (a₂.trans a₃.symm).toLM ∘ (a₁.trans a₂.symm).toLM = (a₁.trans a₃.symm).toLM
      ext x
      change (baseChange_assoc_eq E.π₀ E.ρ₃ hρ₃_σ M).symm
          ((baseChange_assoc_eq E.π₀ E.ρ₂ hρ₂_σ M)
            ((baseChange_assoc_eq E.π₀ E.ρ₂ hρ₂_σ M).symm
              ((baseChange_assoc_eq E.π₀ E.ρ₁ hρ₁_σ M) x))) =
        (baseChange_assoc_eq E.π₀ E.ρ₃ hρ₃_σ M).symm ((baseChange_assoc_eq E.π₀ E.ρ₁ hρ₁_σ M) x)
      rw [LinearEquiv.apply_symm_apply]
  }

@[simp]
lemma constantDescentDatum_φ_tmul (M : Type*) [AddCommGroup M] [Module E.R₀ M]
    [Module.Finite E.R₀ M] [Module.Projective E.R₀ M]
    (r : E.R₂) (s : E.R₁) (m : M) :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
    (constantDescentDatum E M).φ
      (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
       r ⊗ₜ[E.R₁] (s ⊗ₜ[E.R₀] m)) =
    (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
     (E.π₁ s * r) ⊗ₜ[E.R₁] ((1 : E.R₁) ⊗ₜ[E.R₀] m)) := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  change ((baseChange_assoc_eq E.π₀ E.π₁ (rfl : E.π₁.comp E.π₀ = _) M).trans
      (baseChange_assoc_eq E.π₀ E.π₂ E.π₁_π₀_eq_π₂_π₀.symm M).symm)
      (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
       r ⊗ₜ[E.R₁] (s ⊗ₜ[E.R₀] m)) = _
  rw [LinearEquiv.trans_apply]
  rw [baseChange_assoc_eq_tmul]
  change (baseChange_assoc_eq E.π₀ E.π₂ E.π₁_π₀_eq_π₂_π₀.symm M).symm
      ((E.π₁ s * r) ⊗ₜ[E.R₀] m) = _
  rw [baseChange_assoc_eq_symm_tmul]

private lemma internalHom_φ_one_tmul_baseChange
    (E : ExtendedCosimplicialRing) (M N : Type*)
    [AddCommGroup M] [Module E.R₀ M] [Module.Finite E.R₀ M] [Module.Projective E.R₀ M]
    [AddCommGroup N] [Module E.R₀ N] [Module.Finite E.R₀ N] [Module.Projective E.R₀ N]
    (f : M →ₗ[E.R₀] N) :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
    (DescentDatum.internalHom (constantDescentDatum E M) (constantDescentDatum E N)).φ
      (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
       (1 : E.R₂) ⊗ₜ[E.R₁] LinearMap.baseChange E.R₁ f) =
    (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
     (1 : E.R₂) ⊗ₜ[E.R₁] LinearMap.baseChange E.R₁ f) := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  let g := LinearMap.baseChange E.R₁ f
  let C := E.toCosimplicialRing
  let M_dd : DescentDatum C := constantDescentDatum E M
  let N_dd : DescentDatum C := constantDescentDatum E N
  have hkey : N_dd.φ.toLinearMap ∘ₗ baseChangeMap E.π₁ g ∘ₗ M_dd.φ.symm.toLinearMap =
      baseChangeMap E.π₂ g :=
    baseChangeMap_conj_baseChange_assoc E.π₀ E.π₁ E.π₂ E.π₁_π₀_eq_π₂_π₀ M N f
  have h_iff := DescentDatum.hom_iff_eq_φ (C := C) (M := M_dd) (N := N_dd) (f := g)
  apply h_iff.mp
  have h := (LinearEquiv.eq_comp_toLinearMap_symm
    (baseChangeMap E.π₂ g)
    (N_dd.φ.toLinearMap ∘ₗ baseChangeMap E.π₁ g)).mp hkey.symm
  exact h.symm

-- Fence: keep `homBaseChangeEquiv` opaque so the unifier in the proofs below
-- matches it by head symbol instead of unfolding its heavy body (~33% less
-- tactic-execution time). Restored to `semireducible` after the iso def.
attribute [local irreducible] homBaseChangeEquiv

lemma constantDescentDatum_internalHom_hom_commute_φ
    {E : ExtendedCosimplicialRing}
    (M N : Type*) [AddCommGroup M] [Module E.R₀ M] [Module.Finite E.R₀ M] [Module.Projective E.R₀ M]
    [AddCommGroup N] [Module E.R₀ N] [Module.Finite E.R₀ N] [Module.Projective E.R₀ N] :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    (DescentDatum.internalHom (constantDescentDatum E M) (constantDescentDatum E N)).φ.toLinearMap ∘ₗ
      (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
       LinearMap.baseChange E.R₂ (homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁).toLinearMap) =
    (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
     LinearMap.baseChange E.R₂ (homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁).toLinearMap) ∘ₗ
      (constantDescentDatum E (M →ₗ[E.R₀] N)).φ.toLinearMap := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  let Hom := M →ₗ[E.R₀] N
  let α : (E.R₂ ⊗[E.R₀] Hom) ≃ₗ[E.R₂] baseChange_along E.π₁ (E.R₁ ⊗[E.R₀] Hom) :=
    (baseChange_assoc_eq E.π₀ E.π₁ (rfl : E.π₁.comp E.π₀ = _) Hom).symm
  have hα_surj : Function.Surjective
      (α : E.R₂ ⊗[E.R₀] Hom → baseChange_along E.π₁ (E.R₁ ⊗[E.R₀] Hom)) :=
    α.surjective
  ext y
  obtain ⟨x, rfl⟩ := hα_surj y
  simp only [LinearMap.comp_apply]
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r f
    have h_scale : α (r ⊗ₜ[E.R₀] f) = r • α ((1 : E.R₂) ⊗ₜ[E.R₀] f) := by
      simp [α, baseChange_assoc_eq_symm_tmul, TensorProduct.smul_tmul']
    rw [h_scale]
    simp only [map_smul]
    congr 1
    have hα_one : α ((1 : E.R₂) ⊗ₜ[E.R₀] f) =
        (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
         (1 : E.R₂) ⊗ₜ[E.R₁] ((1 : E.R₁) ⊗ₜ[E.R₀] f)) := by
      simp [α, baseChange_assoc_eq_symm_tmul]
    have hφ_step : (constantDescentDatum E Hom).φ
        (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
         (1 : E.R₂) ⊗ₜ[E.R₁] ((1 : E.R₁) ⊗ₜ[E.R₀] f)) =
        (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
         (1 : E.R₂) ⊗ₜ[E.R₁] ((1 : E.R₁) ⊗ₜ[E.R₀] f)) := by
      simp [constantDescentDatum_φ_tmul]
    have hbc_one : (↑(homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁) :
        E.R₁ ⊗[E.R₀] Hom →ₗ[E.R₁] _)
        (1 ⊗ₜ[E.R₀] f) = LinearMap.baseChange E.R₁ f := by
      letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
      simp only [LinearEquiv.coe_toLinearMap]
      exact (homBaseChangeEquiv_tmul E.R₁ 1 f).trans (one_smul _ _)
    rw [hα_one]
    change ((DescentDatum.internalHom (constantDescentDatum E M) (constantDescentDatum E N)).φ.toLinearMap)
        ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
          LinearMap.baseChange E.R₂
            (homBaseChangeEquiv (R:=E.R₀) (M:=M) (N:=N) E.R₁).toLinearMap
            ((1:E.R₂) ⊗ₜ[E.R₁] ((1:E.R₁) ⊗ₜ[E.R₀] f)))) =
      (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
       LinearMap.baseChange E.R₂
         (homBaseChangeEquiv (R:=E.R₀) (M:=M) (N:=N) E.R₁).toLinearMap)
        ((constantDescentDatum E Hom).φ
          (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
           (1:E.R₂) ⊗ₜ[E.R₁] ((1:E.R₁) ⊗ₜ[E.R₀] f)))
    rw [hφ_step]
    change ((DescentDatum.internalHom (constantDescentDatum E M) (constantDescentDatum E N)).φ.toLinearMap)
        ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
          LinearMap.baseChange E.R₂
            (homBaseChangeEquiv (R:=E.R₀) (M:=M) (N:=N) E.R₁).toLinearMap
            ((1:E.R₂) ⊗ₜ[E.R₁] ((1:E.R₁) ⊗ₜ[E.R₀] f)))) =
      (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
       (1:E.R₂) ⊗ₜ[E.R₁]
          ((homBaseChangeEquiv (R:=E.R₀) (M:=M) (N:=N) E.R₁).toLinearMap
            ((1:E.R₁) ⊗ₜ[E.R₀] f)))
    have hlhs : (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
        LinearMap.baseChange E.R₂
          (homBaseChangeEquiv (R:=E.R₀) (M:=M) (N:=N) E.R₁).toLinearMap
          ((1:E.R₂) ⊗ₜ[E.R₁] ((1:E.R₁) ⊗ₜ[E.R₀] f))) =
        (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
         (1:E.R₂) ⊗ₜ[E.R₁] LinearMap.baseChange E.R₁ f) := by
      simp [LinearMap.baseChange_tmul, hbc_one]
    rw [hlhs, hbc_one]
    exact internalHom_φ_one_tmul_baseChange E M N f
  · intro x y hx hy
    simp [map_add, hx, hy]

private lemma comp_symm_of_comp {R : Type*} [CommSemiring R]
    {M₁ M₂ N₁ N₂ : Type*}
    [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    [AddCommMonoid N₁] [Module R N₁] [AddCommMonoid N₂] [Module R N₂]
    {Φ : M₂ →ₗ[R] N₂} {Ψ : M₁ →ₗ[R] N₁}
    {B : M₁ ≃ₗ[R] M₂} {C : N₁ ≃ₗ[R] N₂}
    (h : Φ ∘ₗ B.toLinearMap = C.toLinearMap ∘ₗ Ψ) :
    Ψ ∘ₗ B.symm.toLinearMap = C.symm.toLinearMap ∘ₗ Φ := by
  ext x
  have := LinearMap.congr_fun h (B.symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, B.apply_symm_apply] at this
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [this, C.symm_apply_apply]

lemma constantDescentDatum_internalHom_inv_commute_φ
    {E : ExtendedCosimplicialRing}
    (M N : Type*) [AddCommGroup M] [Module E.R₀ M] [Module.Finite E.R₀ M] [Module.Projective E.R₀ M]
    [AddCommGroup N] [Module E.R₀ N] [Module.Finite E.R₀ N] [Module.Projective E.R₀ N] :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    (constantDescentDatum E (M →ₗ[E.R₀] N)).φ.toLinearMap ∘ₗ
      (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
       LinearMap.baseChange E.R₂ (homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁).symm.toLinearMap) =
    (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
     LinearMap.baseChange E.R₂ (homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁).symm.toLinearMap) ∘ₗ
      (DescentDatum.internalHom (constantDescentDatum E M) (constantDescentDatum E N)).φ.toLinearMap := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  let B := letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
    LinearEquiv.baseChange E.R₁ E.R₂ _ _ (homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁)
  let C := letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
    LinearEquiv.baseChange E.R₁ E.R₂ _ _ (homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁)
  exact comp_symm_of_comp (B := B) (C := C)
    (constantDescentDatum_internalHom_hom_commute_φ (E := E) M N)

noncomputable def constantDescentDatum_internalHom
    (M N : Type*) [AddCommGroup M] [Module E.R₀ M] [Module.Finite E.R₀ M] [Module.Projective E.R₀ M]
    [AddCommGroup N] [Module E.R₀ N] [Module.Finite E.R₀ N] [Module.Projective E.R₀ N] :
    constantDescentDatum E (M →ₗ[E.R₀] N) ≅ 
    DescentDatum.internalHom (constantDescentDatum E M) (constantDescentDatum E N) :=
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  {
    hom := {
      toLinearMap := (homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁).toLinearMap
      commute_φ := constantDescentDatum_internalHom_hom_commute_φ M N
    }
    inv := {
      toLinearMap := (homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁).symm.toLinearMap
      commute_φ := constantDescentDatum_internalHom_inv_commute_φ M N
    }
    hom_inv_id := by
      apply Novikov.Descent.Abstract.DescentDatum.hom_ext
      ext x
      exact LinearEquiv.left_inv (homBaseChangeEquiv E.R₁) x
    inv_hom_id := by
      apply Novikov.Descent.Abstract.DescentDatum.hom_ext
      ext x
      exact LinearEquiv.right_inv (homBaseChangeEquiv E.R₁) x
  }

attribute [local semireducible] homBaseChangeEquiv

/-- Base-changing a map of `R₀`-modules gives a morphism of the corresponding
constant descent data. -/
noncomputable def constantDescentDatumMap (M N : FiniteProjectiveModule E.R₀)
    (f : M ⟶ N) : constantDescentDatum E M.M ⟶ constantDescentDatum E N.M := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  exact
  { toLinearMap := LinearMap.baseChange E.R₁ f
    commute_φ := by
      let g := LinearMap.baseChange E.R₁ f
      let Mdd : DescentDatum E.toCosimplicialRing := constantDescentDatum E M.M
      let Ndd : DescentDatum E.toCosimplicialRing := constantDescentDatum E N.M
      exact (DescentDatum.hom_iff_eq_φ (C := E.toCosimplicialRing) (M := Mdd) (N := Ndd)
        (f := g)).mpr (internalHom_φ_one_tmul_baseChange E M.M N.M f) }

@[simp]
lemma constantDescentDatumMap_toLinearMap (M N : FiniteProjectiveModule E.R₀) (f : M ⟶ N) :
    (constantDescentDatumMap E M N f).toLinearMap =
      (letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra; LinearMap.baseChange E.R₁ f) :=
  rfl

/-- The constant descent datum construction as a functor from finite projective
`R₀`-modules to descent data. -/
noncomputable def constantDescentDatumFunctor :
    FiniteProjectiveModule E.R₀ ⥤ DescentDatum E.toCosimplicialRing where
  obj M := constantDescentDatum E M.M
  map {M N} f := constantDescentDatumMap E M N f
  map_id M := by
    apply DescentDatum.hom_ext
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    change LinearMap.baseChange E.R₁ (LinearMap.id : M.M →ₗ[E.R₀] M.M) = LinearMap.id
    exact LinearMap.baseChange_id (A := E.R₁) (M := M.M)
  map_comp {X Y Z} f g := by
    apply DescentDatum.hom_ext
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    change LinearMap.baseChange E.R₁ (g.comp f) =
      (LinearMap.baseChange E.R₁ g).comp (LinearMap.baseChange E.R₁ f)
    exact LinearMap.baseChange_comp (A := E.R₁) f g

end Novikov.Descent.Abstract
