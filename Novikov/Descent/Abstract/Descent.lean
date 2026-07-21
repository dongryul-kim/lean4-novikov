import Novikov.Miscellany.BaseChange
import Novikov.Miscellany.Projective
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.CategoryTheory.Iso

open CategoryTheory

/-!
# Descent data over a cosimplicial ring

A *cosimplicial ring* (truncated to levels 1–3) consists of three rings
`R₁, R₂, R₃` together with ring homomorphisms

```
       π₁
  R₁ ------> R₂
       π₂

           π₁₂
         ------>
  R₁  →  R₂  π₁₃  R₃
         ------>
           π₂₃

  R₁ ------> R₃
       ρ₁, ρ₂, ρ₃
```

satisfying the composition identities
  ρ₁ = π₁₂ ∘ π₁ = π₁₃ ∘ π₁
  ρ₂ = π₁₂ ∘ π₂ = π₂₃ ∘ π₁
  ρ₃ = π₁₃ ∘ π₂ = π₂₃ ∘ π₂

Given a cosimplicial ring `C`, a *descent datum* is a finite projective
`R₁`-module `M` together with an `R₂`-linear isomorphism
`φ : R₂ ⊗_{R₁, π₁} M ≃ R₂ ⊗_{R₁, π₂} M` satisfying the cocycle condition
`π₂₃^* φ ∘ π₁₂^* φ = π₁₃^* φ`.
-/

open TensorProduct

namespace Novikov.Descent.Abstract

open Novikov.Miscellany

/-- A cosimplicial ring truncated to levels 1–3.

The composites `ρ_i : R₁ → R₃` are *defined* by specific compositions of the
face maps, with three propositional identifications among the alternate
compositions (one per `ρ_i`).  Choosing definitions rather than fields
lets `pullbackMap_23` be a clean term-mode definition (no `rw`). -/
structure CosimplicialRing where
  R₁ : Type*
  R₂ : Type*
  R₃ : Type*
  [instR₁ : CommRing R₁]
  [instR₂ : CommRing R₂]
  [instR₃ : CommRing R₃]
  /-- Face maps R₁ → R₂ -/
  π₁ : R₁ →+* R₂
  π₂ : R₁ →+* R₂
  /-- Face maps R₂ → R₃ -/
  π₁₂ : R₂ →+* R₃
  π₁₃ : R₂ →+* R₃
  π₂₃ : R₂ →+* R₃
  /-- ρ₁ has two equivalent expressions; this is the one not picked as the def. -/
  π₁₃_π₁_eq_π₁₂_π₁ : π₁₃.comp π₁ = π₁₂.comp π₁
  /-- ρ₂ has two equivalent expressions; this is the one not picked as the def. -/
  π₁₂_π₂_eq_π₂₃_π₁ : π₁₂.comp π₂ = π₂₃.comp π₁
  /-- ρ₃ has two equivalent expressions; this is the one not picked as the def. -/
  π₁₃_π₂_eq_π₂₃_π₂ : π₁₃.comp π₂ = π₂₃.comp π₂

variable (C : CosimplicialRing)

-- Export the instances
attribute [instance] CosimplicialRing.instR₁ CosimplicialRing.instR₂ CosimplicialRing.instR₃

/-- The composite `R₁ → R₂ → R₃` along `π₁` then `π₁₂`. -/
def CosimplicialRing.ρ₁ (C : CosimplicialRing) : C.R₁ →+* C.R₃ := C.π₁₂.comp C.π₁
/-- The composite `R₁ → R₂ → R₃` along `π₁` then `π₂₃`. -/
def CosimplicialRing.ρ₂ (C : CosimplicialRing) : C.R₁ →+* C.R₃ := C.π₂₃.comp C.π₁
/-- The composite `R₁ → R₂ → R₃` along `π₂` then `π₂₃`. -/
def CosimplicialRing.ρ₃ (C : CosimplicialRing) : C.R₁ →+* C.R₃ := C.π₂₃.comp C.π₂

lemma CosimplicialRing.ρ₁_eq_π₁₂_π₁ : C.ρ₁ = C.π₁₂.comp C.π₁ := rfl
lemma CosimplicialRing.ρ₁_eq_π₁₃_π₁ : C.ρ₁ = C.π₁₃.comp C.π₁ := C.π₁₃_π₁_eq_π₁₂_π₁.symm
lemma CosimplicialRing.ρ₂_eq_π₂₃_π₁ : C.ρ₂ = C.π₂₃.comp C.π₁ := rfl
lemma CosimplicialRing.ρ₂_eq_π₁₂_π₂ : C.ρ₂ = C.π₁₂.comp C.π₂ := C.π₁₂_π₂_eq_π₂₃_π₁.symm
lemma CosimplicialRing.ρ₃_eq_π₂₃_π₂ : C.ρ₃ = C.π₂₃.comp C.π₂ := rfl
lemma CosimplicialRing.ρ₃_eq_π₁₃_π₂ : C.ρ₃ = C.π₁₃.comp C.π₂ := C.π₁₃_π₂_eq_π₂₃_π₂.symm

/-! ### Pullback (base change) types

Each ring homomorphism `f : R →+* S` induces an algebra structure and hence a
pullback operation `M ↦ S ⊗_{R, f} M`.  We define a family of reducible aliases
for the pullbacks along the face maps. -/

/-- Pullback along `π₁`. -/
@[reducible]
def π₁s (M : Type*) [AddCommGroup M] [Module C.R₁ M] : Type _ :=
  baseChange_along C.π₁ M

/-- Pullback along `π₂`. -/
@[reducible]
def π₂s (M : Type*) [AddCommGroup M] [Module C.R₁ M] : Type _ :=
  baseChange_along C.π₂ M

/-- Pullback along `ρ₁`. -/
@[reducible]
def ρ₁s (M : Type*) [AddCommGroup M] [Module C.R₁ M] : Type _ :=
  baseChange_along C.ρ₁ M

/-- Pullback along `ρ₂`. -/
@[reducible]
def ρ₂s (M : Type*) [AddCommGroup M] [Module C.R₁ M] : Type _ :=
  baseChange_along C.ρ₂ M

/-- Pullback along `ρ₃`. -/
@[reducible]
def ρ₃s (M : Type*) [AddCommGroup M] [Module C.R₁ M] : Type _ :=
  baseChange_along C.ρ₃ M

/-! ### Abstract pullback along a ring map

Given ring homomorphisms `f₁ f₂ : R₁ →+* R₂` and `g : R₂ →+* R₃`, with
composites `h₁ = g.comp f₁` and `h₂ = g.comp f₂`, an `R₂`-linear equivalence

  `φ : R₂ ⊗[R₁, f₁] M₁ ≃ R₂ ⊗[R₁, f₂] M₂`

base-changes along `g` to an `R₃`-linear equivalence

  `R₃ ⊗[R₁, h₁] M₁ ≃ R₃ ⊗[R₁, h₂] M₂`.

This subsumes `pullbackMap_12`, `pullbackMap_13`, `pullbackMap_23`. -/

section AbstractPullback

variable {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂]

variable {R₃ : Type*} [CommRing R₃]

/-- Abstract pullback of a base-change equivalence along `g`. Given
`φ : R₂ ⊗[R₁,f₁] M₁ ≃ R₂ ⊗[R₁,f₂] M₂`, produces
`R₃ ⊗[R₁,h₁] M₁ ≃ R₃ ⊗[R₁,h₂] M₂` where `h₁ = g.comp f₁` and `h₂ = g.comp f₂`
(or propositionally equal ring homs via `hh₁`, `hh₂`). -/
noncomputable def pullbackMap (f₁ f₂ : R₁ →+* R₂) (g : R₂ →+* R₃)
    {h₁ h₂ : R₁ →+* R₃} (hh₁ : g.comp f₁ = h₁) (hh₂ : g.comp f₂ = h₂)
    (M₁ : Type*) [AddCommGroup M₁] [Module R₁ M₁]
    (M₂ : Type*) [AddCommGroup M₂] [Module R₁ M₂]
    (φ : baseChange_along f₁ M₁ ≃ₗ[R₂] baseChange_along f₂ M₂) :
    baseChange_along h₁ M₁ ≃ₗ[R₃] baseChange_along h₂ M₂ := by
  subst hh₁; subst hh₂
  exact
    letI : Algebra R₂ R₃ := g.toAlgebra
    (Novikov.Miscellany.baseChange_assoc f₁ g M₁).symm.trans
      ((LinearEquiv.baseChange R₂ R₃ (baseChange_along f₁ M₁) (baseChange_along f₂ M₂) φ).trans
        (Novikov.Miscellany.baseChange_assoc f₂ g M₂))

lemma pullbackMap_tmul_eq_tmul (f₁ f₂ : R₁ →+* R₂) (g : R₂ →+* R₃)
    {h₁ : R₁ →+* R₃} (hh₁ : g.comp f₁ = h₁)
    {h₂ : R₁ →+* R₃} (hh₂ : g.comp f₂ = h₂)
    (M₁ M₂ : Type*) [AddCommGroup M₁] [Module R₁ M₁] [AddCommGroup M₂] [Module R₁ M₂]
    (φ : baseChange_along f₁ M₁ ≃ₗ[R₂] baseChange_along f₂ M₂)
    (r : R₃) (m : M₁) (r' : R₃) (m' : M₂)
    (h : (pullbackMap f₁ f₂ g rfl rfl M₁ M₂ φ)
          (letI : Algebra R₁ R₃ := (g.comp f₁).toAlgebra; r ⊗ₜ[R₁] m) =
        (letI : Algebra R₁ R₃ := (g.comp f₂).toAlgebra; r' ⊗ₜ[R₁] m')) :
    pullbackMap f₁ f₂ g hh₁ hh₂ M₁ M₂ φ
      (letI : Algebra R₁ R₃ := h₁.toAlgebra; r ⊗ₜ[R₁] m) =
      (letI : Algebra R₁ R₃ := h₂.toAlgebra; r' ⊗ₜ[R₁] m') := by
  subst hh₁ hh₂
  exact h

/-- Conjugation of base-change equivs on the internal Hom: given
`φ_M : R₂ ⊗[R₁,f₁] M ≃ R₂ ⊗[R₁,f₂] M` and `φ_N : R₂ ⊗[R₁,f₁] N ≃ R₂ ⊗[R₁,f₂] N`,
the map `u ↦ φ_N ∘ u ∘ φ_M⁻¹` transported through `homBaseChangeEquiv`. -/
noncomputable def homConj (f₁ f₂ : R₁ →+* R₂)
    (M N : Type*) [AddCommGroup M] [Module R₁ M]
    [Module.Finite R₁ M] [Module.Projective R₁ M]
    [AddCommGroup N] [Module R₁ N]
    [Module.Finite R₁ N] [Module.Projective R₁ N]
    (φM : baseChange_along f₁ M ≃ₗ[R₂] baseChange_along f₂ M)
    (φN : baseChange_along f₁ N ≃ₗ[R₂] baseChange_along f₂ N) :
    baseChange_along f₁ (M →ₗ[R₁] N) ≃ₗ[R₂] baseChange_along f₂ (M →ₗ[R₁] N) :=
  let H1 : baseChange_along f₁ (M →ₗ[R₁] N) ≃ₗ[R₂]
           (baseChange_along f₁ M →ₗ[R₂] baseChange_along f₁ N) :=
    letI : Algebra R₁ R₂ := f₁.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := R₁) R₂
  let H2 : baseChange_along f₂ (M →ₗ[R₁] N) ≃ₗ[R₂]
           (baseChange_along f₂ M →ₗ[R₂] baseChange_along f₂ N) :=
    letI : Algebra R₁ R₂ := f₂.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := R₁) R₂
  H1.trans ((φM.arrowCongr φN).trans H2.symm)

/-- Naturality helper: `homBaseChangeEquiv` at the composed algebra
`(g ∘ f)`, applied to a `baseChange_assoc`-image of `r ⊗ v`, agrees with
`r • s ⊗ (H_f v)(1 ⊗ m)` after applying to a tensor `(s, m)`. -/
private lemma homBaseChangeEquiv_baseChange_assoc_apply_tmul
    (f : R₁ →+* R₂) (g : R₂ →+* R₃)
    (M N : Type*) [AddCommGroup M] [Module R₁ M]
    [Module.Finite R₁ M] [Module.Projective R₁ M]
    [AddCommGroup N] [Module R₁ N]
    [Module.Finite R₁ N] [Module.Projective R₁ N]
    (r s : R₃) (m : M)
    (v : letI : Algebra R₁ R₂ := f.toAlgebra
         R₂ ⊗[R₁] (M →ₗ[R₁] N)) :
    letI : Algebra R₁ R₂ := f.toAlgebra
    letI : Algebra R₂ R₃ := g.toAlgebra
    letI : Algebra R₁ R₃ := (g.comp f).toAlgebra
    ((Novikov.Miscellany.homBaseChangeEquiv (R := R₁) (M := M) (N := N) R₃)
      ((Novikov.Miscellany.baseChange_assoc f g (M →ₗ[R₁] N))
        (r ⊗ₜ[R₂] v))) (s ⊗ₜ[R₁] m) =
    r • ((Novikov.Miscellany.baseChange_assoc f g N)
      (s ⊗ₜ[R₂] ((Novikov.Miscellany.homBaseChangeEquiv (R := R₁) (M := M) (N := N) R₂) v
        (1 ⊗ₜ[R₁] m)))) := by
  letI : Algebra R₁ R₂ := f.toAlgebra
  letI : Algebra R₂ R₃ := g.toAlgebra
  letI : Algebra R₁ R₃ := (g.comp f).toAlgebra
  haveI : IsScalarTower R₁ R₂ R₃ :=
    IsScalarTower.of_algebraMap_eq (R := R₁) (S := R₂) (A := R₃) (fun _ => rfl)
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp
  · intro a u
    simp only [Novikov.Miscellany.baseChange_assoc_tmul,
               Novikov.Miscellany.homBaseChangeEquiv_tmul,
               LinearMap.smul_apply, LinearMap.baseChange_tmul,
               TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    -- Goal: (a • r * s) ⊗ u m = (r * a • s) ⊗ u m
    congr 1
    simp [Algebra.smul_def, mul_comm, mul_left_comm]
  · intro v1 v2 h1 h2
    simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, smul_add]
    rw [h1, h2]

/-- The conjugation lemma: pulling back `homConj φ_M φ_N` along `g` and
applying `homBaseChangeEquiv` at the `h₂`-algebra equals the conjugation
of the level-3 base-change of `x` by the pullbacks of `φ_M` and `φ_N`.
Here `h₁` and `h₂` are ring homs propositionally equal to `g.comp f₁` and `g.comp f₂`. -/
lemma conj_lemma (f₁ f₂ : R₁ →+* R₂) (g : R₂ →+* R₃)
    {h₁ h₂ : R₁ →+* R₃} (hh₁ : g.comp f₁ = h₁) (hh₂ : g.comp f₂ = h₂)
    (M N : Type*) [AddCommGroup M] [Module R₁ M]
    [Module.Finite R₁ M] [Module.Projective R₁ M]
    [AddCommGroup N] [Module R₁ N]
    [Module.Finite R₁ N] [Module.Projective R₁ N]
    (φM : baseChange_along f₁ M ≃ₗ[R₂] baseChange_along f₂ M)
    (φN : baseChange_along f₁ N ≃ₗ[R₂] baseChange_along f₂ N)
    (x : baseChange_along h₁ (M →ₗ[R₁] N)) :
    (letI : Algebra R₁ R₃ := h₂.toAlgebra
     Novikov.Miscellany.homBaseChangeEquiv (R := R₁) (M := M) (N := N) R₃)
        (pullbackMap f₁ f₂ g hh₁ hh₂ (M →ₗ[R₁] N) (M →ₗ[R₁] N)
          (homConj f₁ f₂ M N φM φN) x) =
      (pullbackMap f₁ f₂ g hh₁ hh₂ N N φN).toLinearMap ∘ₗ
        ((letI : Algebra R₁ R₃ := h₁.toAlgebra
          Novikov.Miscellany.homBaseChangeEquiv (R := R₁) (M := M) (N := N) R₃) x) ∘ₗ
        (pullbackMap f₁ f₂ g hh₁ hh₂ M M φM).symm.toLinearMap := by
  subst hh₁; subst hh₂
  letI : Algebra R₁ R₃ := (g.comp f₁).toAlgebra
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r f
    letI A2 : Algebra R₁ R₃ := (g.comp f₂).toAlgebra
    apply LinearMap.ext
    intro y
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp
    · intro s m
      -- Reduce both sides to a common form using the naturality helper and
      -- `baseChange_assoc_naturality`.
      simp only [pullbackMap, homConj, LinearEquiv.trans_apply,
                LinearEquiv.coe_coe, LinearMap.coe_comp,
                Function.comp_apply, baseChange_assoc_symm_tmul,
                LinearEquiv.baseChange_tmul, homBaseChangeEquiv_tmul]
      -- LHS: apply naturality helper.
      rw [homBaseChangeEquiv_baseChange_assoc_apply_tmul,
          LinearEquiv.apply_symm_apply]
      -- LHS = r • baseChange_assoc f₂ g N (s ⊗ L(1 ⊗ m)) where L is the conj
      -- RHS: simplify via baseChange_assoc_naturality.
      have hnat := Novikov.Miscellany.baseChange_assoc_naturality
        (M := M) (N := N) f₁ g f
      have hnat_apply := congrFun (congrArg DFunLike.coe hnat)
        ((letI : Algebra R₁ R₂ := f₁.toAlgebra
          letI : Algebra R₂ R₃ := g.toAlgebra
          s ⊗ₜ[R₂] φM.symm (letI : Algebra R₁ R₂ := f₂.toAlgebra; 1 ⊗ₜ[R₁] m)))
      simp only [LinearMap.coe_comp, Function.comp_apply,
                LinearEquiv.coe_coe] at hnat_apply
      dsimp
      simp only [baseChange_assoc_symm_tmul, ← LinearEquiv.baseChange_symm, LinearEquiv.baseChange_tmul]
      rw [hnat_apply]
      simp
    · intro a b ha hb
      simp only [map_add]
      rw [ha, hb]
  · intro x y hx hy
    simp only [map_add, LinearMap.add_comp, LinearMap.comp_add]
    rw [hx, hy]

end AbstractPullback

/-! ### Pullback of a linear equivalence

Given `φ : π₁^* M ≃ π₂^* M`, we can pull it back along a face map
`h : R₂ →+* R₃` to obtain `ρ_a^* M ≃ ρ_b^* M`.  These are concrete
instances of the abstract `pullbackMap` above, specialised so that the
codomain composition matches the chosen definition of `ρ₂`/`ρ₃`. -/

/-- Pullback of `φ` along `π₁₂`, giving `ρ₁^* M ≃ ρ₂^* M`.

Instance of `pullbackMap` with `(g, f₁, f₂) = (π₁₂, π₁, π₂)`,
codomains `(h₁, h₂) = (ρ₁, ρ₂)`, and propositional witnesses
`ρ₁_eq_π₁₂_π₁.symm` (definitional `rfl`) and `ρ₂_eq_π₁₂_π₂.symm`. -/
noncomputable def pullbackMap_12 (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (φ : π₁s C M ≃ₗ[C.R₂] π₂s C M) :
    ρ₁s C M ≃ₗ[C.R₃] ρ₂s C M :=
  Novikov.Descent.Abstract.pullbackMap C.π₁ C.π₂ C.π₁₂
    C.ρ₁_eq_π₁₂_π₁.symm C.ρ₂_eq_π₁₂_π₂.symm M M φ

/-- Pullback of `φ` along `π₁₃`, giving `ρ₁^* M ≃ ρ₃^* M`.

Instance of `pullbackMap` with `(g, f₁, f₂) = (π₁₃, π₁, π₂)`,
codomains `(h₁, h₂) = (ρ₁, ρ₃)`, and propositional witnesses
`ρ₁_eq_π₁₃_π₁.symm` and `ρ₃_eq_π₁₃_π₂.symm`. -/
noncomputable def pullbackMap_13 (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (φ : π₁s C M ≃ₗ[C.R₂] π₂s C M) :
    ρ₁s C M ≃ₗ[C.R₃] ρ₃s C M :=
  Novikov.Descent.Abstract.pullbackMap C.π₁ C.π₂ C.π₁₃
    C.ρ₁_eq_π₁₃_π₁.symm C.ρ₃_eq_π₁₃_π₂.symm M M φ

/-- Pullback of `φ` along `π₂₃`, giving `ρ₂^* M ≃ ρ₃^* M`.

Instance of `pullbackMap`; the witnesses are both `rfl` since
`ρ₂ = π₂₃.comp π₁` and `ρ₃ = π₂₃.comp π₂` are definitional. -/
noncomputable def pullbackMap_23 (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (φ : π₁s C M ≃ₗ[C.R₂] π₂s C M) :
    ρ₂s C M ≃ₗ[C.R₃] ρ₃s C M :=
  Novikov.Descent.Abstract.pullbackMap C.π₁ C.π₂ C.π₂₃ rfl rfl M M φ

/-! ### Descent datum -/

/-- A descent datum for a cosimplicial ring `C` consists of a finite projective
`R₁`-module `M` and an `R₂`-linear isomorphism `φ : π₁^* M ≃ π₂^* M`
satisfying the cocycle condition. -/
structure DescentDatum where
  M : Type*
  [instAddCommGroup : AddCommGroup M]
  [instModule : Module C.R₁ M]
  [instFinite : Module.Finite C.R₁ M]
  [instProjective : Module.Projective C.R₁ M]
  /-- The cocycle isomorphism `π₁^* M ≃ π₂^* M`. -/
  φ : π₁s C M ≃ₗ[C.R₂] π₂s C M
  /-- The cocycle condition. -/
  cocycle :
    (pullbackMap_23 C M φ).toLinearMap ∘ (pullbackMap_12 C M φ).toLinearMap =
    (pullbackMap_13 C M φ).toLinearMap

attribute [instance] DescentDatum.instAddCommGroup DescentDatum.instModule
  DescentDatum.instFinite DescentDatum.instProjective

section Category

variable {C : CosimplicialRing}

/-- A morphism of descent data is an `R₁`-linear map whose base changes
along `π₁` and `π₂` commute with `φ`. -/
structure DescentDatum.Hom (M N : DescentDatum C) where
  toLinearMap : M.M →ₗ[C.R₁] N.M
  commute_φ :
    N.φ.toLinearMap ∘ₗ
        (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
         LinearMap.baseChange C.R₂ toLinearMap) =
      (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
       LinearMap.baseChange C.R₂ toLinearMap) ∘ₗ M.φ.toLinearMap

namespace DescentDatum

@[ext]
lemma hom_ext {M N : DescentDatum C} (f g : Hom M N)
    (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f; cases g; congr

/-- The category of descent data. -/
noncomputable instance : Category (DescentDatum C) where
  Hom := Hom
  id M := {
    toLinearMap := LinearMap.id
    commute_φ := by
      letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
      letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
      simp [LinearMap.baseChange_id]
  }
  comp f g := {
    toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
    commute_φ := by
      letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
      letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
      simp only [LinearMap.baseChange_comp]
      rw [← LinearMap.comp_assoc, g.commute_φ, LinearMap.comp_assoc,
          f.commute_φ, ← LinearMap.comp_assoc]
  }
  id_comp f := by ext; rfl
  comp_id f := by ext; rfl
  assoc f g h := by ext; rfl

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
noncomputable def isoOfLinearEquiv {M N : DescentDatum C}
    (f : M ⟶ N) (e : M.M ≃ₗ[C.R₁] N.M)
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

/-- The cocycle identity dualised: pulling back the inverse of `φ` along
`π₁₂.symm` and `π₂₃.symm` agrees with pulling back along `π₁₃.symm`. -/
lemma cocycle_symm (M : DescentDatum C) (y : ρ₃s C M.M) :
    (pullbackMap_12 C M.M M.φ).symm ((pullbackMap_23 C M.M M.φ).symm y) =
    (pullbackMap_13 C M.M M.φ).symm y := by
  have hM := M.cocycle
  have hM_y := congrFun hM
  simp only [Function.comp_apply, LinearEquiv.coe_coe] at hM_y
  apply (pullbackMap_13 C M.M M.φ).injective
  rw [(pullbackMap_13 C M.M M.φ).apply_symm_apply, ← hM_y,
      (pullbackMap_12 C M.M M.φ).apply_symm_apply,
      (pullbackMap_23 C M.M M.φ).apply_symm_apply]

/-- The internal Hom of two descent data.
As an underlying module it is the `R₁`-linear maps, and `φ` is conjugation
by `M.φ` and `N.φ` after identifying base change of Hom with Hom of base changes. -/
noncomputable def internalHom (M N : DescentDatum C) : DescentDatum C :=
  letI : AddCommGroup M.M := M.instAddCommGroup
  letI : Module C.R₁ M.M := M.instModule
  letI : Module.Finite C.R₁ M.M := M.instFinite
  letI : Module.Projective C.R₁ M.M := M.instProjective
  letI : AddCommGroup N.M := N.instAddCommGroup
  letI : Module C.R₁ N.M := N.instModule
  letI : Module.Finite C.R₁ N.M := N.instFinite
  letI : Module.Projective C.R₁ N.M := N.instProjective
  { M := M.M →ₗ[C.R₁] N.M
    instFinite := inferInstance
    instProjective := inferInstance
    φ := Novikov.Descent.Abstract.homConj C.π₁ C.π₂ M.M N.M M.φ N.φ
    cocycle := by
      -- Setup: φ' for the internal Hom, and H₂/H₃ using ρ₂/ρ₃ algebras
      let φ' := Novikov.Descent.Abstract.homConj C.π₁ C.π₂ M.M N.M M.φ N.φ
      let H₂ :=
        letI : Algebra C.R₁ C.R₃ := C.ρ₂.toAlgebra
        Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁)
          (M := M.M) (N := N.M) C.R₃
      let H₃ :=
        letI : Algebra C.R₁ C.R₃ := C.ρ₃.toAlgebra
        Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁)
          (M := M.M) (N := N.M) C.R₃
      -- Key conjugation lemma for the 23 case. Direct instance of the
      -- abstract `Novikov.Descent.Abstract.conj_lemma` at `(π₁, π₂, π₂₃)`: the
      -- output types `ρ₂s/ρ₃s` are defeq to `baseChange_along (π₂₃∘π₁)/(π₂₃∘π₂)`
      -- since `ρ₂ = π₂₃.comp π₁` and `ρ₃ = π₂₃.comp π₂` by definition.
      have conj_lemma (x : ρ₂s C (M.M →ₗ[C.R₁] N.M)) :
          H₃ (pullbackMap_23 C (M.M →ₗ[C.R₁] N.M) φ' x) =
          (pullbackMap_23 C N.M N.φ).toLinearMap ∘ₗ H₂ x ∘ₗ
            (pullbackMap_23 C M.M M.φ).symm.toLinearMap :=
        Novikov.Descent.Abstract.conj_lemma C.π₁ C.π₂ C.π₂₃ rfl rfl M.M N.M M.φ N.φ x
      -- Conjugation lemma for π₁₂.  Direct instance of `conj_lemma` at
      -- `(π₁, π₂, π₁₂)` with codomain compositions `h₁ = ρ₁`, `h₂ = ρ₂`
      -- and propositional witnesses from the cosimplicial structure.
      -- Since `pullbackMap_12 = pullbackMap` by definition, this matches.
      have conj_lemma_12 (x : ρ₁s C (M.M →ₗ[C.R₁] N.M)) :
          H₂ (pullbackMap_12 C (M.M →ₗ[C.R₁] N.M) φ' x) =
          (pullbackMap_12 C N.M N.φ).toLinearMap ∘ₗ
            (letI : Algebra C.R₁ C.R₃ := C.ρ₁.toAlgebra
             Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁)
               (M := M.M) (N := N.M) C.R₃) x ∘ₗ
            (pullbackMap_12 C M.M M.φ).symm.toLinearMap :=
        Novikov.Descent.Abstract.conj_lemma C.π₁ C.π₂ C.π₁₂
          C.ρ₁_eq_π₁₂_π₁.symm C.ρ₂_eq_π₁₂_π₂.symm M.M N.M M.φ N.φ x
      -- Conjugation lemma for π₁₃.  Direct instance of `conj_lemma` at
      -- `(π₁, π₂, π₁₃)` with codomain compositions `h₁ = ρ₁`, `h₂ = ρ₃`.
      have conj_lemma_13 (x : ρ₁s C (M.M →ₗ[C.R₁] N.M)) :
          H₃ (pullbackMap_13 C (M.M →ₗ[C.R₁] N.M) φ' x) =
          (pullbackMap_13 C N.M N.φ).toLinearMap ∘ₗ
            (letI : Algebra C.R₁ C.R₃ := C.ρ₁.toAlgebra
             Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁)
               (M := M.M) (N := N.M) C.R₃) x ∘ₗ
            (pullbackMap_13 C M.M M.φ).symm.toLinearMap :=
        Novikov.Descent.Abstract.conj_lemma C.π₁ C.π₂ C.π₁₃
          C.ρ₁_eq_π₁₃_π₁.symm C.ρ₃_eq_π₁₃_π₂.symm M.M N.M M.φ N.φ x
      -- N's cocycle (M's is folded into `cocycle_symm`).
      have hN := N.cocycle
      -- The chase: cancel H₃ (injective), apply the three conj_lemmas and the
      -- M/N cocycles.
      funext x
      apply H₃.injective
      simp only [Function.comp_apply, LinearEquiv.coe_coe]
      rw [conj_lemma ((pullbackMap_12 C (M.M →ₗ[C.R₁] N.M) φ') x), conj_lemma_12 x,
          conj_lemma_13 x]
      apply LinearMap.ext
      intro y
      simp only [LinearMap.comp_apply]
      have hN_y := congrFun hN
      simp only [Function.comp_apply] at hN_y
      rw [hN_y]
      simp only [LinearEquiv.coe_coe]
      rw [cocycle_symm M y]
  }

lemma hom_iff_eq_φ {M N : DescentDatum C} (f : M.M →ₗ[C.R₁] N.M) :
    N.φ.toLinearMap ∘ₗ
        (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
         LinearMap.baseChange C.R₂ f) =
      (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
       LinearMap.baseChange C.R₂ f) ∘ₗ M.φ.toLinearMap ↔
    (DescentDatum.internalHom M N).φ (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] f) =
      (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] f) := by
  let F1 := letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; LinearMap.baseChange C.R₂ f
  let F2 := letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra; LinearMap.baseChange C.R₂ f
  let H1 :=
    letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M) (N := N.M) C.R₂
  let H2 :=
    letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
    Novikov.Miscellany.homBaseChangeEquiv (R := C.R₁) (M := M.M) (N := N.M) C.R₂
  let conj :
      (baseChange_along C.π₁ M.M →ₗ[C.R₂] baseChange_along C.π₁ N.M) ≃ₗ[C.R₂]
      (baseChange_along C.π₂ M.M →ₗ[C.R₂] baseChange_along C.π₂ N.M) :=
    { toFun := fun u => N.φ.toLinearMap ∘ₗ u ∘ₗ M.φ.symm.toLinearMap
      invFun := fun u => N.φ.symm.toLinearMap ∘ₗ u ∘ₗ M.φ.toLinearMap
      left_inv := by intro u; ext x; simp
      right_inv := by intro u; ext x; simp
      map_add' := by intro u v; ext x; simp [LinearMap.add_comp, LinearMap.comp_add]
      map_smul' := by intro r u; ext x; simp [LinearMap.smul_apply, LinearMap.comp_apply] }
  have h_internal_phi : (DescentDatum.internalHom M N).φ =
      H1.trans (conj.trans H2.symm) := rfl
  have h_H1 : H1 ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] f)) = F1 := by
    dsimp [H1, F1]; rw [Novikov.Miscellany.homBaseChangeEquiv_tmul]; simp only [one_smul]
  have h_H2 : H2 ((letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] f)) = F2 := by
    dsimp [H2, F2]; rw [Novikov.Miscellany.homBaseChangeEquiv_tmul]; simp only [one_smul]
  change N.φ.toLinearMap ∘ₗ F1 = F2 ∘ₗ M.φ.toLinearMap ↔
    (DescentDatum.internalHom M N).φ ((letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] f)) =
      ((letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] f))
  constructor
  · intro h
    rw [h_internal_phi]
    change H2.symm (conj (H1 (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] f))) = (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] f)
    rw [h_H1, LinearEquiv.symm_apply_eq, h_H2]
    apply LinearMap.ext
    intro x
    have h_eval := LinearMap.congr_fun h (M.φ.symm x)
    change N.φ.toLinearMap (F1 (M.φ.symm x)) = F2 (M.φ.toLinearMap (M.φ.symm x)) at h_eval
    have h_M : M.φ.toLinearMap (M.φ.symm x) = x := M.φ.apply_symm_apply x
    rw [h_M] at h_eval
    exact h_eval
  · intro h
    rw [h_internal_phi] at h
    change H2.symm (conj (H1 (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] f))) = (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra; (1 : C.R₂) ⊗ₜ[C.R₁] f) at h
    rw [h_H1, LinearEquiv.symm_apply_eq, h_H2] at h
    apply LinearMap.ext
    intro x
    have h_eval := LinearMap.congr_fun h (M.φ x)
    change N.φ.toLinearMap (F1 (M.φ.symm.toLinearMap (M.φ x))) = F2 (M.φ.toLinearMap x) at h_eval
    have h_M : M.φ.symm.toLinearMap (M.φ x) = x := M.φ.symm_apply_apply x
    rw [h_M] at h_eval
    exact h_eval

end DescentDatum

end Category

end Novikov.Descent.Abstract
