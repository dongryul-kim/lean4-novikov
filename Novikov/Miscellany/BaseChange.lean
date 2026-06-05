import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

open LinearMap TensorProduct

namespace Novikov.Miscellany

section BaseChange

variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

/-- Base change of `M` along a ring homomorphism `f : A →+* B`, with the algebra
structure on `B` taken from `f`. -/
@[reducible]
def baseChange_along (f : A →+* B) (M : Type*) [AddCommGroup M] [Module A M] : Type _ :=
  letI : Algebra A B := f.toAlgebra
  B ⊗[A] M

/-- Base change of a linear map along a ring homomorphism, with the algebra
structure on the target ring taken from the ring homomorphism. -/
noncomputable def baseChangeMap (f : A →+* B) {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (φ : M →ₗ[A] N) :
    letI : Algebra A B := f.toAlgebra; (B ⊗[A] M) →ₗ[B] (B ⊗[A] N) := by
  letI : Algebra A B := f.toAlgebra
  exact LinearMap.baseChange B φ

@[simp]
theorem baseChangeMap_tmul (f : A →+* B) {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (φ : M →ₗ[A] N) (b : B) (m : M) :
    baseChangeMap f (M := M) (N := N) φ (letI : Algebra A B := f.toAlgebra; b ⊗ₜ[A] m) =
      (letI : Algebra A B := f.toAlgebra; b ⊗ₜ[A] (φ m)) := by
  letI : Algebra A B := f.toAlgebra
  exact LinearMap.baseChange_tmul φ b m

/-- Associativity of iterated base change: `C ⊗[B] (B ⊗[A] M) ≃ C ⊗[A] M`. -/
noncomputable def baseChange_assoc (f : A →+* B) (g : B →+* C)
    (M : Type*) [AddCommGroup M] [Module A M] :
    letI : Algebra A B := f.toAlgebra;
    letI : Algebra B C := g.toAlgebra;
    letI : Algebra A C := (g.comp f).toAlgebra;
    (C ⊗[B] (B ⊗[A] M)) ≃ₗ[C] (C ⊗[A] M) := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B C := g.toAlgebra
  letI : Algebra A C := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := by
    apply IsScalarTower.of_algebraMap_eq (R := A) (S := B) (A := C)
    intro x; rfl
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M

/-- Pure-tensor formula for `baseChange_assoc`. -/
@[simp]
theorem baseChange_assoc_tmul (f : A →+* B) (g : B →+* C)
    {M : Type*} [AddCommGroup M] [Module A M] (c : C) (b : B) (m : M) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra B C := g.toAlgebra
    letI : Algebra A C := (g.comp f).toAlgebra
    baseChange_assoc f g M (c ⊗ₜ[B] (b ⊗ₜ[A] m)) = (b • c) ⊗ₜ[A] m := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B C := g.toAlgebra
  letI : Algebra A C := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := B) (A := C) (fun _ => rfl)
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul A B C c m b

/-- Moving a scalar on the outer tensor factor through the associativity
comparison for iterated base change. -/
lemma cancelBaseChange_tmul_left {R A B M : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [AddCommGroup M] [Module R M]
    (b : B) (x : A ⊗[R] M) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M)
      (b ⊗ₜ[A] x) =
    b • (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M)
      ((1 : B) ⊗ₜ[A] x) := by
  have h : (b ⊗ₜ[A] x : B ⊗[A] (A ⊗[R] M)) =
      b • ((1 : B) ⊗ₜ[A] x) := by
    rw [TensorProduct.smul_tmul']
    simp
  rw [h]
  rw [map_smul]

/-- Pure-tensor formula for `baseChange_assoc.symm`. -/
@[simp]
theorem baseChange_assoc_symm_tmul (f : A →+* B) (g : B →+* C)
    {M : Type*} [AddCommGroup M] [Module A M] (c : C) (m : M) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra B C := g.toAlgebra
    letI : Algebra A C := (g.comp f).toAlgebra
    (baseChange_assoc f g M).symm (c ⊗ₜ[A] m) = c ⊗ₜ[B] (1 ⊗ₜ[A] m) := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B C := g.toAlgebra
  letI : Algebra A C := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := B) (A := C) (fun _ => rfl)
  apply (baseChange_assoc f g M).injective
  rw [LinearEquiv.apply_symm_apply, baseChange_assoc_tmul, one_smul]

/-- `baseChange_assoc` viewed as an equivalence whose target is `baseChange_along ρ M`
for some ring hom `ρ` propositionally equal to `π.comp π₀`. -/
noncomputable def baseChange_assoc_eq
    {R₀ R₁ R₂ : Type*} [CommRing R₀] [CommRing R₁] [CommRing R₂]
    (π₀ : R₀ →+* R₁) (π : R₁ →+* R₂)
    {ρ : R₀ →+* R₂} (h : π.comp π₀ = ρ)
    (M : Type*) [AddCommGroup M] [Module R₀ M] :
    letI : Algebra R₀ R₁ := π₀.toAlgebra
    letI : Algebra R₁ R₂ := π.toAlgebra
    letI : Algebra R₀ R₂ := ρ.toAlgebra
    (R₂ ⊗[R₁] (R₁ ⊗[R₀] M)) ≃ₗ[R₂] (R₂ ⊗[R₀] M) := by
  subst h
  exact Novikov.Miscellany.baseChange_assoc π₀ π M

@[simp]
lemma baseChange_assoc_eq_tmul
    {R₀ R₁ R₂ : Type*} [CommRing R₀] [CommRing R₁] [CommRing R₂]
    (π₀ : R₀ →+* R₁) (π : R₁ →+* R₂)
    {ρ : R₀ →+* R₂} (h : π.comp π₀ = ρ)
    (M : Type*) [AddCommGroup M] [Module R₀ M]
    (c : R₂) (b : R₁) (m : M) :
    letI : Algebra R₀ R₁ := π₀.toAlgebra
    letI : Algebra R₁ R₂ := π.toAlgebra
    letI : Algebra R₀ R₂ := ρ.toAlgebra
    (baseChange_assoc_eq π₀ π h M) (c ⊗ₜ[R₁] (b ⊗ₜ[R₀] m)) = (b • c) ⊗ₜ[R₀] m := by
  subst h
  exact Novikov.Miscellany.baseChange_assoc_tmul π₀ π c b m

@[simp]
lemma baseChange_assoc_eq_symm_tmul
    {R₀ R₁ R₂ : Type*} [CommRing R₀] [CommRing R₁] [CommRing R₂]
    (π₀ : R₀ →+* R₁) (π : R₁ →+* R₂)
    {ρ : R₀ →+* R₂} (h : π.comp π₀ = ρ)
    (M : Type*) [AddCommGroup M] [Module R₀ M]
    (c : R₂) (m : M) :
    letI : Algebra R₀ R₁ := π₀.toAlgebra
    letI : Algebra R₁ R₂ := π.toAlgebra
    letI : Algebra R₀ R₂ := ρ.toAlgebra
    (baseChange_assoc_eq π₀ π h M).symm (c ⊗ₜ[R₀] m) = c ⊗ₜ[R₁] ((1 : R₁) ⊗ₜ[R₀] m) := by
  subst h
  exact Novikov.Miscellany.baseChange_assoc_symm_tmul π₀ π c m

/-- Naturality: `LinearMap.baseChange` commutes with `baseChange_assoc`. -/
theorem baseChange_assoc_naturality (f : A →+* B) (g : B →+* C)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (h : M →ₗ[A] N) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra B C := g.toAlgebra
    letI : Algebra A C := (g.comp f).toAlgebra
    (LinearMap.baseChange C h) ∘ₗ (baseChange_assoc f g M).toLinearMap =
      (baseChange_assoc f g N).toLinearMap ∘ₗ
        (LinearMap.baseChange C (LinearMap.baseChange B h)) := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B C := g.toAlgebra
  letI : Algebra A C := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := B) (A := C) (fun _ => rfl)
  apply TensorProduct.AlgebraTensorModule.ext
  intro c x
  refine TensorProduct.induction_on (motive := fun x =>
    (LinearMap.baseChange C h ∘ₗ (baseChange_assoc f g M).toLinearMap) (c ⊗ₜ[B] x) =
      ((baseChange_assoc f g N).toLinearMap ∘ₗ
        LinearMap.baseChange C (LinearMap.baseChange B h)) (c ⊗ₜ[B] x)) x ?_ ?_ ?_
  · simp
  · intro b m
    simp
  · intro x y hx hy
    simp only [TensorProduct.tmul_add, map_add, LinearMap.comp_apply] at hx hy ⊢
    rw [hx, hy]

section RingHomCongr

variable {R S : Type*} [CommRing R] [CommRing S]
variable {f g : R →+* S}

/-- Base-change modules along propositionally equal ring homomorphisms are
canonically linearly equivalent. -/
noncomputable def baseChangeCongrRingHom (h : f = g)
    (M : Type*) [AddCommGroup M] [Module R M] :
    baseChange_along f M ≃ₗ[S] baseChange_along g M := by
  subst h
  exact LinearEquiv.refl S _

@[simp]
lemma baseChangeCongrRingHom_refl
    (M : Type*) [AddCommGroup M] [Module R M] :
    baseChangeCongrRingHom (f := f) (g := f) rfl M =
      LinearEquiv.refl S (baseChange_along f M) := rfl

@[simp]
lemma baseChangeCongrRingHom_tmul (h : f = g)
    (M : Type*) [AddCommGroup M] [Module R M] (s : S) (m : M) :
    baseChangeCongrRingHom (f := f) (g := g) h M
      ((letI : Algebra R S := f.toAlgebra; s ⊗ₜ[R] m)) =
      (letI : Algebra R S := g.toAlgebra; s ⊗ₜ[R] m) := by
  subst h
  rfl

/-- `baseChange_assoc_eq` is `baseChange_assoc` followed by the canonical
congruence for the propositionally equal composite ring homomorphisms. -/
lemma baseChange_assoc_eq_apply_eq_congr
    {R₀ R₁ R₂ : Type*} [CommRing R₀] [CommRing R₁] [CommRing R₂]
    (π₀ : R₀ →+* R₁) (π : R₁ →+* R₂)
    {ρ : R₀ →+* R₂} (h : π.comp π₀ = ρ)
    (M : Type*) [AddCommGroup M] [Module R₀ M]
    (z : letI : Algebra R₀ R₁ := π₀.toAlgebra; letI : Algebra R₁ R₂ := π.toAlgebra;
      R₂ ⊗[R₁] (R₁ ⊗[R₀] M)) :
    letI : Algebra R₀ R₁ := π₀.toAlgebra
    letI : Algebra R₁ R₂ := π.toAlgebra
    letI : Algebra R₀ R₂ := ρ.toAlgebra
    (baseChange_assoc_eq π₀ π h M) z =
      (baseChangeCongrRingHom h M) ((baseChange_assoc π₀ π M) z) := by
  subst h
  rfl

/-- Naturality of `baseChangeCongrRingHom`: it commutes with base-changed maps. -/
lemma baseChangeCongrRingHom_naturality {R S : Type*} [CommRing R] [CommRing S]
    {f g : R →+* S} (h : f = g)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) :
    (baseChangeCongrRingHom h N).toLinearMap ∘ₗ baseChangeMap f φ =
      baseChangeMap g φ ∘ₗ (baseChangeCongrRingHom h M).toLinearMap := by
  subst h
  rfl

end RingHomCongr

/-- Naturality of `baseChange_assoc` in `baseChangeMap` form. -/
lemma baseChange_assoc_baseChangeMap_naturality (f : A →+* B) (g : B →+* C)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (φ : M →ₗ[A] N) :
    (baseChange_assoc f g N).toLinearMap ∘ₗ baseChangeMap g (baseChangeMap f φ) =
      baseChangeMap (g.comp f) φ ∘ₗ (baseChange_assoc f g M).toLinearMap :=
  (baseChange_assoc_naturality f g φ).symm

/-- Compare two ways of extending scalars around a commutative square of ring
homomorphisms. -/
noncomputable def baseChangeSquare (f : A →+* B) (f' : A →+* C)
    (g : B →+* D) (g' : C →+* D) (h : g.comp f = g'.comp f')
    (M : Type*) [AddCommGroup M] [Module A M] :
    baseChange_along g (baseChange_along f M) ≃ₗ[D]
      letI : Algebra C D := g'.toAlgebra
      D ⊗[C] baseChange_along f' M := by
  let e1 : baseChange_along g (baseChange_along f M) ≃ₗ[D]
      baseChange_along (g.comp f) M :=
    baseChange_assoc f g M
  let e2 : baseChange_along (g.comp f) M ≃ₗ[D]
      baseChange_along (g'.comp f') M :=
    baseChangeCongrRingHom h M
  let e3 : (letI : Algebra C D := g'.toAlgebra
      D ⊗[C] baseChange_along f' M) ≃ₗ[D]
      baseChange_along (g'.comp f') M :=
    baseChange_assoc f' g' M
  exact e1.trans (e2.trans e3.symm)

/-- Pure-tensor formula for `baseChangeSquare`. -/
@[simp]
theorem baseChangeSquare_tmul (f : A →+* B) (f' : A →+* C)
    (g : B →+* D) (g' : C →+* D) (h : g.comp f = g'.comp f')
    {M : Type*} [AddCommGroup M] [Module A M] (d : D) (b : B) (m : M) :
    baseChangeSquare f f' g g' h M
      ((letI : Algebra B D := g.toAlgebra
        letI : Algebra A B := f.toAlgebra
        d ⊗ₜ[B] (b ⊗ₜ[A] m))) =
      (letI : Algebra C D := g'.toAlgebra
       letI : Algebra A C := f'.toAlgebra
       letI : Algebra B D := g.toAlgebra
       (b • d) ⊗ₜ[C] ((1 : C) ⊗ₜ[A] m)) := by
  simp [baseChangeSquare]

/-- Pure-tensor formula for `baseChangeSquare.symm`. -/
@[simp]
theorem baseChangeSquare_symm_tmul (f : A →+* B) (f' : A →+* C)
    (g : B →+* D) (g' : C →+* D) (h : g.comp f = g'.comp f')
    {M : Type*} [AddCommGroup M] [Module A M] (d : D) (c : C) (m : M) :
    (baseChangeSquare f f' g g' h M).symm
      ((letI : Algebra C D := g'.toAlgebra
        letI : Algebra A C := f'.toAlgebra
        d ⊗ₜ[C] (c ⊗ₜ[A] m))) =
      (letI : Algebra C D := g'.toAlgebra
       letI : Algebra B D := g.toAlgebra
       letI : Algebra A B := f.toAlgebra
       (c • d) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] m)) := by
  letI : Algebra C D := g'.toAlgebra
  letI : Algebra A C := f'.toAlgebra
  rw [show d ⊗ₜ[C] (c ⊗ₜ[A] m) = (c • d) ⊗ₜ[C] ((1 : C) ⊗ₜ[A] m) from by
    rw [smul_tmul, smul_tmul', smul_eq_mul, mul_one]]
  apply (baseChangeSquare f f' g g' h M).injective
  rw [LinearEquiv.apply_symm_apply, baseChangeSquare_tmul]
  letI : Algebra B D := g.toAlgebra
  simp

/-- Naturality of `baseChangeSquare` with respect to maps of modules. -/
lemma baseChangeSquare_naturality (f : A →+* B) (f' : A →+* C)
    (g : B →+* D) (g' : C →+* D) (h : g.comp f = g'.comp f')
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (φ : M →ₗ[A] N) :
    (baseChangeSquare f f' g g' h N).toLinearMap ∘ₗ baseChangeMap g (baseChangeMap f φ) =
      baseChangeMap g' (baseChangeMap f' φ) ∘ₗ
        (baseChangeSquare f f' g g' h M).toLinearMap := by
  have nat1 := baseChange_assoc_baseChangeMap_naturality f g φ
  have nat3 := baseChange_assoc_baseChangeMap_naturality f' g' φ
  have nat2 := baseChangeCongrRingHom_naturality h φ
  have nat3' : (baseChange_assoc f' g' N).symm.toLinearMap ∘ₗ
        baseChangeMap (g'.comp f') φ =
      baseChangeMap g' (baseChangeMap f' φ) ∘ₗ
        (baseChange_assoc f' g' M).symm.toLinearMap := by
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    have hn := LinearMap.congr_fun nat3 ((baseChange_assoc f' g' M).symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hn
    exact hn.symm
  apply LinearMap.ext; intro x
  have h1 := LinearMap.congr_fun nat1 x
  have h2 := LinearMap.congr_fun nat2 ((baseChange_assoc f g M) x)
  have h3 := LinearMap.congr_fun nat3'
    ((baseChangeCongrRingHom h M) ((baseChange_assoc f g M) x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h1 h2 h3 ⊢
  simp only [baseChangeSquare, LinearEquiv.trans_apply]
  rw [h1, h2, h3]

/-- Tetrahedron coherence: three levels of base change assoc compose consistently.

Given ring maps `f : A → B`, `g : B → C`, `h : C → D` and an `A`-module `M`,
the two natural ways to go from `D ⊗[C] (C ⊗[B] (B ⊗[A] M))` to `D ⊗[A] M`
(inner assoc first vs outer assoc first) are equal. -/
theorem baseChange_assoc_tetrahedron (f : A →+* B) (g : B →+* C) (h : C →+* D)
    {M : Type*} [AddCommGroup M] [Module A M] :
    letI : Algebra A B := f.toAlgebra;
    letI : Algebra B C := g.toAlgebra;
    letI : Algebra C D := h.toAlgebra;
    letI : Algebra A C := (g.comp f).toAlgebra;
    letI : Algebra B D := (h.comp g).toAlgebra;
    letI : Algebra A D := (h.comp (g.comp f)).toAlgebra;
    (baseChange_assoc (g.comp f) h M).toLinearMap ∘ₗ
      (LinearEquiv.baseChange C D (C ⊗[B] (B ⊗[A] M)) (C ⊗[A] M)
        (baseChange_assoc f g M)).toLinearMap =
    (letI : Algebra A D := ((h.comp g).comp f).toAlgebra;
    (baseChange_assoc f (h.comp g) M).toLinearMap ∘ₗ
      (baseChange_assoc g h (B ⊗[A] M)).toLinearMap) := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B C := g.toAlgebra
  letI : Algebra C D := h.toAlgebra
  letI : Algebra A C := (g.comp f).toAlgebra
  letI : Algebra B D := (h.comp g).toAlgebra
  letI : Algebra A D := (h.comp (g.comp f)).toAlgebra
  haveI : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := B) (A := C) (fun _ => rfl)
  haveI : IsScalarTower B C D :=
    IsScalarTower.of_algebraMap_eq (R := B) (S := C) (A := D) (fun _ => rfl)
  apply TensorProduct.AlgebraTensorModule.ext
  intro d y
  change (baseChange_assoc (g.comp f) h M)
      ((LinearEquiv.baseChange C D _ _ (baseChange_assoc f g M)) (d ⊗ₜ[C] y)) =
    (baseChange_assoc f (h.comp g) M) ((baseChange_assoc g h (B ⊗[A] M)) (d ⊗ₜ[C] y))
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · simp only [tmul_zero, map_zero]
  · intro c z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp only [tmul_zero, map_zero]
    · intro b m
      simp [smul_assoc]
    · intro z₁ z₂ hz₁ hz₂
      simp only [TensorProduct.tmul_add, map_add, hz₁, hz₂]
  · intro y₁ y₂ hy₁ hy₂
    simp only [TensorProduct.tmul_add, map_add, hy₁, hy₂]

end BaseChange

end Novikov.Miscellany
