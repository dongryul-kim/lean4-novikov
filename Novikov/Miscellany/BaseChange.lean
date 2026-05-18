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
    rfl
  · intro c z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp only [tmul_zero, map_zero]
      rfl
    · intro b m
      simp [smul_assoc]
      rfl
    · intro z₁ z₂ hz₁ hz₂
      simp only [TensorProduct.tmul_add, map_add, hz₁, hz₂]
      rfl
  · intro y₁ y₂ hy₁ hy₂
    simp only [TensorProduct.tmul_add, map_add, hy₁, hy₂]
    rfl

end BaseChange

end Novikov.Miscellany
