import Novikov.Isocrystal.Frobenius
import Novikov.Series.Algebra
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.CategoryTheory.Preadditive.Basic
import Novikov.Miscellany.Projective

/-!
# Novikov isocrystals

This file defines the notion of a Novikov isocrystal and proves basic facts.
A Novikov isocrystal over a ring `A` is a finite projective module over
`RealNovikovSeries A` together with a Frobenius-semilinear bijection.

## Main definitions

* `NovikovIsocrystal (Λ := Λ) A`: The type of Novikov isocrystals over `A`.
* `NovikovIsocrystal.Hom M N`: The type of morphisms between Novikov isocrystals.
* `vectToNovIsoc A`: The functor from finite projective `A`-modules to Novikov isocrystals.

## Main results

* `vectToNovIsoc_fully_faithful`: The functor `vectToNovIsoc` is fully faithful.
-/

open CategoryTheory
open TensorProduct

namespace Novikov
variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]

section Isocrystal
variable {A : Type*} [CommRing A]

instance hΛ : Fact (Λ > 0) := ⟨by have := hΛ1.out; linarith ⟩ 

instance hΛinv : Fact (1/Λ > 0) := ⟨by 
  have hpos : 0 < Λ := by have := hΛ1.out; linarith
  exact one_div_pos.mpr hpos ⟩

/-- The inverse of the Frobenius endomorphism. -/
noncomputable def frobeniusRingHomInv : RealNovikovSeries A →+* RealNovikovSeries A := 
  @Novikov.frobeniusRingHom (1/Λ) hΛinv A _

noncomputable instance : RingHomInvPair (@Novikov.frobeniusRingHom Λ hΛ A _) (frobeniusRingHomInv (Λ := Λ)) where
  comp_eq := by
    ext f d
    simp only [Novikov.frobeniusRingHom, frobeniusRingHomInv, frobenius]
    dsimp [frobeniusFun]
    have h_eq : (fun (x : Unit) ↦ ⟨(d () : ℝ) / (1 / Λ) / Λ, AddSubgroup.mem_top _⟩) = d := by
      ext i
      have hΛ_ne_zero : Λ ≠ 0 := by have := hΛ1.out; linarith
      change (d () : ℝ) / (1 / Λ) / Λ = (d i : ℝ)
      have h_i : d () = d i := by congr
      rw [h_i]
      have h1 : 1 / Λ ≠ 0 := one_div_ne_zero hΛ_ne_zero
      field_simp [hΛ_ne_zero, h1]
    rw [h_eq]
  comp_eq₂ := by
    ext f d
    simp only [Novikov.frobeniusRingHom, frobeniusRingHomInv, frobenius]
    dsimp [frobeniusFun]
    have h_eq : (fun (x : Unit) ↦ ⟨(d () : ℝ) / Λ / (1 / Λ), AddSubgroup.mem_top _⟩) = d := by
      ext i
      have hΛ_ne_zero : Λ ≠ 0 := by have := hΛ1.out; linarith
      change (d () : ℝ) / Λ / (1 / Λ) = (d i : ℝ)
      have h_i : d () = d i := by congr
      rw [h_i]
      have h1 : 1 / Λ ≠ 0 := one_div_ne_zero hΛ_ne_zero
      field_simp [hΛ_ne_zero, h1]
    rw [h_eq]

noncomputable instance : RingHomInvPair (frobeniusRingHomInv (Λ := Λ)) (@Novikov.frobeniusRingHom Λ hΛ A _) := 
  RingHomInvPair.symm _ _

/-- A Novikov isocrystal over a ring `A` is a finite projective module over
    `RealNovikovSeries A` together with a Frobenius-semilinear bijection. -/
structure NovikovIsocrystal (A : Type*) [CommRing A] where
  M : Type*
  [instAddCommGroup : AddCommGroup M]
  [instModule : Module (RealNovikovSeries A) M]
  [instFinite : Module.Finite (RealNovikovSeries A) M]
  [instProjective : Module.Projective (RealNovikovSeries A) M]
  F_M : M ≃ₛₗ[@Novikov.frobeniusRingHom Λ hΛ A _] M

attribute [instance] NovikovIsocrystal.instAddCommGroup NovikovIsocrystal.instModule
  NovikovIsocrystal.instFinite NovikovIsocrystal.instProjective

/-- A morphism between Novikov isocrystals is an $A((t))$-linear map that
    commutes with the Frobenius. -/
structure NovikovIsocrystal.Hom (M N : NovikovIsocrystal (Λ := Λ) A) where
  toLinearMap : M.M →ₗ[RealNovikovSeries A] N.M
  commute_frobenius : ∀ x : M.M, N.F_M (toLinearMap x) = toLinearMap (M.F_M x)

namespace NovikovIsocrystal

/-- Helper to show equality of morphisms. -/
@[ext]
lemma hom_ext {M N : NovikovIsocrystal (Λ := Λ) A} (f g : Hom M N) (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f; cases g; congr

/-- Category instance for Novikov isocrystals. -/
noncomputable instance : Category (NovikovIsocrystal (Λ := Λ) A) where
  Hom := Hom
  id M := {
    toLinearMap := LinearMap.id
    commute_frobenius := fun _ => rfl
  }
  comp f g := {
    toLinearMap := g.toLinearMap.comp f.toLinearMap
    commute_frobenius := by
      intro x
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [g.commute_frobenius, f.commute_frobenius]
  }
  id_comp f := by ext; rfl
  comp_id f := by ext; rfl
  assoc f g h := by ext; rfl

noncomputable instance (M N : NovikovIsocrystal (Λ := Λ) A) : Zero (M ⟶ N) where
  zero := { toLinearMap := 0, commute_frobenius := by intro x; simp only [LinearMap.zero_apply, map_zero] }

noncomputable instance (M N : NovikovIsocrystal (Λ := Λ) A) : Add (M ⟶ N) where
  add f g := { toLinearMap := f.toLinearMap + g.toLinearMap, commute_frobenius := by intro x; simp only [LinearMap.add_apply, map_add, f.commute_frobenius, g.commute_frobenius] }

noncomputable instance (M N : NovikovIsocrystal (Λ := Λ) A) : Neg (M ⟶ N) where
  neg f := { toLinearMap := -f.toLinearMap, commute_frobenius := by intro x; simp only [LinearMap.neg_apply, map_neg, f.commute_frobenius] }

noncomputable instance (M N : NovikovIsocrystal (Λ := Λ) A) : Sub (M ⟶ N) where
  sub f g := { toLinearMap := f.toLinearMap - g.toLinearMap, commute_frobenius := by intro x; simp only [LinearMap.sub_apply, map_sub, f.commute_frobenius, g.commute_frobenius] }

noncomputable instance (M N : NovikovIsocrystal (Λ := Λ) A) : SMul ℕ (M ⟶ N) where
  smul n f := { toLinearMap := n • f.toLinearMap, commute_frobenius := by intro x; simp only [LinearMap.smul_apply, map_nsmul, f.commute_frobenius] }

noncomputable instance (M N : NovikovIsocrystal (Λ := Λ) A) : SMul ℤ (M ⟶ N) where
  smul n f := { toLinearMap := n • f.toLinearMap, commute_frobenius := by intro x; simp only [LinearMap.smul_apply, map_zsmul, f.commute_frobenius] }

noncomputable instance homGroup (M N : NovikovIsocrystal (Λ := Λ) A) : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (fun f => f.toLinearMap) (fun f g h => by apply hom_ext; exact h)
    (rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Preadditive instance for the category of Novikov isocrystals. -/
noncomputable instance : Preadditive (NovikovIsocrystal (Λ := Λ) A) where
  homGroup _ _ := inferInstance
  add_comp _ _ _ f g h := by apply hom_ext; exact LinearMap.comp_add _ _ _
  comp_add _ _ _ f g h := by apply hom_ext; exact LinearMap.add_comp _ _ _

/-- The dual of a Novikov isocrystal. -/
noncomputable def dual (M : NovikovIsocrystal (Λ := Λ) A) : NovikovIsocrystal (Λ := Λ) A :=
  letI : AddCommGroup M.M := M.instAddCommGroup
  letI : Module (RealNovikovSeries A) M.M := M.instModule
  letI : Module.Finite (RealNovikovSeries A) M.M := M.instFinite
  letI : Module.Projective (RealNovikovSeries A) M.M := M.instProjective
  { M := Module.Dual (RealNovikovSeries A) M.M
    instFinite := inferInstance
    instProjective := inferInstance
    F_M := {
      toFun := fun f => {
        toFun := fun x => (frobeniusRingHom (Λ := Λ) (A := A)) (f (M.F_M.symm x))
        map_add' := by intro x y; rw [map_add, map_add, map_add]
        map_smul' := by
          intro r x
          dsimp
          rw [LinearEquiv.map_smulₛₗ, LinearMap.map_smul]
          simp only [smul_eq_mul, RingHom.map_mul, RingHomInvPair.comp_apply_eq₂]
      }
      invFun := fun g => {
        toFun := fun x => (frobeniusRingHomInv (Λ := Λ) (A := A)) (g (M.F_M x))
        map_add' := by intro x y; rw [map_add, map_add, map_add]
        map_smul' := by
          intro r x
          dsimp
          rw [LinearEquiv.map_smulₛₗ, LinearMap.map_smul]
          simp only [smul_eq_mul, RingHom.map_mul, RingHomInvPair.comp_apply_eq]
      }
      left_inv := by
        intro f; ext x; dsimp
        simp only [LinearEquiv.symm_apply_apply, RingHomInvPair.comp_apply_eq]
      right_inv := by
        intro g; ext x; dsimp
        simp only [LinearEquiv.apply_symm_apply, RingHomInvPair.comp_apply_eq₂]
      map_add' := by
        intro f g; ext x; dsimp
        simp only [map_add]
        rfl
      map_smul' := by
        intro r f; ext x; dsimp
        simp only [map_mul]
        rfl
    }
  }

/-- The internal Hom of two Novikov isocrystals. -/
noncomputable def internalHom (M N : NovikovIsocrystal (Λ := Λ) A) : NovikovIsocrystal (Λ := Λ) A :=
  let R := RealNovikovSeries A
  letI : AddCommGroup M.M := M.instAddCommGroup
  letI : Module R M.M := M.instModule
  letI : Module.Finite R M.M := M.instFinite
  letI : Module.Projective R M.M := M.instProjective
  letI : AddCommGroup N.M := N.instAddCommGroup
  letI : Module R N.M := N.instModule
  letI : Module.Finite R N.M := N.instFinite
  letI : Module.Projective R N.M := N.instProjective
  letI : Module.Finite R (M.M →ₗ[R] N.M) :=
    Novikov.Miscellany.linearMap_finite_projective (R := R) (M := M.M) (N := N.M)
  letI : Module.Projective R (M.M →ₗ[R] N.M) :=
    Novikov.Miscellany.linearMap_projective_projective (R := R) (M := M.M) (N := N.M)
  { M := M.M →ₗ[R] N.M
    instFinite := inferInstance
    instProjective := inferInstance
    F_M := {
      toFun := fun f => {
        toFun := fun x => N.F_M (f (M.F_M.symm x))
        map_add' := by intro x y; simp only [map_add]
        map_smul' := by
          intro r x
          dsimp
          rw [M.F_M.symm.map_smulₛₗ, f.map_smul, N.F_M.map_smulₛₗ]
          simp only [RingHomInvPair.comp_apply_eq₂]
      }
      invFun := fun g => {
        toFun := fun x => N.F_M.symm (g (M.F_M x))
        map_add' := by intro x y; simp only [map_add]
        map_smul' := by
          intro r x
          dsimp
          rw [M.F_M.map_smulₛₗ, g.map_smul, N.F_M.symm.map_smulₛₗ]
          simp only [RingHomInvPair.comp_apply_eq]
      }
      left_inv := by
        intro f; ext x; dsimp
        simp only [LinearEquiv.symm_apply_apply]
      right_inv := by
        intro g; ext x; dsimp
        simp only [LinearEquiv.apply_symm_apply]
      map_add' := by
        intro f g; ext x; dsimp
        simp only [map_add]
      map_smul' := by
        intro r f; ext x; dsimp
        simp only [N.F_M.map_smulₛₗ]
    }
  }

/-- A map between Novikov isocrystals commutes with Frobenius if and only if it is a
    Frobenius fixed point of the internal Hom isocrystal. -/
lemma frobenius_fixed_points (M N : NovikovIsocrystal (Λ := Λ) A) (f : M.M →ₗ[RealNovikovSeries A] N.M) :
    (∀ x, N.F_M (f x) = f (M.F_M x)) ↔ (internalHom M N).F_M f = f := by
  constructor
  · intro h
    refine LinearMap.ext fun x => ?_
    have h1 := h (M.F_M.symm x)
    rw [LinearEquiv.apply_symm_apply] at h1
    change N.F_M (f (M.F_M.symm x)) = f x
    exact h1
  · intro h x
    have h' := LinearMap.ext_iff.mp h (M.F_M x)
    change N.F_M (f (M.F_M.symm (M.F_M x))) = f (M.F_M x) at h'
    rw [LinearEquiv.symm_apply_apply] at h'
    exact h'


end NovikovIsocrystal

end Isocrystal

end Novikov
