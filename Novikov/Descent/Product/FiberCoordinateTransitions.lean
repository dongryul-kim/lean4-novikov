import Novikov.Descent.Product.FiberCompatibility
import Novikov.Descent.Product.GeneratorTransitions

/-!
# Fiber-coordinate transition identities for product-field descent

This file constructs pullback coordinates on the chosen constant fiber objects
and converts the fiber-trivialization compatibility into forward and inverse
coordinate transition identities.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract
open scoped BigOperators

namespace Novikov.Descent

noncomputable section

universe u v

variable {S : Type*} [SetLike S ℝ] {Γ : S}

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)] [∀ i, IsAlgClosed (K i)]

section FiberTrivializationPullbacks

attribute [local irreducible]
  fiberTrivializationLinearEquiv
  fiberGeneratorPullback₁
  fiberGeneratorPullback₂
  fiberConstGeneratorPullback₁
  fiberConstGeneratorPullback₂
  productFiberRankBoundN
  generatorTransitionCoeff
  generatorInverseTransitionCoeff
  LinearMap.baseChange

/-- The constant fiber descent isomorphism sends the `j`-th trivialized generator
to the finite sum with evaluated transition coefficients. -/
private lemma fiberConst_phi_generator_eq_sum
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j : Fin (productFiberRankBoundN K M)) :
    (fiberConstDescentDatum K M i).φ (fiberConstGeneratorPullback₁ K M i j) =
      ∑ k : Fin (productFiberRankBoundN K M),
        (show (realC (K i)).R₂ from coeffwiseEvalRingHom
          (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
          (generatorTransitionCoeff K M j k)) • fiberConstGeneratorPullback₂ K M i k := by
  rw [← fiberGeneratorConstTriv_pullback₁ K M i j]
  rw [fiberTrivializationLinearEquiv_commute_φ_apply K M i]
  rw [fiber_phi_generator_eq_sum_fiberGenerator]
  letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  rw [fiberGeneratorConstTriv_pullback₂]

/-- The inverse constant fiber descent isomorphism sends the `j`-th trivialized
generator to the finite sum with evaluated inverse-transition coefficients. -/
private lemma fiberConst_phi_symm_generator_eq_sum
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j : Fin (productFiberRankBoundN K M)) :
    (fiberConstDescentDatum K M i).φ.symm (fiberConstGeneratorPullback₂ K M i j) =
      ∑ k : Fin (productFiberRankBoundN K M),
        (show (realC (K i)).R₂ from coeffwiseEvalRingHom
          (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
          (generatorInverseTransitionCoeff K M j k)) • fiberConstGeneratorPullback₁ K M i k := by
  rw [← fiberGeneratorConstTriv_pullback₂ K M i j]
  have hcomm := fiberTrivializationLinearEquiv_commute_φ_apply K M i
    ((fiberDescentDatum K M i).φ.symm (fiberGeneratorPullback₂ K M i j))
  rw [LinearEquiv.apply_symm_apply] at hcomm
  have hsymm : (fiberConstDescentDatum K M i).φ.symm
      ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ :=
        (realC (K i)).π₂.toAlgebra;
        LinearMap.baseChange (realC (K i)).R₂
          (fiberTrivializationLinearEquiv K M i).toLinearMap)
        (fiberGeneratorPullback₂ K M i j)) =
      (letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ :=
        (realC (K i)).π₁.toAlgebra;
        LinearMap.baseChange (realC (K i)).R₂
          (fiberTrivializationLinearEquiv K M i).toLinearMap)
        ((fiberDescentDatum K M i).φ.symm (fiberGeneratorPullback₂ K M i j)) := by
    rw [← hcomm]
    rw [LinearEquiv.symm_apply_apply]
  rw [hsymm]
  rw [fiber_phi_symm_generator_eq_sum_fiberGenerator]
  letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₁.toAlgebra
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  rw [fiberGeneratorConstTriv_pullback₁]

end FiberTrivializationPullbacks

/-- Coordinates on the `π₁`-pullback of a constant fiber object, obtained by
associating scalar extension and then applying the single-fiber finite-free
coordinate map. -/
private noncomputable def fiberConstPullbackCoordπ₁
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) :
    π₁s (realC (K i)) (fiberConstDescentDatum K M i).M →ₗ[(realC (K i)).R₂]
      (Fin (productFiberRankBoundN K M) → (realC (K i)).R₂) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  letI : Module E.R₀ (fiberConstModule K M i).M := (fiberConstModule K M i).instModule
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  change (E.R₂ ⊗[E.R₁] (E.R₁ ⊗[E.R₀] (fiberConstModule K M i).M)) →ₗ[E.R₂]
      (Fin (productFiberRankBoundN K M) → E.R₂)
  exact (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
    (productFiberRankBoundN K M) i E.R₂).comp
      (baseChange_assoc E.π₀ E.π₁ (fiberConstModule K M i).M).toLinearMap

/-- Coordinates on the `π₂`-pullback of a constant fiber object, obtained by
associating scalar extension and then applying the single-fiber finite-free
coordinate map. -/
private noncomputable def fiberConstPullbackCoordπ₂
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) :
    π₂s (realC (K i)) (fiberConstDescentDatum K M i).M →ₗ[(realC (K i)).R₂]
      (Fin (productFiberRankBoundN K M) → (realC (K i)).R₂) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  letI : Module E.R₀ (fiberConstModule K M i).M := (fiberConstModule K M i).instModule
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  change (E.R₂ ⊗[E.R₁] (E.R₁ ⊗[E.R₀] (fiberConstModule K M i).M)) →ₗ[E.R₂]
      (Fin (productFiberRankBoundN K M) → E.R₂)
  exact (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
    (productFiberRankBoundN K M) i E.R₂).comp
      (baseChange_assoc E.π₀ E.π₂ (fiberConstModule K M i).M).toLinearMap

/-- The `π₁`-pullback coordinate of `1 ⊗ y` is obtained by applying `π₁` to the
coordinate of `y`. -/
private lemma fiberConstPullbackCoordπ₁_one_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (y : (fiberConstDescentDatum K M i).M)
    (c : Fin (productFiberRankBoundN K M)) :
    fiberConstPullbackCoordπ₁ K M i
      ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₁.toAlgebra
        (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁] y)) c =
    (realC (K i)).π₁
      ((letI : Algebra (K i) (realC (K i)).R₁ :=
        (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
       FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i (realC (K i)).R₁ y c)) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  letI : Module E.R₀ (fiberConstModule K M i).M := (fiberConstModule K M i).instModule
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  change (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i E.R₂)
        ((baseChange_assoc E.π₀ E.π₁ (fiberConstModule K M i).M)
          ((1 : E.R₂) ⊗ₜ[E.R₁] y)) c =
      E.π₁ ((FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i E.R₁ y) c)
  have h := FiniteProjectiveModule.fiberBaseChangeCoord_baseChange_assoc K (fiberConstModule K M)
    (productFiberRankBoundN K M) i E.R₁ E.R₂ E.π₀ E.π₁ y
  exact congrFun h c

/-- The `π₂`-pullback coordinate of `1 ⊗ y` is obtained by applying `π₂` to the
coordinate of `y`. -/
private lemma fiberConstPullbackCoordπ₂_one_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (y : (fiberConstDescentDatum K M i).M)
    (c : Fin (productFiberRankBoundN K M)) :
    fiberConstPullbackCoordπ₂ K M i
      ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
        (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁] y)) c =
    (realC (K i)).π₂
      ((letI : Algebra (K i) (realC (K i)).R₁ :=
        (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
       FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i (realC (K i)).R₁ y c)) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  letI : Module E.R₀ (fiberConstModule K M i).M := (fiberConstModule K M i).instModule
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  change (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i E.R₂)
        ((baseChange_assoc E.π₀ E.π₂ (fiberConstModule K M i).M)
          ((1 : E.R₂) ⊗ₜ[E.R₁] y)) c =
      E.π₂ ((FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i E.R₁ y) c)
  have h := FiniteProjectiveModule.fiberBaseChangeCoord_baseChange_assoc K (fiberConstModule K M)
    (productFiberRankBoundN K M) i E.R₁ E.R₂ E.π₀ E.π₂ y
  exact congrFun h c

section FiberConstCoordinateInduction

attribute [local irreducible]
  FiniteProjectiveModule.fiberBaseChangeCoord
  FiniteProjectiveModule.fiberCoordIntoFree
  productFiberRankBoundN
  baseChange_assoc

/-- Pure-tensor case of the forward constant-coordinate calculation. -/
private lemma fiberConstPullbackCoordπ₂_constant_φ_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (s : (realC (K i)).R₁) (p : (fiberConstModule K M i).M)
    (c : Fin (productFiberRankBoundN K M)) :
    let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i);
    let P := (fiberConstModule K M i).M;
    letI : Module E.R₀ P := (fiberConstModule K M i).instModule;
    letI : Module.Finite E.R₀ P := (fiberConstModule K M i).instFinite;
    letI : Module.Projective E.R₀ P := (fiberConstModule K M i).instProjective;
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra;
    letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra;
    fiberConstPullbackCoordπ₂ K M i
      ((constantDescentDatum E P).φ
        ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
          (1 : E.R₂) ⊗ₜ[E.R₁] (s ⊗ₜ[E.R₀] p)))) c =
    E.π₁ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₁ (s ⊗ₜ[E.R₀] p) c) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  letI : Module E.R₀ (fiberConstModule K M i).M := (fiberConstModule K M i).instModule
  letI : Module.Finite E.R₀ (fiberConstModule K M i).M := (fiberConstModule K M i).instFinite
  letI : Module.Projective E.R₀ (fiberConstModule K M i).M :=
    (fiberConstModule K M i).instProjective
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  change fiberConstPullbackCoordπ₂ K M i
      ((constantDescentDatum E (fiberConstModule K M i).M).φ
        ((1 : E.R₂) ⊗ₜ[E.R₁] (s ⊗ₜ[E.R₀] p))) c =
    E.π₁ ((FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₁ (s ⊗ₜ[E.R₀] p)) c)
  rw [constantDescentDatum_φ_tmul]
  letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  dsimp [fiberConstPullbackCoordπ₂]
  change (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₂)
      ((baseChange_assoc E.π₀ E.π₂ (fiberConstModule K M i).M)
        ((E.π₁ s * 1) ⊗ₜ[E.R₁] ((1 : E.R₁) ⊗ₜ[E.R₀] p))) c =
    E.π₁ ((FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₁ (s ⊗ₜ[E.R₀] p)) c)
  rw [baseChange_assoc_tmul]
  simp only [one_smul, mul_one]
  change (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₂)
      ((E.π₁ s) ⊗ₜ[K i] p) c =
    E.π₁ ((FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₁ (s ⊗ₜ[K i] p)) c)
  rw [FiniteProjectiveModule.fiberBaseChangeCoord_tmul]
  rw [FiniteProjectiveModule.fiberBaseChangeCoord_tmul]
  simp only [Algebra.smul_def]
  rw [show (algebraMap (K i) E.R₂)
        ((FiniteProjectiveModule.fiberCoordIntoFree K (fiberConstModule K M)
          (productFiberRankBoundN K M) i) p c) =
      E.π₁ ((algebraMap (K i) E.R₁)
        ((FiniteProjectiveModule.fiberCoordIntoFree K (fiberConstModule K M)
          (productFiberRankBoundN K M) i) p c)) by
    change E.π₂ (E.π₀ ((FiniteProjectiveModule.fiberCoordIntoFree K
      (fiberConstModule K M) (productFiberRankBoundN K M) i) p c)) =
      E.π₁ (E.π₀ ((FiniteProjectiveModule.fiberCoordIntoFree K
        (fiberConstModule K M) (productFiberRankBoundN K M) i) p c))
    exact congrArg (fun f : E.R₀ →+* E.R₂ => f _)
      E.π₁_π₀_eq_π₂_π₀.symm]
  rw [map_mul]

/-- Zero case of the forward constant-coordinate calculation. -/
private lemma fiberConstPullbackCoordπ₂_constant_φ_zero
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (c : Fin (productFiberRankBoundN K M)) :
    let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i);
    let P := (fiberConstModule K M i).M;
    letI : Module E.R₀ P := (fiberConstModule K M i).instModule;
    letI : Module.Finite E.R₀ P := (fiberConstModule K M i).instFinite;
    letI : Module.Projective E.R₀ P := (fiberConstModule K M i).instProjective;
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra;
    letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra;
    fiberConstPullbackCoordπ₂ K M i
      ((constantDescentDatum E P).φ
        ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
          (1 : E.R₂) ⊗ₜ[E.R₁] (0 : E.R₁ ⊗[E.R₀] P)))) c =
    E.π₁ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₁ (0 : E.R₁ ⊗[E.R₀] P) c) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  let P := (fiberConstModule K M i).M
  letI : Module E.R₀ P := (fiberConstModule K M i).instModule
  letI : Module.Finite E.R₀ P := (fiberConstModule K M i).instFinite
  letI : Module.Projective E.R₀ P := (fiberConstModule K M i).instProjective
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  have ht : ((1 : E.R₂) ⊗ₜ[E.R₁]
      (0 : E.R₁ ⊗[E.R₀] P)) = 0 := by
    rw [TensorProduct.tmul_zero]
  calc
    fiberConstPullbackCoordπ₂ K M i
        ((constantDescentDatum E P).φ
          ((1 : E.R₂) ⊗ₜ[E.R₁] (0 : E.R₁ ⊗[E.R₀] P))) c
        = fiberConstPullbackCoordπ₂ K M i
            ((constantDescentDatum E P).φ 0) c := by
          exact congrArg (fun q => fiberConstPullbackCoordπ₂ K M i
            ((constantDescentDatum E P).φ q) c) ht
    _ = E.π₁ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
          (productFiberRankBoundN K M) i E.R₁ (0 : E.R₁ ⊗[E.R₀] P) c) := by
          rw [map_zero]
          have hL := congrFun (map_zero (fiberConstPullbackCoordπ₂ K M i)) c
          have hR := congrFun (map_zero (FiniteProjectiveModule.fiberBaseChangeCoord K
            (fiberConstModule K M) (productFiberRankBoundN K M) i E.R₁)) c
          change (fiberConstPullbackCoordπ₂ K M i) 0 c =
            E.π₁ ((FiniteProjectiveModule.fiberBaseChangeCoord K
              (fiberConstModule K M) (productFiberRankBoundN K M) i E.R₁) 0 c)
          rw [hL, hR]
          change (0 : E.R₂) = E.π₁ (0 : E.R₁)
          exact (map_zero E.π₁).symm

/-- Additive step of the forward constant-coordinate calculation. -/
private lemma fiberConstPullbackCoordπ₂_constant_φ_add
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (c : Fin (productFiberRankBoundN K M)) :
    let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i);
    let P := (fiberConstModule K M i).M;
    letI : Module E.R₀ P := (fiberConstModule K M i).instModule;
    letI : Module.Finite E.R₀ P := (fiberConstModule K M i).instFinite;
    letI : Module.Projective E.R₀ P := (fiberConstModule K M i).instProjective;
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra;
    letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra;
    ∀ x y : E.R₁ ⊗[E.R₀] P,
      fiberConstPullbackCoordπ₂ K M i
          ((constantDescentDatum E P).φ
            ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
              (1 : E.R₂) ⊗ₜ[E.R₁] x))) c =
        E.π₁ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
          (productFiberRankBoundN K M) i E.R₁ x c) →
      fiberConstPullbackCoordπ₂ K M i
          ((constantDescentDatum E P).φ
            ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
              (1 : E.R₂) ⊗ₜ[E.R₁] y))) c =
        E.π₁ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
          (productFiberRankBoundN K M) i E.R₁ y c) →
      fiberConstPullbackCoordπ₂ K M i
          ((constantDescentDatum E P).φ
            ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
              (1 : E.R₂) ⊗ₜ[E.R₁] (x + y)))) c =
        E.π₁ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
          (productFiberRankBoundN K M) i E.R₁ (x + y) c) := by
  dsimp only
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  let P := (fiberConstModule K M i).M
  letI : Module E.R₀ P := (fiberConstModule K M i).instModule
  letI : Module.Finite E.R₀ P := (fiberConstModule K M i).instFinite
  letI : Module.Projective E.R₀ P := (fiberConstModule K M i).instProjective
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  intro x y hx hy
  have ht : ((1 : E.R₂) ⊗ₜ[E.R₁] (x + y)) =
      ((1 : E.R₂) ⊗ₜ[E.R₁] x) + ((1 : E.R₂) ⊗ₜ[E.R₁] y) := by
    rw [TensorProduct.tmul_add]
  have hcoord_add :
      (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i E.R₁ (x + y) c) =
      (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i E.R₁ x c) +
      (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i E.R₁ y c) := by
    exact congrFun (map_add (FiniteProjectiveModule.fiberBaseChangeCoord K
      (fiberConstModule K M) (productFiberRankBoundN K M) i E.R₁) x y) c
  calc
    fiberConstPullbackCoordπ₂ K M i
        ((constantDescentDatum E P).φ
          ((1 : E.R₂) ⊗ₜ[E.R₁] (x + y))) c
        = fiberConstPullbackCoordπ₂ K M i
            ((constantDescentDatum E P).φ
              (((1 : E.R₂) ⊗ₜ[E.R₁] x) + ((1 : E.R₂) ⊗ₜ[E.R₁] y))) c := by
          exact congrArg (fun q => fiberConstPullbackCoordπ₂ K M i
            ((constantDescentDatum E P).φ q) c) ht
    _ = fiberConstPullbackCoordπ₂ K M i
            (((constantDescentDatum E P).φ ((1 : E.R₂) ⊗ₜ[E.R₁] x)) +
              ((constantDescentDatum E P).φ ((1 : E.R₂) ⊗ₜ[E.R₁] y))) c := by
          exact congrArg (fun q => fiberConstPullbackCoordπ₂ K M i q c)
            (map_add (constantDescentDatum E P).φ
              ((1 : E.R₂) ⊗ₜ[E.R₁] x) ((1 : E.R₂) ⊗ₜ[E.R₁] y))
    _ = fiberConstPullbackCoordπ₂ K M i
            ((constantDescentDatum E P).φ ((1 : E.R₂) ⊗ₜ[E.R₁] x)) c +
          fiberConstPullbackCoordπ₂ K M i
            ((constantDescentDatum E P).φ ((1 : E.R₂) ⊗ₜ[E.R₁] y)) c := by
          exact congrFun (map_add (fiberConstPullbackCoordπ₂ K M i) _ _) c
    _ = E.π₁ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
          (productFiberRankBoundN K M) i E.R₁ (x + y) c) := by
          rw [hx, hy, hcoord_add, map_add]
          rfl

/-- Applying the constant descent isomorphism to `1 ⊗ y` and taking `π₂`-pullback
coordinates gives the `π₁`-image of the original coordinates. -/
private lemma fiberConstPullbackCoordπ₂_constant_φ_one_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (y : (fiberConstDescentDatum K M i).M)
    (c : Fin (productFiberRankBoundN K M)) :
    fiberConstPullbackCoordπ₂ K M i
      ((fiberConstDescentDatum K M i).φ
        ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₁.toAlgebra
          (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁] y))) c =
    (realC (K i)).π₁
      ((letI : Algebra (K i) (realC (K i)).R₁ :=
        (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
       FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i (realC (K i)).R₁ y c)) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  letI : Module E.R₀ (fiberConstModule K M i).M := (fiberConstModule K M i).instModule
  letI : Module.Finite E.R₀ (fiberConstModule K M i).M := (fiberConstModule K M i).instFinite
  letI : Module.Projective E.R₀ (fiberConstModule K M i).M :=
    (fiberConstModule K M i).instProjective
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  change E.R₁ ⊗[E.R₀] (fiberConstModule K M i).M at y
  change fiberConstPullbackCoordπ₂ K M i
      ((constantDescentDatum E (fiberConstModule K M i).M).φ
        ((1 : E.R₂) ⊗ₜ[E.R₁] y)) c =
    E.π₁ ((FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₁ y) c)
  induction y using TensorProduct.induction_on with
  | zero =>
      exact fiberConstPullbackCoordπ₂_constant_φ_zero K M i c
  | add x y hx hy =>
      exact fiberConstPullbackCoordπ₂_constant_φ_add K M i c x y hx hy
  | tmul s p =>
      exact fiberConstPullbackCoordπ₂_constant_φ_tmul K M i s p c

/-- Pure-tensor case of the inverse constant-coordinate calculation. -/
private lemma fiberConstPullbackCoordπ₁_constant_φ_symm_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (s : (realC (K i)).R₁) (p : (fiberConstModule K M i).M)
    (c : Fin (productFiberRankBoundN K M)) :
    let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i);
    let P := (fiberConstModule K M i).M;
    letI : Module E.R₀ P := (fiberConstModule K M i).instModule;
    letI : Module.Finite E.R₀ P := (fiberConstModule K M i).instFinite;
    letI : Module.Projective E.R₀ P := (fiberConstModule K M i).instProjective;
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra;
    letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra;
    fiberConstPullbackCoordπ₁ K M i
      ((constantDescentDatum E P).φ.symm
        ((letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra;
          (1 : E.R₂) ⊗ₜ[E.R₁] (s ⊗ₜ[E.R₀] p)))) c =
    E.π₂ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₁ (s ⊗ₜ[E.R₀] p) c) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  letI : Module E.R₀ (fiberConstModule K M i).M := (fiberConstModule K M i).instModule
  letI : Module.Finite E.R₀ (fiberConstModule K M i).M := (fiberConstModule K M i).instFinite
  letI : Module.Projective E.R₀ (fiberConstModule K M i).M :=
    (fiberConstModule K M i).instProjective
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  change fiberConstPullbackCoordπ₁ K M i
      ((constantDescentDatum E (fiberConstModule K M i).M).φ.symm
        ((1 : E.R₂) ⊗ₜ[E.R₁] (s ⊗ₜ[E.R₀] p))) c =
    E.π₂ ((FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₁ (s ⊗ₜ[E.R₀] p)) c)
  rw [constantDescentDatum_φ_symm_tmul]
  letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  dsimp [fiberConstPullbackCoordπ₁]
  change (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₂)
      ((baseChange_assoc E.π₀ E.π₁ (fiberConstModule K M i).M)
        ((E.π₂ s * 1) ⊗ₜ[E.R₁] ((1 : E.R₁) ⊗ₜ[E.R₀] p))) c =
    E.π₂ ((FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₁ (s ⊗ₜ[E.R₀] p)) c)
  rw [baseChange_assoc_tmul]
  simp only [one_smul, mul_one]
  change (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₂)
      ((E.π₂ s) ⊗ₜ[K i] p) c =
    E.π₂ ((FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₁ (s ⊗ₜ[K i] p)) c)
  rw [FiniteProjectiveModule.fiberBaseChangeCoord_tmul]
  rw [FiniteProjectiveModule.fiberBaseChangeCoord_tmul]
  simp only [Algebra.smul_def]
  rw [show (algebraMap (K i) E.R₂)
        ((FiniteProjectiveModule.fiberCoordIntoFree K (fiberConstModule K M)
          (productFiberRankBoundN K M) i) p c) =
      E.π₂ ((algebraMap (K i) E.R₁)
        ((FiniteProjectiveModule.fiberCoordIntoFree K (fiberConstModule K M)
          (productFiberRankBoundN K M) i) p c)) by
    change E.π₁ (E.π₀ ((FiniteProjectiveModule.fiberCoordIntoFree K
      (fiberConstModule K M) (productFiberRankBoundN K M) i) p c)) =
      E.π₂ (E.π₀ ((FiniteProjectiveModule.fiberCoordIntoFree K
        (fiberConstModule K M) (productFiberRankBoundN K M) i) p c))
    exact congrArg (fun f : E.R₀ →+* E.R₂ => f _)
      E.π₁_π₀_eq_π₂_π₀]
  rw [map_mul]

/-- Zero case of the inverse constant-coordinate calculation. -/
private lemma fiberConstPullbackCoordπ₁_constant_φ_symm_zero
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (c : Fin (productFiberRankBoundN K M)) :
    let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i);
    let P := (fiberConstModule K M i).M;
    letI : Module E.R₀ P := (fiberConstModule K M i).instModule;
    letI : Module.Finite E.R₀ P := (fiberConstModule K M i).instFinite;
    letI : Module.Projective E.R₀ P := (fiberConstModule K M i).instProjective;
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra;
    letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra;
    fiberConstPullbackCoordπ₁ K M i
      ((constantDescentDatum E P).φ.symm
        ((letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra;
          (1 : E.R₂) ⊗ₜ[E.R₁] (0 : E.R₁ ⊗[E.R₀] P)))) c =
    E.π₂ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₁ (0 : E.R₁ ⊗[E.R₀] P) c) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  let P := (fiberConstModule K M i).M
  letI : Module E.R₀ P := (fiberConstModule K M i).instModule
  letI : Module.Finite E.R₀ P := (fiberConstModule K M i).instFinite
  letI : Module.Projective E.R₀ P := (fiberConstModule K M i).instProjective
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  have ht : ((1 : E.R₂) ⊗ₜ[E.R₁]
      (0 : E.R₁ ⊗[E.R₀] P)) = 0 := by
    rw [TensorProduct.tmul_zero]
  calc
    fiberConstPullbackCoordπ₁ K M i
        ((constantDescentDatum E P).φ.symm
          ((1 : E.R₂) ⊗ₜ[E.R₁] (0 : E.R₁ ⊗[E.R₀] P))) c
        = fiberConstPullbackCoordπ₁ K M i
            ((constantDescentDatum E P).φ.symm 0) c := by
          exact congrArg (fun q => fiberConstPullbackCoordπ₁ K M i
            ((constantDescentDatum E P).φ.symm q) c) ht
    _ = E.π₂ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
          (productFiberRankBoundN K M) i E.R₁ (0 : E.R₁ ⊗[E.R₀] P) c) := by
          rw [map_zero]
          have hL := congrFun (map_zero (fiberConstPullbackCoordπ₁ K M i)) c
          have hR := congrFun (map_zero (FiniteProjectiveModule.fiberBaseChangeCoord K
            (fiberConstModule K M) (productFiberRankBoundN K M) i E.R₁)) c
          change (fiberConstPullbackCoordπ₁ K M i) 0 c =
            E.π₂ ((FiniteProjectiveModule.fiberBaseChangeCoord K
              (fiberConstModule K M) (productFiberRankBoundN K M) i E.R₁) 0 c)
          rw [hL, hR]
          change (0 : E.R₂) = E.π₂ (0 : E.R₁)
          exact (map_zero E.π₂).symm

/-- Additive step of the inverse constant-coordinate calculation. -/
private lemma fiberConstPullbackCoordπ₁_constant_φ_symm_add
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (c : Fin (productFiberRankBoundN K M)) :
    let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i);
    let P := (fiberConstModule K M i).M;
    letI : Module E.R₀ P := (fiberConstModule K M i).instModule;
    letI : Module.Finite E.R₀ P := (fiberConstModule K M i).instFinite;
    letI : Module.Projective E.R₀ P := (fiberConstModule K M i).instProjective;
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra;
    letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra;
    ∀ x y : E.R₁ ⊗[E.R₀] P,
      fiberConstPullbackCoordπ₁ K M i
          ((constantDescentDatum E P).φ.symm
            ((letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra;
              (1 : E.R₂) ⊗ₜ[E.R₁] x))) c =
        E.π₂ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
          (productFiberRankBoundN K M) i E.R₁ x c) →
      fiberConstPullbackCoordπ₁ K M i
          ((constantDescentDatum E P).φ.symm
            ((letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra;
              (1 : E.R₂) ⊗ₜ[E.R₁] y))) c =
        E.π₂ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
          (productFiberRankBoundN K M) i E.R₁ y c) →
      fiberConstPullbackCoordπ₁ K M i
          ((constantDescentDatum E P).φ.symm
            ((letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra;
              (1 : E.R₂) ⊗ₜ[E.R₁] (x + y)))) c =
        E.π₂ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
          (productFiberRankBoundN K M) i E.R₁ (x + y) c) := by
  dsimp only
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  let P := (fiberConstModule K M i).M
  letI : Module E.R₀ P := (fiberConstModule K M i).instModule
  letI : Module.Finite E.R₀ P := (fiberConstModule K M i).instFinite
  letI : Module.Projective E.R₀ P := (fiberConstModule K M i).instProjective
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  intro x y hx hy
  have ht : ((1 : E.R₂) ⊗ₜ[E.R₁] (x + y)) =
      ((1 : E.R₂) ⊗ₜ[E.R₁] x) + ((1 : E.R₂) ⊗ₜ[E.R₁] y) := by
    rw [TensorProduct.tmul_add]
  have hcoord_add :
      (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i E.R₁ (x + y) c) =
      (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i E.R₁ x c) +
      (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i E.R₁ y c) := by
    exact congrFun (map_add (FiniteProjectiveModule.fiberBaseChangeCoord K
      (fiberConstModule K M) (productFiberRankBoundN K M) i E.R₁) x y) c
  calc
    fiberConstPullbackCoordπ₁ K M i
        ((constantDescentDatum E P).φ.symm
          ((1 : E.R₂) ⊗ₜ[E.R₁] (x + y))) c
        = fiberConstPullbackCoordπ₁ K M i
            ((constantDescentDatum E P).φ.symm
              (((1 : E.R₂) ⊗ₜ[E.R₁] x) + ((1 : E.R₂) ⊗ₜ[E.R₁] y))) c := by
          exact congrArg (fun q => fiberConstPullbackCoordπ₁ K M i
            ((constantDescentDatum E P).φ.symm q) c) ht
    _ = fiberConstPullbackCoordπ₁ K M i
            (((constantDescentDatum E P).φ.symm ((1 : E.R₂) ⊗ₜ[E.R₁] x)) +
              ((constantDescentDatum E P).φ.symm ((1 : E.R₂) ⊗ₜ[E.R₁] y))) c := by
          exact congrArg (fun q => fiberConstPullbackCoordπ₁ K M i q c)
            (map_add (constantDescentDatum E P).φ.symm
              ((1 : E.R₂) ⊗ₜ[E.R₁] x) ((1 : E.R₂) ⊗ₜ[E.R₁] y))
    _ = fiberConstPullbackCoordπ₁ K M i
            ((constantDescentDatum E P).φ.symm ((1 : E.R₂) ⊗ₜ[E.R₁] x)) c +
          fiberConstPullbackCoordπ₁ K M i
            ((constantDescentDatum E P).φ.symm ((1 : E.R₂) ⊗ₜ[E.R₁] y)) c := by
          exact congrFun (map_add (fiberConstPullbackCoordπ₁ K M i) _ _) c
    _ = E.π₂ (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
          (productFiberRankBoundN K M) i E.R₁ (x + y) c) := by
          rw [hx, hy, hcoord_add, map_add]
          rfl

/-- Applying the inverse constant descent isomorphism to `1 ⊗ y` and taking
`π₁`-pullback coordinates gives the `π₂`-image of the original coordinates. -/
private lemma fiberConstPullbackCoordπ₁_constant_φ_symm_one_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (y : (fiberConstDescentDatum K M i).M)
    (c : Fin (productFiberRankBoundN K M)) :
    fiberConstPullbackCoordπ₁ K M i
      ((fiberConstDescentDatum K M i).φ.symm
        ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
          (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁] y))) c =
    (realC (K i)).π₂
      ((letI : Algebra (K i) (realC (K i)).R₁ :=
        (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
       FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i (realC (K i)).R₁ y c)) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  letI : Module E.R₀ (fiberConstModule K M i).M := (fiberConstModule K M i).instModule
  letI : Module.Finite E.R₀ (fiberConstModule K M i).M := (fiberConstModule K M i).instFinite
  letI : Module.Projective E.R₀ (fiberConstModule K M i).M :=
    (fiberConstModule K M i).instProjective
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  letI : Algebra (K i) E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  change E.R₁ ⊗[E.R₀] (fiberConstModule K M i).M at y
  change fiberConstPullbackCoordπ₁ K M i
      ((constantDescentDatum E (fiberConstModule K M i).M).φ.symm
        ((1 : E.R₂) ⊗ₜ[E.R₁] y)) c =
    E.π₂ ((FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) i E.R₁ y) c)
  induction y using TensorProduct.induction_on with
  | zero =>
      exact fiberConstPullbackCoordπ₁_constant_φ_symm_zero K M i c
  | add x y hx hy =>
      exact fiberConstPullbackCoordπ₁_constant_φ_symm_add K M i c x y hx hy
  | tmul s p =>
      exact fiberConstPullbackCoordπ₁_constant_φ_symm_tmul K M i s p c

end FiberConstCoordinateInduction

/-- Pullback coordinates of a `π₂` constant-generator pullback are the `π₂`
images of the trivialized generator coordinates. -/
private lemma fiberConstPullbackCoordπ₂_generator
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j c : Fin (productFiberRankBoundN K M)) :
    fiberConstPullbackCoordπ₂ K M i (fiberConstGeneratorPullback₂ K M i j) c =
      (realC (K i)).π₂
        (trivializedCoordFamily K M (productFiberGenerator K M j) c i) := by
  rw [fiberConstGeneratorPullback₂]
  rw [fiberConstPullbackCoordπ₂_one_tmul]
  rw [trivializedCoordFamily_generator_apply]

/-- Pullback coordinates of a `π₁` constant-generator pullback are the `π₁`
images of the trivialized generator coordinates. -/
private lemma fiberConstPullbackCoordπ₁_generator
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j c : Fin (productFiberRankBoundN K M)) :
    fiberConstPullbackCoordπ₁ K M i (fiberConstGeneratorPullback₁ K M i j) c =
      (realC (K i)).π₁
        (trivializedCoordFamily K M (productFiberGenerator K M j) c i) := by
  rw [fiberConstGeneratorPullback₁]
  rw [fiberConstPullbackCoordπ₁_one_tmul]
  rw [trivializedCoordFamily_generator_apply]

/-- The left side of the forward coordinate equality is the `π₂`-pullback
coordinate of the constant-fiber descent translate. -/
private lemma generatorForward_lhs_eq_pullback
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j c : Fin (productFiberRankBoundN K M)) :
    (realC (K i)).π₁ (trivializedCoordFamily K M (productFiberGenerator K M j) c i) =
      fiberConstPullbackCoordπ₂ K M i
        ((fiberConstDescentDatum K M i).φ (fiberConstGeneratorPullback₁ K M i j)) c := by
  rw [trivializedCoordFamily_generator_apply]
  rw [fiberConstGeneratorPullback₁]
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra (K i) (realC (K i)).R₁ :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
  change (realC (K i)).π₁
      ((FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i (realC (K i)).R₁
        (fiberGeneratorConstTriv K M i j)) c) =
    fiberConstPullbackCoordπ₂ K M i
      ((fiberConstDescentDatum K M i).φ
        ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₁.toAlgebra
          (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁]
            fiberGeneratorConstTriv K M i j))) c
  rw [← fiberConstPullbackCoordπ₂_constant_φ_one_tmul]

/-- The left side of the inverse coordinate equality is the `π₁`-pullback
coordinate of the inverse constant-fiber descent translate. -/
private lemma generatorInverse_lhs_eq_pullback
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j c : Fin (productFiberRankBoundN K M)) :
    (realC (K i)).π₂ (trivializedCoordFamily K M (productFiberGenerator K M j) c i) =
      fiberConstPullbackCoordπ₁ K M i
        ((fiberConstDescentDatum K M i).φ.symm (fiberConstGeneratorPullback₂ K M i j)) c := by
  rw [trivializedCoordFamily_generator_apply]
  rw [fiberConstGeneratorPullback₂]
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  letI : Algebra (K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra (K i) (realC (K i)).R₁ :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
  change (realC (K i)).π₂
      ((FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i (realC (K i)).R₁
        (fiberGeneratorConstTriv K M i j)) c) =
    fiberConstPullbackCoordπ₁ K M i
      ((fiberConstDescentDatum K M i).φ.symm
        ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
          (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁]
            fiberGeneratorConstTriv K M i j))) c
  rw [← fiberConstPullbackCoordπ₁_constant_φ_symm_one_tmul]

/-- Applying `π₂`-pullback coordinates to the forward transition sum gives the
right side of the forward coordinate equality. -/
private lemma fiberConstPullbackCoordπ₂_transition_sum
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j c : Fin (productFiberRankBoundN K M)) :
    fiberConstPullbackCoordπ₂ K M i
      (∑ k : Fin (productFiberRankBoundN K M),
        (show (realC (K i)).R₂ from coeffwiseEvalRingHom
          (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
          (generatorTransitionCoeff K M j k)) •
          fiberConstGeneratorPullback₂ K M i k) c =
      ∑ k : Fin (productFiberRankBoundN K M),
        (show (realC (K i)).R₂ from coeffwiseEvalRingHom
          (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
          (generatorTransitionCoeff K M j k)) *
          (realC (K i)).π₂ (trivializedCoordFamily K M (productFiberGenerator K M k) c i) := by
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [fiberConstPullbackCoordπ₂_generator]

/-- Applying `π₁`-pullback coordinates to the inverse transition sum gives the
right side of the inverse coordinate equality. -/
private lemma fiberConstPullbackCoordπ₁_inverse_transition_sum
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j c : Fin (productFiberRankBoundN K M)) :
    fiberConstPullbackCoordπ₁ K M i
      (∑ k : Fin (productFiberRankBoundN K M),
        (show (realC (K i)).R₂ from coeffwiseEvalRingHom
          (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
          (generatorInverseTransitionCoeff K M j k)) •
          fiberConstGeneratorPullback₁ K M i k) c =
      ∑ k : Fin (productFiberRankBoundN K M),
        (show (realC (K i)).R₂ from coeffwiseEvalRingHom
          (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
          (generatorInverseTransitionCoeff K M j k)) *
          (realC (K i)).π₁ (trivializedCoordFamily K M (productFiberGenerator K M k) c i) := by
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [fiberConstPullbackCoordπ₁_generator]


/-- Coordinate form of the forward descent relation for chosen generators. -/
def GeneratorForwardCoordinateEquality
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) : Prop :=
  ∀ (i : I) (j c : Fin (productFiberRankBoundN K M)),
    (realC (K i)).π₁ (trivializedCoordFamily K M (productFiberGenerator K M j) c i) =
      ∑ k : Fin (productFiberRankBoundN K M),
        (show (realC (K i)).R₂ from coeffwiseEvalRingHom
          (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
          (generatorTransitionCoeff K M j k)) *
          (realC (K i)).π₂ (trivializedCoordFamily K M (productFiberGenerator K M k) c i)

/-- Coordinate form of the inverse descent relation for chosen generators. -/
def GeneratorInverseCoordinateEquality
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) : Prop :=
  ∀ (i : I) (j c : Fin (productFiberRankBoundN K M)),
    (realC (K i)).π₂ (trivializedCoordFamily K M (productFiberGenerator K M j) c i) =
      ∑ k : Fin (productFiberRankBoundN K M),
        (show (realC (K i)).R₂ from coeffwiseEvalRingHom
          (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
          (generatorInverseTransitionCoeff K M j k)) *
          (realC (K i)).π₁ (trivializedCoordFamily K M (productFiberGenerator K M k) c i)

/-- The forward coordinate equality for the chosen generators. -/
lemma generatorForwardCoordinateEquality
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    GeneratorForwardCoordinateEquality K M := by
  intro i j c
  rw [generatorForward_lhs_eq_pullback]
  rw [fiberConst_phi_generator_eq_sum]
  rw [fiberConstPullbackCoordπ₂_transition_sum]

/-- The inverse coordinate equality for the chosen generators. -/
lemma generatorInverseCoordinateEquality
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    GeneratorInverseCoordinateEquality K M := by
  intro i j c
  rw [generatorInverse_lhs_eq_pullback]
  rw [fiberConst_phi_symm_generator_eq_sum]
  rw [fiberConstPullbackCoordπ₁_inverse_transition_sum]
end

end Novikov.Descent
