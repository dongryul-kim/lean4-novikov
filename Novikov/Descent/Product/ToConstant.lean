import Novikov.Descent.Product.ConstantCoordinateCompatibility
import Novikov.Descent.Product.EssentialSurj

/-!
# The forward comparison to the product constant object

This file develops the product-constant generator coordinates, proves the
transition formulas for the lifted coordinates, and uses them to construct the
descent morphism `toConstant`.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract
open scoped BigOperators

namespace Novikov.Descent

noncomputable section

universe u v

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)] [∀ i, IsAlgClosed (K i)]

/-- The `π₂`-pullback coordinate map of the product constant object is injective. -/
lemma productConstPullbackCoordπ₂_injective
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    Function.Injective (productConstPullbackCoordπ₂ K M) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let P := fiberConstModule K M
  let N := productFiberRankBoundN K M
  let hN := fiberConstModule_finrank_le K M
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  letI : Algebra (∀ i, K i) E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  change Function.Injective
    ((FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₂).comp
      (baseChange_assoc E.π₀ E.π₂ (productConstModule K M).M).toLinearMap)
  exact (FiniteProjectiveModule.piUniformBaseChangeCoord_injective K P N hN E.R₂).comp
    (baseChange_assoc E.π₀ E.π₂ (productConstModule K M).M).injective

/-- Standard `π₂`-pullback coordinates for `toConstantLinearMap` on a chosen
product generator. -/
private lemma toConstantLinearMap_generator_pullbackπ₂_coord
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j c : Fin (productFiberRankBoundN K M)) :
    letI : Algebra (∀ i, K i) (realC (∀ i, K i)).R₁ :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra;
    productConstPullbackCoordπ₂ K M
      ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
        (realC (∀ i, K i)).π₂.toAlgebra;
        (1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁]
          (toConstantLinearMap K M (productFiberGenerator K M j)))) c =
    (realC (∀ i, K i)).π₂ (trivializedCoordLift K M (productFiberGenerator K M j) c) := by
  let R := (realC (∀ i, K i)).R₁
  let S := (realC (∀ i, K i)).R₂
  let P := fiberConstModule K M
  let N := productFiberRankBoundN K M
  let hN := fiberConstModule_finrank_le K M
  let m := productFiberGenerator K M j
  let y := toConstantLinearMap K M m
  letI : Algebra (∀ i, K i) R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  letI : Algebra R S := (realC (∀ i, K i)).π₂.toAlgebra
  calc
    productConstPullbackCoordπ₂ K M ((1 : S) ⊗ₜ[R] y) c
        = (realC (∀ i, K i)).π₂
            (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN R y c) := by
          exact productConstPullbackCoordπ₂_one_tmul K M y c
    _ = (realC (∀ i, K i)).π₂ (trivializedCoordLift K M m c) := by
          have hbase := toConstantModuleElement_coord_apply K M m c
          change FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN R
              (toConstantModuleElement K M m) c = trivializedCoordLift K M m c at hbase
          dsimp [y]
          exact congrArg (realC (∀ i, K i)).π₂ hbase

/-- Standard `π₂`-pullback coordinates of the transition sum obtained by applying
`toConstantLinearMap` to the chosen generators. -/
private lemma productConstPullbackCoordπ₂_transition_sum_toConstant_generators
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j c : Fin (productFiberRankBoundN K M)) :
    let R := (realC (∀ i, K i)).R₁;
    let S := (realC (∀ i, K i)).R₂;
    letI : Algebra (∀ i, K i) R :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra;
    letI : Algebra R S := (realC (∀ i, K i)).π₂.toAlgebra;
    productConstPullbackCoordπ₂ K M
      (∑ k : Fin (productFiberRankBoundN K M),
        generatorTransitionCoeff K M j k •
          ((1 : S) ⊗ₜ[R] (toConstantLinearMap K M (productFiberGenerator K M k)))) c =
    ∑ k : Fin (productFiberRankBoundN K M),
      generatorTransitionCoeff K M j k *
        (realC (∀ i, K i)).π₂
          (trivializedCoordLift K M (productFiberGenerator K M k) c) := by
  let R := (realC (∀ i, K i)).R₁
  let S := (realC (∀ i, K i)).R₂
  letI : Algebra (∀ i, K i) R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  letI : Algebra R S := (realC (∀ i, K i)).π₂.toAlgebra
  change productConstPullbackCoordπ₂ K M
      (∑ k : Fin (productFiberRankBoundN K M),
        generatorTransitionCoeff K M j k •
          ((1 : S) ⊗ₜ[R] (toConstantLinearMap K M (productFiberGenerator K M k)))) c =
    ∑ k : Fin (productFiberRankBoundN K M),
      generatorTransitionCoeff K M j k *
        (realC (∀ i, K i)).π₂
          (trivializedCoordLift K M (productFiberGenerator K M k) c)
  rw [map_sum]
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  change (generatorTransitionCoeff K M j k •
      productConstPullbackCoordπ₂ K M ((1 : S) ⊗ₜ[R]
        (toConstantLinearMap K M (productFiberGenerator K M k)))) c = _
  rw [Pi.smul_apply]
  change generatorTransitionCoeff K M j k *
      productConstPullbackCoordπ₂ K M ((1 : S) ⊗ₜ[R]
        (toConstantLinearMap K M (productFiberGenerator K M k))) c = _
  rw [toConstantLinearMap_generator_pullbackπ₂_coord]

/-- Applying the base-changed `toConstantLinearMap` to the descent translate of a
chosen generator gives the transition sum of the images of the generators. -/
private lemma toConstantLinearMap_phi_generator_eq_transition_sum
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j : Fin (productFiberRankBoundN K M)) :
    let R := (realC (∀ i, K i)).R₁;
    let S := (realC (∀ i, K i)).R₂;
    letI : Algebra R S := (realC (∀ i, K i)).π₂.toAlgebra;
    (LinearMap.baseChange S (toConstantLinearMap K M))
      (M.φ ((letI : Algebra R S := (realC (∀ i, K i)).π₁.toAlgebra;
        (1 : S) ⊗ₜ[R] productFiberGenerator K M j))) =
    ∑ k : Fin (productFiberRankBoundN K M),
      generatorTransitionCoeff K M j k •
        ((1 : S) ⊗ₜ[R] (toConstantLinearMap K M (productFiberGenerator K M k))) := by
  let R := (realC (∀ i, K i)).R₁
  let S := (realC (∀ i, K i)).R₂
  letI : Algebra R S := (realC (∀ i, K i)).π₂.toAlgebra
  change (LinearMap.baseChange S (toConstantLinearMap K M))
      (M.φ ((letI : Algebra R S := (realC (∀ i, K i)).π₁.toAlgebra;
        (1 : S) ⊗ₜ[R] productFiberGenerator K M j))) =
    ∑ k : Fin (productFiberRankBoundN K M),
      generatorTransitionCoeff K M j k •
        ((1 : S) ⊗ₜ[R] (toConstantLinearMap K M (productFiberGenerator K M k)))
  rw [← productPullback₂Presentation_generatorTransitionVector K M j]
  rw [productPullback₂Presentation_eq_sum_generators]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  congr 1

/-- The lifted generator coordinates satisfy the forward descent transition
relations over the product Novikov ring. -/
private lemma trivializedCoordLift_forward_transition
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j c : Fin (productFiberRankBoundN K M)) :
    (realC (∀ i, K i)).π₁ (trivializedCoordLift K M (productFiberGenerator K M j) c) =
      ∑ k : Fin (productFiberRankBoundN K M),
        generatorTransitionCoeff K M j k *
          (realC (∀ i, K i)).π₂
            (trivializedCoordLift K M (productFiberGenerator K M k) c) := by
  apply (coeffwisePiRingHom_injective (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K)
  change (coeffwiseRealCHom K).f₂
      ((realC (∀ i, K i)).π₁ (trivializedCoordLift K M (productFiberGenerator K M j) c)) =
    (coeffwiseRealCHom K).f₂
      (∑ k : Fin (productFiberRankBoundN K M),
        generatorTransitionCoeff K M j k *
          (realC (∀ i, K i)).π₂
            (trivializedCoordLift K M (productFiberGenerator K M k) c))
  funext i
  rw [CosimplicialRingHom.map_π₁_apply]
  rw [map_sum]
  change (realC (K i)).π₁
      ((coeffwiseRealCHom K).f₁
        (trivializedCoordLift K M (productFiberGenerator K M j) c) i) =
    (∑ k : Fin (productFiberRankBoundN K M),
      (coeffwiseRealCHom K).f₂
        (generatorTransitionCoeff K M j k *
          (realC (∀ i, K i)).π₂
            (trivializedCoordLift K M (productFiberGenerator K M k) c))) i
  rw [show (∑ k : Fin (productFiberRankBoundN K M),
      (coeffwiseRealCHom K).f₂
        (generatorTransitionCoeff K M j k *
          (realC (∀ i, K i)).π₂
            (trivializedCoordLift K M (productFiberGenerator K M k) c))) i =
      ∑ k : Fin (productFiberRankBoundN K M),
        (coeffwiseRealCHom K).f₂
          (generatorTransitionCoeff K M j k *
            (realC (∀ i, K i)).π₂
              (trivializedCoordLift K M (productFiberGenerator K M k) c)) i by
    exact Finset.sum_apply i Finset.univ _]
  rw [coeffwiseRealCHom_f₁_trivializedCoordLift_apply]
  rw [generatorForwardCoordinateEquality]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul]
  change (show (realC (K i)).R₂ from coeffwiseEvalRingHom
        (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
        (generatorTransitionCoeff K M j k)) *
      (realC (K i)).π₂ (trivializedCoordFamily K M (productFiberGenerator K M k) c i) =
    ((coeffwiseRealCHom K).f₂ (generatorTransitionCoeff K M j k) i) *
      ((coeffwiseRealCHom K).f₂
        ((realC (∀ i, K i)).π₂
          (trivializedCoordLift K M (productFiberGenerator K M k) c)) i)
  rw [CosimplicialRingHom.map_π₂_apply]
  change (show (realC (K i)).R₂ from coeffwiseEvalRingHom
        (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
        (generatorTransitionCoeff K M j k)) *
      (realC (K i)).π₂ (trivializedCoordFamily K M (productFiberGenerator K M k) c i) =
    (show (realC (K i)).R₂ from coeffwiseEvalRingHom
        (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
        (generatorTransitionCoeff K M j k)) *
      (realC (K i)).π₂
        ((coeffwiseRealCHom K).f₁
          (trivializedCoordLift K M (productFiberGenerator K M k) c) i)
  rw [coeffwiseRealCHom_f₁_trivializedCoordLift_apply]

/-- Standard `π₂`-pullback coordinates for the right side of the descent square
on a chosen product generator. -/
lemma toConstantLinearMap_phi_generator_pullbackπ₂_coord
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j c : Fin (productFiberRankBoundN K M)) :
    let R := (realC (∀ i, K i)).R₁;
    let S := (realC (∀ i, K i)).R₂;
    letI : Algebra R S := (realC (∀ i, K i)).π₂.toAlgebra;
    productConstPullbackCoordπ₂ K M
      ((LinearMap.baseChange S (toConstantLinearMap K M))
        (M.φ ((letI : Algebra R S := (realC (∀ i, K i)).π₁.toAlgebra;
          (1 : S) ⊗ₜ[R] productFiberGenerator K M j)))) c =
    (realC (∀ i, K i)).π₁ (trivializedCoordLift K M (productFiberGenerator K M j) c) := by
  let R := (realC (∀ i, K i)).R₁
  let S := (realC (∀ i, K i)).R₂
  letI : Algebra R S := (realC (∀ i, K i)).π₂.toAlgebra
  change productConstPullbackCoordπ₂ K M
      ((LinearMap.baseChange S (toConstantLinearMap K M))
        (M.φ ((letI : Algebra R S := (realC (∀ i, K i)).π₁.toAlgebra;
          (1 : S) ⊗ₜ[R] productFiberGenerator K M j)))) c =
    (realC (∀ i, K i)).π₁ (trivializedCoordLift K M (productFiberGenerator K M j) c)
  rw [toConstantLinearMap_phi_generator_eq_transition_sum]
  rw [productConstPullbackCoordπ₂_transition_sum_toConstant_generators]
  exact (trivializedCoordLift_forward_transition K M j c).symm


attribute [local irreducible] FiniteProjectiveModule.piUniformBaseChangeCoord productConstPullbackCoordπ₂

/-- Standard `π₂`-pullback coordinates of the left side of the descent square
for `toConstantLinearMap` on a chosen generator. -/
private lemma toConstantLinearMap_generator_pullbackπ₂_constant_φ_coord
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j c : Fin (productFiberRankBoundN K M)) :
    let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i);
    letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule;
    letI : Module.Finite E.R₀ (productConstModule K M).M := (productConstModule K M).instFinite;
    letI : Module.Projective E.R₀ (productConstModule K M).M := (productConstModule K M).instProjective;
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra;
    letI : Algebra (∀ i, K i) E.R₁ := E.π₀.toAlgebra;
    productConstPullbackCoordπ₂ K M
      ((constantDescentDatum E (productConstModule K M).M).φ
        ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
          (1 : E.R₂) ⊗ₜ[E.R₁]
            (toConstantLinearMap K M (productFiberGenerator K M j))))) c =
    (realC (∀ i, K i)).π₁
      (trivializedCoordLift K M (productFiberGenerator K M j) c) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let P := fiberConstModule K M
  let N := productFiberRankBoundN K M
  let hN := fiberConstModule_finrank_le K M
  let m := productFiberGenerator K M j
  let y := toConstantLinearMap K M m
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Module.Finite E.R₀ (productConstModule K M).M := (productConstModule K M).instFinite
  letI : Module.Projective E.R₀ (productConstModule K M).M := (productConstModule K M).instProjective
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (∀ i, K i) E.R₁ := E.π₀.toAlgebra
  calc
    productConstPullbackCoordπ₂ K M
        ((constantDescentDatum E (productConstModule K M).M).φ
          ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
            (1 : E.R₂) ⊗ₜ[E.R₁] y))) c
        = (realC (∀ i, K i)).π₁
            (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁ y c) := by
          exact productConstPullbackCoordπ₂_constant_φ_one_tmul K M y c
    _ = (realC (∀ i, K i)).π₁ (trivializedCoordLift K M m c) := by
          have hbase := toConstantModuleElement_coord_apply K M m c
          change FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁
              (toConstantModuleElement K M m) c = trivializedCoordLift K M m c at hbase
          dsimp [y]
          exact congrArg (realC (∀ i, K i)).π₁ hbase

/-- Generator-level descent compatibility for `toConstantLinearMap`, stated in
the standard `π₂`-pullback target. -/
private lemma toConstantLinearMap_generator_commute
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j : Fin (productFiberRankBoundN K M)) :
    let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i);
    let R := (realC (∀ i, K i)).R₁;
    let S := (realC (∀ i, K i)).R₂;
    letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule;
    letI : Module.Finite E.R₀ (productConstModule K M).M := (productConstModule K M).instFinite;
    letI : Module.Projective E.R₀ (productConstModule K M).M := (productConstModule K M).instProjective;
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra;
    letI : Algebra (∀ i, K i) E.R₁ := E.π₀.toAlgebra;
    ((constantDescentDatum E (productConstModule K M).M).φ
      ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
        (1 : E.R₂) ⊗ₜ[E.R₁]
          (toConstantLinearMap K M (productFiberGenerator K M j))))) =
    (letI : Algebra R S := (realC (∀ i, K i)).π₂.toAlgebra;
      (LinearMap.baseChange S (toConstantLinearMap K M))
        (M.φ ((letI : Algebra R S := (realC (∀ i, K i)).π₁.toAlgebra;
          (1 : S) ⊗ₜ[R] productFiberGenerator K M j)))) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let R := (realC (∀ i, K i)).R₁
  let S := (realC (∀ i, K i)).R₂
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Module.Finite E.R₀ (productConstModule K M).M := (productConstModule K M).instFinite
  letI : Module.Projective E.R₀ (productConstModule K M).M := (productConstModule K M).instProjective
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (∀ i, K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra R S := (realC (∀ i, K i)).π₂.toAlgebra
  apply productConstPullbackCoordπ₂_injective K M
  ext c
  calc
    productConstPullbackCoordπ₂ K M
        ((constantDescentDatum E (productConstModule K M).M).φ
          ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
            (1 : E.R₂) ⊗ₜ[E.R₁]
              (toConstantLinearMap K M (productFiberGenerator K M j))))) c =
        (realC (∀ i, K i)).π₁
          (trivializedCoordLift K M (productFiberGenerator K M j) c) := by
          exact toConstantLinearMap_generator_pullbackπ₂_constant_φ_coord K M j c
    _ = productConstPullbackCoordπ₂ K M
        ((LinearMap.baseChange S (toConstantLinearMap K M))
          (M.φ ((letI : Algebra R S := (realC (∀ i, K i)).π₁.toAlgebra;
            (1 : S) ⊗ₜ[R] productFiberGenerator K M j)))) c := by
          exact (toConstantLinearMap_phi_generator_pullbackπ₂_coord K M j c).symm

omit [∀ i, IsAlgClosed (K i)] in
/-- Linear maps out of the first pullback agree when they agree on the chosen
product generators. -/
private lemma productPullback₁_linearMap_ext
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    {N : Type v} [AddCommGroup N] [Module (realC (∀ i, K i)).R₁ N]
    (L Rmap : π₁s (realC (∀ i, K i)) M.M →ₗ[(realC (∀ i, K i)).R₂]
      π₂s (realC (∀ i, K i)) N)
    (h : ∀ j : Fin (productFiberRankBoundN K M),
      L ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
          (realC (∀ i, K i)).π₁.toAlgebra;
        (1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁]
          productFiberGenerator K M j)) =
      Rmap ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
          (realC (∀ i, K i)).π₁.toAlgebra;
        (1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁]
          productFiberGenerator K M j))) :
    L = Rmap := by
  apply (LinearMap.cancel_right (productPullback₁Presentation_surjective K M)).mp
  apply LinearMap.ext
  intro w
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [productPullback₁Presentation_eq_sum_generators]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_smul, h]

/-- The target object's descent isomorphism is definitionally the constant one. -/
private lemma productConstTarget_φ
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i);
    letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule;
    letI : Module.Finite E.R₀ (productConstModule K M).M := (productConstModule K M).instFinite;
    letI : Module.Projective E.R₀ (productConstModule K M).M := (productConstModule K M).instProjective;
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra;
    ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
      (productConstModule K M)).φ =
      (constantDescentDatum E (productConstModule K M).M).φ := rfl

attribute [local irreducible] productPullback₁Presentation productConstModule constantDescentDatum

/-- Left linear map in the descent-compatibility square for `toConstantLinearMap`. -/
private noncomputable def toConstantLinearMapPullbackLeft
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    π₁s (realC (∀ i, K i)) M.M →ₗ[(realC (∀ i, K i)).R₂]
      π₂s (realC (∀ i, K i))
        (((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
          (productConstModule K M)).M) :=
  (((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
      (productConstModule K M)).φ.toLinearMap).comp
    (letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
      (realC (∀ i, K i)).π₁.toAlgebra;
      LinearMap.baseChange (realC (∀ i, K i)).R₂ (toConstantLinearMap K M))

/-- Right linear map in the descent-compatibility square for `toConstantLinearMap`. -/
private noncomputable def toConstantLinearMapPullbackRight
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    π₁s (realC (∀ i, K i)) M.M →ₗ[(realC (∀ i, K i)).R₂]
      π₂s (realC (∀ i, K i))
        (((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
          (productConstModule K M)).M) :=
  (letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
    (realC (∀ i, K i)).π₂.toAlgebra;
    LinearMap.baseChange (realC (∀ i, K i)).R₂ (toConstantLinearMap K M)).comp
      M.φ.toLinearMap

attribute [local irreducible]
  toConstantLinearMap
  productFiberGenerator
  productFiberRankBoundN
  LinearMap.baseChange

/-- Descent compatibility of `toConstantLinearMap` on all `π₁`-pullback
elements. -/
private lemma toConstantLinearMap_commute_φ
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    toConstantLinearMapPullbackLeft K M = toConstantLinearMapPullbackRight K M := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let R := (realC (∀ i, K i)).R₁
  let S := (realC (∀ i, K i)).R₂
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Module.Finite E.R₀ (productConstModule K M).M := (productConstModule K M).instFinite
  letI : Module.Projective E.R₀ (productConstModule K M).M := (productConstModule K M).instProjective
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (∀ i, K i) E.R₁ := E.π₀.toAlgebra
  change
    (((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (productConstModule K M)).φ.toLinearMap).comp
      (letI : Algebra R S := (realC (∀ i, K i)).π₁.toAlgebra;
        LinearMap.baseChange S (toConstantLinearMap K M)) =
    (letI : Algebra R S := (realC (∀ i, K i)).π₂.toAlgebra;
      LinearMap.baseChange S (toConstantLinearMap K M)).comp M.φ.toLinearMap
  apply productPullback₁_linearMap_ext K M
  intro j
  change ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
      (productConstModule K M)).φ
      ((letI : Algebra R S := (realC (∀ i, K i)).π₁.toAlgebra;
        LinearMap.baseChange S (toConstantLinearMap K M))
        ((letI : Algebra R S := (realC (∀ i, K i)).π₁.toAlgebra;
          (1 : S) ⊗ₜ[R] productFiberGenerator K M j))) =
    (letI : Algebra R S := (realC (∀ i, K i)).π₂.toAlgebra;
      LinearMap.baseChange S (toConstantLinearMap K M))
        (M.φ ((letI : Algebra R S := (realC (∀ i, K i)).π₁.toAlgebra;
          (1 : S) ⊗ₜ[R] productFiberGenerator K M j)))
  letI : Algebra R S := (realC (∀ i, K i)).π₁.toAlgebra
  rw [productConstTarget_φ K M]
  rw [LinearMap.baseChange_tmul]
  exact toConstantLinearMap_generator_commute K M j

/-- The morphism from a product descent datum to the constant object built from
its lifted fiber coordinates. -/
noncomputable def toConstant
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    M ⟶ ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
      (productConstModule K M)) where
  toLinearMap := toConstantLinearMap K M
  commute_φ := by
    change toConstantLinearMapPullbackLeft K M = toConstantLinearMapPullbackRight K M
    exact toConstantLinearMap_commute_φ K M

end

end Novikov.Descent
