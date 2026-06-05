import Novikov.Descent.Product.Fiber

/-!
# Product-constant pullback coordinate compatibility

This file defines finite-free coordinates on the `π₂`-pullback of the product
constant object and isolates the expensive mixed-face coordinate calculation.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract
open scoped BigOperators

namespace Novikov.Descent

noncomputable section

universe u

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)] [∀ i, IsAlgClosed (K i)]

/-- Finite-free coordinates on the `π₂`-pullback of the product constant object. -/
noncomputable def productConstPullbackCoordπ₂
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    π₂s (realC (∀ i, K i))
      (((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (productConstModule K M)).M) →ₗ[(realC (∀ i, K i)).R₂]
      (Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₂) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let P := fiberConstModule K M
  let N := productFiberRankBoundN K M
  let hN := fiberConstModule_finrank_le K M
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  letI : Algebra (∀ i, K i) E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  change (E.R₂ ⊗[E.R₁] (E.R₁ ⊗[E.R₀] (productConstModule K M).M)) →ₗ[E.R₂]
      (Fin N → E.R₂)
  exact (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₂).comp
    (baseChange_assoc E.π₀ E.π₂ (productConstModule K M).M).toLinearMap

/-- The `π₂`-pullback coordinate of `1 ⊗ y` is obtained by applying `π₂` to the
coordinate of `y`. -/
lemma productConstPullbackCoordπ₂_one_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (y : ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (productConstModule K M)).M)
    (c : Fin (productFiberRankBoundN K M)) :
    letI : Algebra (∀ i, K i) (realC (∀ i, K i)).R₁ :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
    productConstPullbackCoordπ₂ K M
      ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
          (realC (∀ i, K i)).π₂.toAlgebra
        (1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁] y)) c =
    (realC (∀ i, K i)).π₂
      (FiniteProjectiveModule.piUniformBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M)
        (realC (∀ i, K i)).R₁ y c) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let P := fiberConstModule K M
  let N := productFiberRankBoundN K M
  let hN := fiberConstModule_finrank_le K M
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (∀ i, K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  letI : Algebra (∀ i, K i) E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  change FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₂
      ((baseChange_assoc E.π₀ E.π₂ (productConstModule K M).M)
        ((1 : E.R₂) ⊗ₜ[E.R₁] y)) c =
    E.π₂ (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁ y c)
  have h := FiniteProjectiveModule.piUniformBaseChangeCoord_baseChange_assoc K P N hN
    E.R₁ E.R₂ E.π₀ E.π₂ y
  exact congrFun h c

section ProductConstPullbackCoordPi2Constant

attribute [local irreducible]
  FiniteProjectiveModule.piUniformBaseChangeCoord
  productConstPullbackCoordπ₂
  baseChange_assoc

/-- Standard `π₂`-pullback coordinates of the constant descent isomorphism
applied to `1 ⊗ y`. -/
lemma productConstPullbackCoordπ₂_constant_φ_one_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (y : ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (productConstModule K M)).M)
    (c : Fin (productFiberRankBoundN K M)) :
    let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i);
    let P := fiberConstModule K M;
    let N := productFiberRankBoundN K M;
    let hN := fiberConstModule_finrank_le K M;
    letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule;
    letI : Module.Finite E.R₀ (productConstModule K M).M := (productConstModule K M).instFinite;
    letI : Module.Projective E.R₀ (productConstModule K M).M := (productConstModule K M).instProjective;
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra;
    letI : Algebra (∀ i, K i) E.R₁ := E.π₀.toAlgebra;
    productConstPullbackCoordπ₂ K M
      ((constantDescentDatum E (productConstModule K M).M).φ
        ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
          (1 : E.R₂) ⊗ₜ[E.R₁] y))) c =
    E.π₁ (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁ y c) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let P := fiberConstModule K M
  let N := productFiberRankBoundN K M
  let hN := fiberConstModule_finrank_le K M
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Module.Finite E.R₀ (productConstModule K M).M := (productConstModule K M).instFinite
  letI : Module.Projective E.R₀ (productConstModule K M).M := (productConstModule K M).instProjective
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra (∀ i, K i) E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
  letI : Module E.R₁ (realC (∀ i, K i)).R₂ := by
    change Module E.R₁ E.R₂
    infer_instance
  letI : Algebra E.R₀ E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  letI : Algebra (∀ i, K i) E.R₂ := (E.π₂.comp E.π₀).toAlgebra
  let Y := E.R₁ ⊗[E.R₀] (productConstModule K M).M
  change Y at y
  let left : Y → E.R₂ := fun y =>
    productConstPullbackCoordπ₂ K M
      ((constantDescentDatum E (productConstModule K M).M).φ
        ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
          (1 : E.R₂) ⊗ₜ[E.R₁] y))) c
  let right : Y → E.R₂ := fun y =>
    E.π₁ (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁ y c)
  change left y = right y
  induction y using TensorProduct.induction_on with
  | zero =>
      have hleft0 : left 0 = 0 := by
        dsimp [left]
        have hφzero : (constantDescentDatum E (productConstModule K M).M).φ
            ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
              (1 : E.R₂) ⊗ₜ[E.R₁] (0 : Y))) = 0 := by
          letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
          exact (congrArg (fun q => (constantDescentDatum E (productConstModule K M).M).φ q)
            (TensorProduct.tmul_zero (R := E.R₁) (M := E.R₂)
              (N := Y) (1 : E.R₂))).trans
            (map_zero (constantDescentDatum E (productConstModule K M).M).φ)
        rw [hφzero]
        exact congrFun (map_zero (productConstPullbackCoordπ₂ K M)) c
      have hright0 : right 0 = 0 := by
        dsimp [right]
        have hcoord0 := congrFun
          (map_zero (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁)) c
        calc
          E.π₁ (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁ 0 c) =
              E.π₁ (0 : E.R₁) := by
                exact congrArg E.π₁ hcoord0
          _ = 0 := map_zero E.π₁
      rw [hleft0, hright0]
  | add y z hy hz =>
      have hleft_add : left (y + z) = left y + left z := by
        dsimp [left]
        have hφadd : (constantDescentDatum E (productConstModule K M).M).φ
            ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
              (1 : E.R₂) ⊗ₜ[E.R₁] (y + z))) =
            (constantDescentDatum E (productConstModule K M).M).φ
              ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
                (1 : E.R₂) ⊗ₜ[E.R₁] y)) +
            (constantDescentDatum E (productConstModule K M).M).φ
              ((letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
                (1 : E.R₂) ⊗ₜ[E.R₁] z)) := by
          letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
          exact (congrArg (fun q => (constantDescentDatum E (productConstModule K M).M).φ q)
            (TensorProduct.tmul_add (R := E.R₁) (M := E.R₂)
              (N := Y) (1 : E.R₂) y z)).trans
            (map_add (constantDescentDatum E (productConstModule K M).M).φ _ _)
        rw [hφadd]
        exact congrFun (map_add (productConstPullbackCoordπ₂ K M) _ _) c
      have hright_add : right (y + z) = right y + right z := by
        dsimp [right]
        have hcoordadd := congrFun
          (map_add (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁) y z) c
        calc
          E.π₁ (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁ (y + z) c) =
              E.π₁ ((FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁ y +
                FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁ z) c) := by
                exact congrArg E.π₁ hcoordadd
          _ = E.π₁ (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁ y c) +
              E.π₁ (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁ z c) := by
                rw [Pi.add_apply, map_add]
      rw [hleft_add, hright_add, hy, hz]
  | tmul s p =>
      dsimp [left, right]
      rw [constantDescentDatum_φ_tmul]
      change productConstPullbackCoordπ₂ K M
          (((E.π₁ s * (1 : E.R₂)) : E.R₂) ⊗ₜ[E.R₁]
            ((1 : E.R₁) ⊗ₜ[E.R₀] p)) c =
        E.π₁ (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁
          (s ⊗ₜ[∀ i, K i] p) c)
      rw [mul_one]
      unfold productConstPullbackCoordπ₂
      letI : Module E.R₀ (FiniteProjectiveModule.piOfUniformFinrank K P N hN).M := by
        change Module (∀ i, K i) (FiniteProjectiveModule.piOfUniformFinrank K P N hN).M
        infer_instance
      change FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₂
          ((baseChange_assoc E.π₀ E.π₂ (FiniteProjectiveModule.piOfUniformFinrank K P N hN).M)
            ((E.π₁ s) ⊗ₜ[E.R₁] ((1 : E.R₁) ⊗ₜ[∀ i, K i] p))) c =
        E.π₁ (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN E.R₁
          (s ⊗ₜ[∀ i, K i] p) c)
      have hassocCoord :=
        FiniteProjectiveModule.piUniformBaseChangeCoord_baseChange_assoc_tmul_apply
          K P N hN E.R₁ E.R₂ E.π₀ E.π₂ (E.π₁ s)
          ((1 : E.R₁) ⊗ₜ[∀ i, K i] p) c
      refine hassocCoord.trans ?_
      rw [FiniteProjectiveModule.piUniformBaseChangeCoord_tmul]
      rw [FiniteProjectiveModule.piUniformBaseChangeCoord_tmul]
      change E.π₁ s * E.π₂
          (((FiniteProjectiveModule.piUniformIntoFree K P N hN p c) : (∀ i, K i)) •
            (1 : E.R₁)) =
        E.π₁ (((FiniteProjectiveModule.piUniformIntoFree K P N hN p c) : (∀ i, K i)) • s)
      simp only [Algebra.smul_def]
      rw [mul_one]
      rw [map_mul]
      have hcomp := congrArg (fun f : E.R₀ →+* E.R₂ =>
          f (FiniteProjectiveModule.piUniformIntoFree K P N hN p c))
        E.π₁_π₀_eq_π₂_π₀
      change E.π₁ s * E.π₂ (E.π₀ (FiniteProjectiveModule.piUniformIntoFree K P N hN p c)) =
        E.π₁ (E.π₀ (FiniteProjectiveModule.piUniformIntoFree K P N hN p c)) * E.π₁ s
      change E.π₁ (E.π₀ (FiniteProjectiveModule.piUniformIntoFree K P N hN p c)) =
        E.π₂ (E.π₀ (FiniteProjectiveModule.piUniformIntoFree K P N hN p c)) at hcomp
      rw [← hcomp]
      ring

end ProductConstPullbackCoordPi2Constant

end

end Novikov.Descent
