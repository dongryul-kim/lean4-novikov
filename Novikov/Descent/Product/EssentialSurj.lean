import Novikov.Descent.Product.SupportEstimate

/-!
# Essential-surjectivity construction for products

This file begins the construction of the comparison from an arbitrary descent
object over a product of algebraically closed fields to the constant object
attached to the product of its fiber trivializations.  The first step is to lift
the product fiber-trivialized finite-free coordinates, whose coefficientwise
range was proved in `SupportEstimate.lean`, back to Novikov series over the
product coefficient ring.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract
open scoped BigOperators

namespace Novikov.Descent

noncomputable section

universe u

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)] [∀ i, IsAlgClosed (K i)]

/-- Lift one trivialized coordinate from the product of fiber Novikov rings to the
Novikov ring over the product coefficient ring. -/
noncomputable def trivializedCoordLift
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) (c : Fin (productFiberRankBoundN K M)) : (realC (∀ i, K i)).R₁ :=
  coeffwiseRangeLift K (trivializedCoordFamily K M m c)
    (trivializedCoordinatesInCoeffwiseRange K M m c)

@[simp]
private lemma coeffwiseRealCHom_f₁_trivializedCoordLift
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) (c : Fin (productFiberRankBoundN K M)) :
    (coeffwiseRealCHom K).f₁ (trivializedCoordLift K M m c) =
      fun i => trivializedCoordFamily K M m c i := by
  exact coeffwiseRangeLift_spec K (trivializedCoordFamily K M m c)
    (trivializedCoordinatesInCoeffwiseRange K M m c)

@[simp]
lemma coeffwiseRealCHom_f₁_trivializedCoordLift_apply
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) (c : Fin (productFiberRankBoundN K M)) (i : I) :
    (coeffwiseRealCHom K).f₁ (trivializedCoordLift K M m c) i =
      trivializedCoordFamily K M m c i := by
  rw [coeffwiseRealCHom_f₁_trivializedCoordLift]

/-- Lifted finite-free coordinate vector of the product fiber trivialization. -/
private noncomputable def trivializedCoordLiftVector
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) : Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₁ :=
  fun c => trivializedCoordLift K M m c

@[simp]
private lemma trivializedCoordLiftVector_apply
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) (c : Fin (productFiberRankBoundN K M)) :
    trivializedCoordLiftVector K M m c = trivializedCoordLift K M m c := rfl

/-- After coefficientwise base change, the lifted coordinate vector is exactly the
finite-free coordinate vector of the product fiber trivialization. -/
private lemma coeffwiseRealCHom_f₁_trivializedCoordLiftVector
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) :
    (fun c => (coeffwiseRealCHom K).f₁ (trivializedCoordLiftVector K M m c)) =
      prodTrivializationCoord K M
        ((letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ :=
            (coeffwiseRealCHom K).f₁.toAlgebra
          (1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m)) := by
  ext c
  funext i
  rw [trivializedCoordLiftVector_apply, coeffwiseRealCHom_f₁_trivializedCoordLift_apply]
  rw [trivializedCoordFamily_apply]

/-- Trivialized coordinate families are additive in the descent-module element. -/
private lemma trivializedCoordFamily_add
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m n : M.M) (c : Fin (productFiberRankBoundN K M)) :
    trivializedCoordFamily K M (m + n) c =
      trivializedCoordFamily K M m c + trivializedCoordFamily K M n c := by
  letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ :=
    (coeffwiseRealCHom K).f₁.toAlgebra
  change prodTrivializationCoord K M
      ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] (m + n)) c =
    prodTrivializationCoord K M
        ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m) c +
      prodTrivializationCoord K M
        ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] n) c
  rw [TensorProduct.tmul_add]
  exact congrFun (map_add (prodTrivializationCoord K M)
    ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m)
    ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] n)) c

/-- Trivialized coordinate families are linear for scalars in the product
Novikov ring. -/
private lemma trivializedCoordFamily_smul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (r : (realC (∀ i, K i)).R₁) (m : M.M) (c : Fin (productFiberRankBoundN K M)) :
    trivializedCoordFamily K M (r • m) c =
      fun i => (coeffwiseRealCHom K).f₁ r i * trivializedCoordFamily K M m c i := by
  letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ :=
    (coeffwiseRealCHom K).f₁.toAlgebra
  change prodTrivializationCoord K M
      ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] (r • m)) c =
    (coeffwiseRealCHom K).f₁ r * prodTrivializationCoord K M
      ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m) c
  rw [TensorProduct.tmul_smul]
  change prodTrivializationCoord K M
      (((coeffwiseRealCHom K).f₁ r • (1 : (prodRealC K).R₁)) ⊗ₜ[(realC (∀ i, K i)).R₁] m) c =
    (coeffwiseRealCHom K).f₁ r * prodTrivializationCoord K M
      ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m) c
  rw [← TensorProduct.smul_tmul']
  exact congrFun (map_smul (prodTrivializationCoord K M) ((coeffwiseRealCHom K).f₁ r)
    ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m)) c

/-- The lifted coordinates are additive. -/
private lemma trivializedCoordLift_add
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m n : M.M) (c : Fin (productFiberRankBoundN K M)) :
    trivializedCoordLift K M (m + n) c =
      trivializedCoordLift K M m c + trivializedCoordLift K M n c := by
  apply (coeffwisePiRingHom_injective (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K)
  change (coeffwiseRealCHom K).f₁ (trivializedCoordLift K M (m + n) c) =
    (coeffwiseRealCHom K).f₁ (trivializedCoordLift K M m c + trivializedCoordLift K M n c)
  rw [map_add]
  funext i
  change (coeffwiseRealCHom K).f₁ (trivializedCoordLift K M (m + n) c) i =
    ((coeffwiseRealCHom K).f₁ (trivializedCoordLift K M m c) +
      (coeffwiseRealCHom K).f₁ (trivializedCoordLift K M n c)) i
  rw [coeffwiseRealCHom_f₁_trivializedCoordLift_apply]
  change trivializedCoordFamily K M (m + n) c i =
    (coeffwiseRealCHom K).f₁ (trivializedCoordLift K M m c) i +
      (coeffwiseRealCHom K).f₁ (trivializedCoordLift K M n c) i
  rw [coeffwiseRealCHom_f₁_trivializedCoordLift_apply]
  rw [coeffwiseRealCHom_f₁_trivializedCoordLift_apply]
  exact congrFun (trivializedCoordFamily_add K M m n c) i

/-- The lifted coordinates are linear for scalars in the product Novikov ring. -/
private lemma trivializedCoordLift_smul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (r : (realC (∀ i, K i)).R₁) (m : M.M) (c : Fin (productFiberRankBoundN K M)) :
    trivializedCoordLift K M (r • m) c =
      r * trivializedCoordLift K M m c := by
  apply (coeffwisePiRingHom_injective (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K)
  change (coeffwiseRealCHom K).f₁ (trivializedCoordLift K M (r • m) c) =
    (coeffwiseRealCHom K).f₁ (r * trivializedCoordLift K M m c)
  rw [map_mul]
  funext i
  change (coeffwiseRealCHom K).f₁ (trivializedCoordLift K M (r • m) c) i =
    ((coeffwiseRealCHom K).f₁ r *
      (coeffwiseRealCHom K).f₁ (trivializedCoordLift K M m c)) i
  rw [coeffwiseRealCHom_f₁_trivializedCoordLift_apply]
  change trivializedCoordFamily K M (r • m) c i =
    (coeffwiseRealCHom K).f₁ r i *
      (coeffwiseRealCHom K).f₁ (trivializedCoordLift K M m c) i
  rw [coeffwiseRealCHom_f₁_trivializedCoordLift_apply]
  exact congrFun (trivializedCoordFamily_smul K M r m c) i

/-- The lifted coordinate vector, bundled as a linear map. -/
private noncomputable def trivializedCoordLiftLinearMap
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    M.M →ₗ[(realC (∀ i, K i)).R₁]
      (Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₁) where
  toFun := trivializedCoordLiftVector K M
  map_add' := by
    intro m n
    ext c
    exact trivializedCoordLift_add K M m n c
  map_smul' := by
    intro r m
    ext c
    exact trivializedCoordLift_smul K M r m c

/-- The underlying `R₁`-linear map from `M` to the candidate constant object. -/
noncomputable def toConstantLinearMap
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    M.M →ₗ[(realC (∀ i, K i)).R₁]
      ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (productConstModule K M)).M := by
  let R := (realC (∀ i, K i)).R₁
  let A := ∀ i, K i
  letI : Algebra A R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  change M.M →ₗ[R] R ⊗[A] (productConstModule K M).M
  exact (LinearMap.baseChange R
    (FiniteProjectiveModule.piUniformFromFree K (fiberConstModule K M)
      (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M))).comp
    ((TensorProduct.piScalarRight A R R (Fin (productFiberRankBoundN K M))).symm.toLinearMap.comp
      (trivializedCoordLiftLinearMap K M))

/-- Candidate underlying element of the constant object. -/
noncomputable def toConstantModuleElement
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) :
    ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
      (productConstModule K M)).M :=
  toConstantLinearMap K M m

/-- The coordinates of `toConstantModuleElement` are obtained by applying the
explicit coordinate projector to the lifted coordinate vector. -/
private lemma toConstantModuleElement_coord_projector
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) :
    letI : Algebra (∀ i, K i) (realC (∀ i, K i)).R₁ :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
    FiniteProjectiveModule.piUniformBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M)
      (realC (∀ i, K i)).R₁ (toConstantModuleElement K M m) =
    FiniteProjectiveModule.piUniformProjectorCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M)
      (realC (∀ i, K i)).R₁ (trivializedCoordLiftVector K M m) := by
  let R := (realC (∀ i, K i)).R₁
  let A := ∀ i, K i
  letI : Algebra A R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  change FiniteProjectiveModule.piUniformBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M) R
      (toConstantModuleElement K M m) =
    FiniteProjectiveModule.piUniformProjectorCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M) R
      (trivializedCoordLiftVector K M m)
  rfl

section LiftedProjector

attribute [local irreducible]
  FiniteProjectiveModule.piUniformProjectorCoord
  FiniteProjectiveModule.fiberBaseChangeProjectorCoord
  FiniteProjectiveModule.piUniformProjectorMatrix
  FiniteProjectiveModule.fiberProjectorMatrix

/-- The lifted coordinate vector is fixed by the explicit coordinate projector. -/
private lemma trivializedCoordLiftVector_projector
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) :
    letI : Algebra (∀ i, K i) (realC (∀ i, K i)).R₁ :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
    FiniteProjectiveModule.piUniformProjectorCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M)
      (realC (∀ i, K i)).R₁ (trivializedCoordLiftVector K M m) =
    trivializedCoordLiftVector K M m := by
  let R := (realC (∀ i, K i)).R₁
  let A := ∀ i, K i
  let N := productFiberRankBoundN K M
  let hN := fiberConstModule_finrank_le K M
  letI : Algebra A R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  change FiniteProjectiveModule.piUniformProjectorCoord K (fiberConstModule K M) N hN R
      (trivializedCoordLiftVector K M m) = trivializedCoordLiftVector K M m
  ext d
  apply (coeffwisePiRingHom_injective (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K)
  change (coeffwiseRealCHom K).f₁
      (FiniteProjectiveModule.piUniformProjectorCoord K (fiberConstModule K M) N hN R
        (trivializedCoordLiftVector K M m) d) =
    (coeffwiseRealCHom K).f₁ (trivializedCoordLiftVector K M m d)
  funext i
  letI : Algebra (K i) (realC (K i)).R₁ :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
  let x : (M.baseChange (coeffwiseRealCHom K)).M :=
    (letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ := (coeffwiseRealCHom K).f₁.toAlgebra
     (1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m)
  let w : Fin N → (prodRealC K).R₁ := prodTrivializationCoord K M x
  have hw_lift : (fun c => (coeffwiseRealCHom K).f₁ (trivializedCoordLiftVector K M m c)) = w := by
    dsimp [w, x]
    exact coeffwiseRealCHom_f₁_trivializedCoordLiftVector K M m
  let y : (realC (K i)).R₁ ⊗[K i] (fiberConstModule K M i).M := by
    change (fiberConstDescentDatum K M i).M
    exact (prodFiberTrivialization K M x) i
  have hfix := congrFun
    (FiniteProjectiveModule.fiberBaseChangeProjectorCoord_baseChangeCoord K (fiberConstModule K M)
      N hN i (realC (K i)).R₁ y) d
  calc
    (coeffwiseRealCHom K).f₁
        (FiniteProjectiveModule.piUniformProjectorCoord K (fiberConstModule K M) N hN R
          (trivializedCoordLiftVector K M m) d) i
        = FiniteProjectiveModule.fiberBaseChangeProjectorCoord K (fiberConstModule K M) N hN
            i (realC (K i)).R₁ (fun c => w c i) d := by
          rw [FiniteProjectiveModule.piUniformProjectorCoord_apply]
          rw [FiniteProjectiveModule.fiberBaseChangeProjectorCoord_apply]
          rw [map_sum]
          rw [show (∑ c : Fin N,
              (coeffwiseRealCHom K).f₁
                ((algebraMap A R)
                    (FiniteProjectiveModule.piUniformProjectorMatrix K (fiberConstModule K M) N hN d c) *
                  trivializedCoordLiftVector K M m c)) i =
              ∑ c : Fin N,
                ((coeffwiseRealCHom K).f₁
                  ((algebraMap A R)
                      (FiniteProjectiveModule.piUniformProjectorMatrix K (fiberConstModule K M) N hN d c) *
                    trivializedCoordLiftVector K M m c)) i by
            exact Finset.sum_apply i Finset.univ _]
          apply Finset.sum_congr rfl
          intro c _
          rw [map_mul]
          change (coeffwiseRealCHom K).f₁
              ((algebraMap A R)
                (FiniteProjectiveModule.piUniformProjectorMatrix K (fiberConstModule K M) N hN d c)) i *
              (coeffwiseRealCHom K).f₁ (trivializedCoordLiftVector K M m c) i =
            (algebraMap (K i) (realC (K i)).R₁)
                (FiniteProjectiveModule.fiberProjectorMatrix K (fiberConstModule K M) N hN i d c) *
              w c i
          congr 1
          · have halg : (coeffwiseRealCHom K).f₁
                ((algebraMap A R)
                  (FiniteProjectiveModule.piUniformProjectorMatrix K (fiberConstModule K M) N hN d c)) i =
              (algebraMap (K i) (realC (K i)).R₁)
                ((FiniteProjectiveModule.piUniformProjectorMatrix K (fiberConstModule K M) N hN d c) i) := by
              change coeffwiseEvalRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K i
                  (Novikov.algebraMapNovikov (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
                    (A := ∀ i, K i)
                    (FiniteProjectiveModule.piUniformProjectorMatrix K (fiberConstModule K M) N hN d c)) =
                Novikov.algebraMapNovikov (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (A := K i)
                  ((FiniteProjectiveModule.piUniformProjectorMatrix K (fiberConstModule K M) N hN d c) i)
              exact coeffwiseEvalRingHom_algebraMapNovikov
                (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K i
                (FiniteProjectiveModule.piUniformProjectorMatrix K (fiberConstModule K M)
                  N hN d c)
            rw [halg, FiniteProjectiveModule.piUniformProjectorMatrix_apply]
          · exact congrFun (congrFun hw_lift c) i
    _ = w d i := by
          simpa [w, y, prodTrivializationCoord, prodFiberConstCoord_apply] using hfix
    _ = (coeffwiseRealCHom K).f₁ (trivializedCoordLiftVector K M m d) i := by
          rw [← congrFun hw_lift d]

end LiftedProjector

/-- The candidate constant-object element has exactly the lifted coordinates. -/
private lemma toConstantModuleElement_coord
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) :
    letI : Algebra (∀ i, K i) (realC (∀ i, K i)).R₁ :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
    FiniteProjectiveModule.piUniformBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M)
      (realC (∀ i, K i)).R₁ (toConstantModuleElement K M m) =
    trivializedCoordLiftVector K M m := by
  let R := (realC (∀ i, K i)).R₁
  let A := ∀ i, K i
  letI : Algebra A R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  rw [toConstantModuleElement_coord_projector, trivializedCoordLiftVector_projector]

/-- Pointwise version of `toConstantModuleElement_coord`. -/
lemma toConstantModuleElement_coord_apply
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) (c : Fin (productFiberRankBoundN K M)) :
    letI : Algebra (∀ i, K i) (realC (∀ i, K i)).R₁ :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
    FiniteProjectiveModule.piUniformBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M)
      (realC (∀ i, K i)).R₁ (toConstantModuleElement K M m) c =
    trivializedCoordLift K M m c := by
  exact congrFun (toConstantModuleElement_coord K M m) c

/-- After coefficientwise base change, the candidate constant-object element has
coordinates equal to the product fiber trivialization of `m`. -/
private lemma toConstantModuleElement_prod_coord
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) :
    letI : Algebra (∀ i, K i) (realC (∀ i, K i)).R₁ :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
    letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ :=
      (coeffwiseRealCHom K).f₁.toAlgebra
    letI : Algebra (∀ i, K i) (prodRealC K).R₁ := ((coeffwiseRealCHom K).f₁.comp
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀).toAlgebra
    letI : IsScalarTower (∀ i, K i) (realC (∀ i, K i)).R₁ (prodRealC K).R₁ :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    FiniteProjectiveModule.piUniformBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M) (prodRealC K).R₁
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange (∀ i, K i)
        (realC (∀ i, K i)).R₁ (prodRealC K).R₁ (prodRealC K).R₁
        (productConstModule K M).M)
        ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁]
          toConstantModuleElement K M m)) =
    prodTrivializationCoord K M
      ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m) := by
  let R := (realC (∀ i, K i)).R₁
  let T := (prodRealC K).R₁
  letI : Algebra (∀ i, K i) R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  letI : Algebra R T := (coeffwiseRealCHom K).f₁.toAlgebra
  letI : Algebra (∀ i, K i) T := ((coeffwiseRealCHom K).f₁.comp
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀).toAlgebra
  letI : IsScalarTower (∀ i, K i) R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  change FiniteProjectiveModule.piUniformBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M) T
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange (∀ i, K i) R T T (productConstModule K M).M)
        ((1 : T) ⊗ₜ[R] toConstantModuleElement K M m)) =
    prodTrivializationCoord K M ((1 : T) ⊗ₜ[R] m)
  calc
    FiniteProjectiveModule.piUniformBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M) T
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange (∀ i, K i) R T T (productConstModule K M).M)
        ((1 : T) ⊗ₜ[R] toConstantModuleElement K M m))
      = fun c => algebraMap R T
          (FiniteProjectiveModule.piUniformBaseChangeCoord K (fiberConstModule K M)
            (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M) R
            (toConstantModuleElement K M m) c) := by
          exact FiniteProjectiveModule.piUniformBaseChangeCoord_cancelBaseChange K
            (fiberConstModule K M) (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M)
            R T (show R ⊗[∀ i, K i] (productConstModule K M).M from
              toConstantModuleElement K M m)
    _ = fun c => (coeffwiseRealCHom K).f₁ (trivializedCoordLiftVector K M m c) := by
          ext c
          rw [toConstantModuleElement_coord]
          rfl
    _ = prodTrivializationCoord K M ((1 : T) ⊗ₜ[R] m) := by
          exact coeffwiseRealCHom_f₁_trivializedCoordLiftVector K M m

/-- The coefficientwise base change of `toConstantLinearMap`, with successive
base changes cancelled. -/
private noncomputable def toConstantLinearMapProdCancel
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    let R := (realC (∀ i, K i)).R₁
    let T := (prodRealC K).R₁
    let A := ∀ i, K i
    letI : Algebra A R :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
    letI : Algebra R T := (coeffwiseRealCHom K).f₁.toAlgebra
    letI : Algebra A T := ((coeffwiseRealCHom K).f₁.comp
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀).toAlgebra
    letI : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    T ⊗[R] M.M →ₗ[T] T ⊗[A] (productConstModule K M).M := by
  intro R T A
  letI : Algebra A R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  letI : Algebra R T := (coeffwiseRealCHom K).f₁.toAlgebra
  letI : Algebra A T := ((coeffwiseRealCHom K).f₁.comp
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀).toAlgebra
  letI : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T
    (productConstModule K M).M).toLinearMap.comp
    (LinearMap.baseChange T (toConstantLinearMap K M))

/-- Finite-free coordinates of the cancelled coefficientwise base change of
`toConstantLinearMap`. -/
private noncomputable def toConstantLinearMapProdCoord
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    let R := (realC (∀ i, K i)).R₁
    let T := (prodRealC K).R₁
    let A := ∀ i, K i
    letI : Algebra A R :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
    letI : Algebra R T := (coeffwiseRealCHom K).f₁.toAlgebra
    letI : Algebra A T := ((coeffwiseRealCHom K).f₁.comp
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀).toAlgebra
    letI : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    T ⊗[R] M.M →ₗ[T] (Fin (productFiberRankBoundN K M) → T) := by
  intro R T A
  letI : Algebra A R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  letI : Algebra R T := (coeffwiseRealCHom K).f₁.toAlgebra
  letI : Algebra A T := ((coeffwiseRealCHom K).f₁.comp
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀).toAlgebra
  letI : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (FiniteProjectiveModule.piUniformBaseChangeCoord K (fiberConstModule K M)
    (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M) T).comp
    (toConstantLinearMapProdCancel K M)

section ToConstantLinearMapProduct

attribute [local irreducible]
  FiniteProjectiveModule.piUniformBaseChangeCoord
  TensorProduct.AlgebraTensorModule.cancelBaseChange
  prodTrivializationCoord

/-- The coordinate composite of the cancelled coefficientwise base change of
`toConstantLinearMap` is the product fiber-trivialized coordinate map. -/
private lemma toConstantLinearMap_prod_coord_map
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    toConstantLinearMapProdCoord K M = prodTrivializationCoord K M := by
  let R := (realC (∀ i, K i)).R₁
  let T := (prodRealC K).R₁
  let A := ∀ i, K i
  letI : Algebra A R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  letI : Algebra R T := (coeffwiseRealCHom K).f₁.toAlgebra
  letI : Algebra A T := ((coeffwiseRealCHom K).f₁.comp
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀).toAlgebra
  letI : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let P := fiberConstModule K M
  let N := productFiberRankBoundN K M
  let hN := fiberConstModule_finrank_le K M
  let L : T ⊗[R] M.M →ₗ[T] (Fin N → T) :=
    (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN T).comp
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T
        (productConstModule K M).M).toLinearMap.comp
        (LinearMap.baseChange T (toConstantLinearMap K M)))
  let G : T ⊗[R] M.M →ₗ[T] (Fin N → T) := prodTrivializationCoord K M
  have hLG : L = G := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s m
    change FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN T
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T (productConstModule K M).M)
          ((LinearMap.baseChange T (toConstantLinearMap K M)) (s ⊗ₜ[R] m))) =
      prodTrivializationCoord K M (s ⊗ₜ[R] m)
    have hcancel :
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T (productConstModule K M).M)
          (s ⊗ₜ[R] (show R ⊗[A] (productConstModule K M).M from
            toConstantModuleElement K M m)) =
        s • (TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T (productConstModule K M).M)
          ((1 : T) ⊗ₜ[R] (show R ⊗[A] (productConstModule K M).M from
            toConstantModuleElement K M m)) := by
      have hs : (s ⊗ₜ[R] (show R ⊗[A] (productConstModule K M).M from
            toConstantModuleElement K M m)) =
          (s • ((1 : T) ⊗ₜ[R] (show R ⊗[A] (productConstModule K M).M from
            toConstantModuleElement K M m)) :
              T ⊗[R] (R ⊗[A] (productConstModule K M).M)) := by
        rw [TensorProduct.smul_tmul']
        simp
      rw [hs]
      rw [map_smul]
    have hcoord : prodTrivializationCoord K M (s ⊗ₜ[R] m) =
        s • prodTrivializationCoord K M ((1 : T) ⊗ₜ[R] m) := by
      let z : T ⊗[R] M.M := (1 : T) ⊗ₜ[R] m
      have hs : (s ⊗ₜ[R] m : T ⊗[R] M.M) = s • z := by
        dsimp [z]
        rw [TensorProduct.smul_tmul']
        simp
      calc
        prodTrivializationCoord K M (s ⊗ₜ[R] m) = prodTrivializationCoord K M (s • z) := by
          rw [hs]
        _ = s • prodTrivializationCoord K M z := by
          exact map_smul (prodTrivializationCoord K M) s z
        _ = s • prodTrivializationCoord K M ((1 : T) ⊗ₜ[R] m) := by
          rfl
    calc
      FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN T
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T (productConstModule K M).M)
            ((LinearMap.baseChange T (toConstantLinearMap K M)) (s ⊗ₜ[R] m)))
        = s • FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN T
            ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T (productConstModule K M).M)
              ((1 : T) ⊗ₜ[R] toConstantModuleElement K M m)) := by
            rw [LinearMap.baseChange_tmul]
            change FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN T
              ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T (productConstModule K M).M)
                (s ⊗ₜ[R] toConstantModuleElement K M m)) = _
            rw [hcancel]
            change FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN T
                (s • (TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T
                  (productConstModule K M).M)
                  ((1 : T) ⊗ₜ[R] toConstantModuleElement K M m)) = _
            exact map_smul (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN T) s
              ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T
                (productConstModule K M).M)
                ((1 : T) ⊗ₜ[R] toConstantModuleElement K M m))
      _ = s • prodTrivializationCoord K M ((1 : T) ⊗ₜ[R] m) := by
            rw [toConstantModuleElement_prod_coord]
      _ = prodTrivializationCoord K M (s ⊗ₜ[R] m) := by
            rw [hcoord]
  change L = G
  exact hLG

end ToConstantLinearMapProduct

/-- The product finite-free coordinate map on the product of constant fiber
objects is injective. -/
private lemma prodFiberConstCoord_injective
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    Function.Injective (prodFiberConstCoord K M) := by
  intro y z hyz
  ext i
  letI : Algebra (K i) (realC (K i)).R₁ :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
  apply FiniteProjectiveModule.fiberBaseChangeCoord_injective K (fiberConstModule K M)
    (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M) i (realC (K i)).R₁
  ext c
  have h := congrFun (congrFun hyz c) i
  simpa [prodFiberConstCoord_apply] using h

/-- The product fiber-trivialized coordinate map is injective. -/
private lemma prodTrivializationCoord_injective
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    Function.Injective (prodTrivializationCoord K M) := by
  exact (prodFiberConstCoord_injective K M).comp
    (prodFiberTrivialization K M).injective

/-- After cancelling successive base changes, the coefficientwise base change of
`toConstantLinearMap` is injective. -/
lemma toConstantLinearMap_prod_cancel_injective
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    let R := (realC (∀ i, K i)).R₁
    let T := (prodRealC K).R₁
    let A := ∀ i, K i
    letI : Algebra A R :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
    letI : Algebra R T := (coeffwiseRealCHom K).f₁.toAlgebra
    letI : Algebra A T := ((coeffwiseRealCHom K).f₁.comp
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀).toAlgebra
    letI : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    Function.Injective (fun x : T ⊗[R] M.M =>
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T (productConstModule K M).M)
        ((LinearMap.baseChange T (toConstantLinearMap K M)) x)) := by
  intro R T A
  letI : Algebra A R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  letI : Algebra R T := (coeffwiseRealCHom K).f₁.toAlgebra
  letI : Algebra A T := ((coeffwiseRealCHom K).f₁.comp
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀).toAlgebra
  letI : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  change Function.Injective (toConstantLinearMapProdCancel K M)
  apply Function.Injective.of_comp
    (f := FiniteProjectiveModule.piUniformBaseChangeCoord K (fiberConstModule K M)
      (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M) T)
  change Function.Injective (toConstantLinearMapProdCoord K M)
  rw [toConstantLinearMap_prod_coord_map]
  exact prodTrivializationCoord_injective K M


end

end Novikov.Descent
