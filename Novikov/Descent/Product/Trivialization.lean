import Novikov.Descent.Product.Fiber

/-!
# Product fiber trivializations

This file assembles the algebraically closed fiber trivializations chosen in
`Fiber.lean` after base change to the levelwise product Novikov ring.  It also
packages the finite-free coordinate map obtained from the uniformly bounded
fiber modules.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract

namespace Novikov.Descent

noncomputable section

universe u

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)] [∀ i, IsAlgClosed (K i)]

/-- A dependent product of linear equivalences is a linear equivalence over the
product scalar ring. -/
private noncomputable def piLinearEquiv {S : I → Type u} [∀ i, Semiring (S i)]
    {X Y : I → Type u} [∀ i, AddCommMonoid (X i)] [∀ i, Module (S i) (X i)]
    [∀ i, AddCommMonoid (Y i)] [∀ i, Module (S i) (Y i)]
    (e : ∀ i, X i ≃ₗ[S i] Y i) :
    letI : Module ((i : I) → S i) ((i : I) → X i) := inferInstance
    letI : Module ((i : I) → S i) ((i : I) → Y i) := inferInstance
    ((i : I) → X i) ≃ₗ[((i : I) → S i)] ((i : I) → Y i) where
  toFun x i := e i (x i)
  invFun y i := (e i).symm (y i)
  left_inv x := by
    funext i
    exact (e i).left_inv (x i)
  right_inv y := by
    funext i
    exact (e i).right_inv (y i)
  map_add' x y := by
    funext i
    exact map_add (e i) (x i) (y i)
  map_smul' a x := by
    funext i
    exact map_smul (e i) (a i) (x i)

/-- Identify base change to `prodRealC K` with the product of the base changes to
all fibers. -/
noncomputable def prodBaseChangeFiberEquiv
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    letI : Module (prodRealC K).R₁ (∀ i, (fiberDescentDatum K M i).M) := by
      change Module ((i : I) → (realC (K i)).R₁) (∀ i, (fiberDescentDatum K M i).M)
      infer_instance
    (M.baseChange (coeffwiseRealCHom K)).M ≃ₗ[(prodRealC K).R₁]
      ∀ i, (fiberDescentDatum K M i).M := by
  letI : ∀ i, Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
    fun i => (fiberRealCHom K i).f₁.toAlgebra
  letI : Module ((i : I) → (realC (K i)).R₁)
      (M.baseChange (coeffwiseRealCHom K)).M := by
    change Module (prodRealC K).R₁ (M.baseChange (coeffwiseRealCHom K)).M
    infer_instance
  change (M.baseChange (coeffwiseRealCHom K)).M ≃ₗ[((i : I) → (realC (K i)).R₁)]
      ∀ i, (fiberDescentDatum K M i).M
  exact tensorProductPiLeftOfFiniteProjective (R := (realC (∀ i, K i)).R₁)
    (fun i => (realC (K i)).R₁) M.M

omit [∀ i, IsAlgClosed (K i)] in
@[simp]
lemma prodBaseChangeFiberEquiv_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (s : (prodRealC K).R₁) (m : M.M) (i : I) :
    letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ :=
      (coeffwiseRealCHom K).f₁.toAlgebra
    letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
      (fiberRealCHom K i).f₁.toAlgebra
    (prodBaseChangeFiberEquiv K M (s ⊗ₜ[(realC (∀ i, K i)).R₁] m)) i =
      s i ⊗ₜ[(realC (∀ i, K i)).R₁] m := by
  letI : ∀ i, Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
    fun i => (fiberRealCHom K i).f₁.toAlgebra
  dsimp [prodBaseChangeFiberEquiv]
  exact tensorProductPiLeftOfFiniteProjective_tmul
    (R := (realC (∀ i, K i)).R₁) (S := fun i => (realC (K i)).R₁) M.M s m i

/-- The inverse of the chosen fiber isomorphism, as a linear equivalence from the
fiber of `M` to the chosen constant fiber object. -/
noncomputable def fiberTrivializationLinearEquiv
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    (fiberDescentDatum K M i).M ≃ₗ[(realC (K i)).R₁]
      (fiberConstDescentDatum K M i).M :=
  LinearEquiv.ofLinear (fiberConstIso K M i).inv.toLinearMap
    (fiberConstIso K M i).hom.toLinearMap
    (congrArg DescentDatum.Hom.toLinearMap (fiberConstIso K M i).hom_inv_id)
    (congrArg DescentDatum.Hom.toLinearMap (fiberConstIso K M i).inv_hom_id)

/-- Product of the inverse fiber trivializations, after identifying base change
to `prodRealC K` with the product of the fiber base changes. -/
noncomputable def prodFiberTrivialization
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    letI : Module (prodRealC K).R₁ (∀ i, (fiberDescentDatum K M i).M) := by
      change Module ((i : I) → (realC (K i)).R₁) (∀ i, (fiberDescentDatum K M i).M)
      infer_instance
    letI : Module (prodRealC K).R₁ (∀ i, (fiberConstDescentDatum K M i).M) := by
      change Module ((i : I) → (realC (K i)).R₁)
        (∀ i, (fiberConstDescentDatum K M i).M)
      infer_instance
    (M.baseChange (coeffwiseRealCHom K)).M ≃ₗ[(prodRealC K).R₁]
      ∀ i, (fiberConstDescentDatum K M i).M := by
  letI : Module (prodRealC K).R₁ (∀ i, (fiberDescentDatum K M i).M) := by
    change Module ((i : I) → (realC (K i)).R₁) (∀ i, (fiberDescentDatum K M i).M)
    infer_instance
  letI : Module (prodRealC K).R₁ (∀ i, (fiberConstDescentDatum K M i).M) := by
    change Module ((i : I) → (realC (K i)).R₁)
      (∀ i, (fiberConstDescentDatum K M i).M)
    infer_instance
  exact (prodBaseChangeFiberEquiv K M).trans
    (piLinearEquiv (fun i => fiberTrivializationLinearEquiv K M i))

/-- The inverse fiber trivialization is compatible with the descent isomorphisms. -/
lemma fiberTrivializationLinearEquiv_commute_φ
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    (fiberConstDescentDatum K M i).φ.toLinearMap ∘ₗ
        (letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₁.toAlgebra
         LinearMap.baseChange (realC (K i)).R₂
           (fiberTrivializationLinearEquiv K M i).toLinearMap) =
      (letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
       LinearMap.baseChange (realC (K i)).R₂
         (fiberTrivializationLinearEquiv K M i).toLinearMap) ∘ₗ
        (fiberDescentDatum K M i).φ.toLinearMap := by
  exact (fiberConstIso K M i).inv.commute_φ

/-- Finite-free coordinates on the product of the chosen constant fiber objects. -/
noncomputable def prodFiberConstCoord
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    letI : Module (prodRealC K).R₁ (∀ i, (fiberConstDescentDatum K M i).M) := by
      change Module ((i : I) → (realC (K i)).R₁)
        (∀ i, (fiberConstDescentDatum K M i).M)
      infer_instance
    (∀ i, (fiberConstDescentDatum K M i).M) →ₗ[(prodRealC K).R₁]
      (Fin (productFiberRankBoundN K M) → (prodRealC K).R₁) := by
  letI : Module (prodRealC K).R₁ (∀ i, (fiberConstDescentDatum K M i).M) := by
    change Module ((i : I) → (realC (K i)).R₁)
      (∀ i, (fiberConstDescentDatum K M i).M)
    infer_instance
  letI : ∀ i, Algebra (K i) (realC (K i)).R₁ := fun i =>
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
  refine
    { toFun := fun y c i =>
        FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
          (productFiberRankBoundN K M) i (realC (K i)).R₁ (y i) c
      map_add' := ?_
      map_smul' := ?_ }
  · intro y z
    ext c i
    exact congrFun (map_add
      (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i (realC (K i)).R₁) (y i) (z i)) c
  · intro a y
    ext c i
    exact congrFun (map_smul
      (FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i (realC (K i)).R₁) (a i) (y i)) c

/-- Finite-free coordinates of the product fiber trivialization of `M`. -/
noncomputable def prodTrivializationCoord
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    (M.baseChange (coeffwiseRealCHom K)).M →ₗ[(prodRealC K).R₁]
      (Fin (productFiberRankBoundN K M) → (prodRealC K).R₁) := by
  letI : Module (prodRealC K).R₁ (∀ i, (fiberDescentDatum K M i).M) := by
    change Module ((i : I) → (realC (K i)).R₁) (∀ i, (fiberDescentDatum K M i).M)
    infer_instance
  letI : Module (prodRealC K).R₁ (∀ i, (fiberConstDescentDatum K M i).M) := by
    change Module ((i : I) → (realC (K i)).R₁)
      (∀ i, (fiberConstDescentDatum K M i).M)
    infer_instance
  exact (prodFiberConstCoord K M).comp (prodFiberTrivialization K M).toLinearMap

@[simp]
lemma prodFiberConstCoord_apply
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (y : ∀ i, (fiberConstDescentDatum K M i).M)
    (c : Fin (productFiberRankBoundN K M)) (i : I) :
    letI : Algebra (K i) (realC (K i)).R₁ :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
    prodFiberConstCoord K M y c i =
      FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i (realC (K i)).R₁ (y i) c :=
  rfl

@[simp]
lemma prodTrivializationCoord_apply
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (x : (M.baseChange (coeffwiseRealCHom K)).M)
    (c : Fin (productFiberRankBoundN K M)) (i : I) :
    letI : Algebra (K i) (realC (K i)).R₁ :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
    prodTrivializationCoord K M x c i =
      FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i (realC (K i)).R₁
          ((fiberConstIso K M i).inv.toLinearMap ((prodBaseChangeFiberEquiv K M x) i)) c :=
  rfl

end

end Novikov.Descent
