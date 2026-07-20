import Novikov.Descent.Product.Ring
import Novikov.Descent.AlgClosed
import Novikov.Miscellany.ProdModule
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Fiberwise trivializations over products of algebraically closed fields

For a real Novikov descent datum over a product of algebraically closed fields,
this file defines its fiber over each factor, chooses the corresponding constant
trivialization using the algebraically closed case, and constructs the uniformly
bounded product of the chosen constant modules.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract

namespace Novikov.Descent

noncomputable section

universe u

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)] [∀ i, IsAlgClosed (K i)]

/-- The cosimplicial-ring homomorphism from `realC (∀ i, K i)` to the `i`-th
factor real Novikov cosimplicial ring. -/
noncomputable def fiberRealCHom (i : I) :
    CosimplicialRingHom (realC (∀ i, K i)) (realC (K i)) :=
  (evalProdRealCHom K i).comp (coeffwiseRealCHom K)

omit [∀ i, IsAlgClosed (K i)] in
/-- The fiber map is the generic real Novikov coefficient map induced by
evaluation at the chosen factor. -/
lemma fiberRealCHom_eq_realCCoeffHom (i : I) :
    fiberRealCHom K i = realCCoeffHom (Pi.evalRingHom K i) := by
  exact eval_comp_coeffwiseRealCHom K i

omit [∀ i, IsAlgClosed (K i)] in
/-- The level-one map of `fiberRealCHom` is the generic coefficient map induced
by evaluation at the chosen factor. -/
lemma fiberRealCHom_f₁_eq_realCCoeffHom (i : I) :
    (fiberRealCHom K i).f₁ =
      (realCCoeffHom (Pi.evalRingHom K i)).f₁ := by
  exact congrArg CosimplicialRingHom.f₁ (fiberRealCHom_eq_realCCoeffHom K i)

omit [∀ i, IsAlgClosed (K i)] in
/-- The level-two map of `fiberRealCHom` is the generic coefficient map induced
by evaluation at the chosen factor. -/
lemma fiberRealCHom_f₂_eq_realCCoeffHom (i : I) :
    (fiberRealCHom K i).f₂ =
      (realCCoeffHom (Pi.evalRingHom K i)).f₂ := by
  exact congrArg CosimplicialRingHom.f₂ (fiberRealCHom_eq_realCCoeffHom K i)

omit [∀ i, IsAlgClosed (K i)] in
/-- The level-three map of `fiberRealCHom` is the generic coefficient map
induced by evaluation at the chosen factor. -/
lemma fiberRealCHom_f₃_eq_realCCoeffHom (i : I) :
    (fiberRealCHom K i).f₃ =
      (realCCoeffHom (Pi.evalRingHom K i)).f₃ := by
  exact congrArg CosimplicialRingHom.f₃ (fiberRealCHom_eq_realCCoeffHom K i)

/-- The `i`-th fiber of a descent datum over a product of fields. -/
noncomputable def fiberDescentDatum
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (K i) :=
  M.baseChange (fiberRealCHom K i)

/-- Chosen constant finite projective module trivializing the `i`-th fiber. -/
noncomputable def fiberConstModule
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) : FiniteProjectiveModule.{u, u} (K i) := by
  let F := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (K i)
  haveI : F.IsEquivalence := vectToNovikovDescent_isEquivalence_algClosed (K i)
  exact F.objPreimage (fiberDescentDatum K M i)

/-- The constant descent datum associated to the chosen `i`-th fiber module. -/
noncomputable abbrev fiberConstDescentDatum
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (K i) :=
  (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (K i)).obj
    (fiberConstModule K M i)

/-- Chosen isomorphism from the constant datum to the `i`-th fiber. -/
noncomputable def fiberConstIso
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) : fiberConstDescentDatum K M i ≅ fiberDescentDatum K M i := by
  let F := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (K i)
  haveI : F.IsEquivalence := vectToNovikovDescent_isEquivalence_algClosed (K i)
  exact F.objObjPreimageIso (fiberDescentDatum K M i)

/-- A vector space quotient of `R^N` has dimension at most `N`. -/
private lemma finrank_le_of_surjective_fin_fun
    {R V : Type*} [Field R] [AddCommGroup V] [Module R V] (N : ℕ)
    (f : (Fin N → R) →ₗ[R] V) (hf : Function.Surjective f) :
    Module.finrank R V ≤ N := by
  have hle := LinearMap.finrank_le_finrank_of_surjective (f := f) hf
  simpa [Module.finrank_fintype_fun_eq_card] using hle

/-- Number of generators chosen for the underlying product-ring Novikov module. -/
noncomputable def productFiberRankBoundN
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) : ℕ :=
  Classical.choose (Module.Finite.exists_fin' (realC (∀ i, K i)).R₁ M.M)

/-- Chosen finite-free presentation of the underlying product-ring Novikov module. -/
noncomputable def productFiberPresentation
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    (Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₁) →ₗ[(realC (∀ i, K i)).R₁]
      M.M :=
  Classical.choose (Classical.choose_spec
    (Module.Finite.exists_fin' (realC (∀ i, K i)).R₁ M.M))

omit [∀ i, IsAlgClosed (K i)] in
lemma productFiberPresentation_surjective
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    Function.Surjective (productFiberPresentation K M) := by
  unfold productFiberPresentation productFiberRankBoundN
  exact Classical.choose_spec (Classical.choose_spec
    (Module.Finite.exists_fin' (realC (∀ i, K i)).R₁ M.M))

/-- The presentation of the `i`-th fiber obtained by base-changing the chosen
product presentation. -/
private noncomputable def fiberPresentation
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    (Fin (productFiberRankBoundN K M) → (realC (K i)).R₁) →ₗ[(realC (K i)).R₁]
      (fiberDescentDatum K M i).M := by
  letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ := (fiberRealCHom K i).f₁.toAlgebra
  let e := TensorProduct.piScalarRight (realC (∀ i, K i)).R₁ (realC (K i)).R₁
    (realC (K i)).R₁ (Fin (productFiberRankBoundN K M))
  exact (LinearMap.baseChange (realC (K i)).R₁ (productFiberPresentation K M)).comp
    e.symm.toLinearMap

omit [∀ i, IsAlgClosed (K i)] in
private lemma fiberPresentation_surjective
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    Function.Surjective (fiberPresentation K M i) := by
  letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ := (fiberRealCHom K i).f₁.toAlgebra
  dsimp [fiberPresentation]
  exact (LinearMap.baseChange_surjective (realC (K i)).R₁
      (productFiberPresentation_surjective K M)).comp
    (LinearEquiv.surjective _)

/-- The fiber presentation transported to the chosen constant object trivializing
that fiber. -/
private noncomputable def fiberConstPresentation
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    (Fin (productFiberRankBoundN K M) → (realC (K i)).R₁) →ₗ[(realC (K i)).R₁]
      (fiberConstDescentDatum K M i).M :=
  (fiberConstIso K M i).inv.toLinearMap.comp (fiberPresentation K M i)

private lemma fiberConstPresentation_surjective
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    Function.Surjective (fiberConstPresentation K M i) := by
  intro y
  obtain ⟨z, hz⟩ := fiberPresentation_surjective K M i
    ((fiberConstIso K M i).hom.toLinearMap y)
  refine ⟨z, ?_⟩
  dsimp [fiberConstPresentation]
  rw [hz]
  have hlin : (fiberConstIso K M i).inv.toLinearMap.comp
      (fiberConstIso K M i).hom.toLinearMap = LinearMap.id := by
    exact congrArg DescentDatum.Hom.toLinearMap (fiberConstIso K M i).hom_inv_id
  exact LinearMap.congr_fun hlin y

/-- The chosen constant fiber object has Novikov-rank bounded by the number of
product generators. -/
private lemma fiberConstModule_finrank_over_novikov_le
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    Module.finrank (realC (K i)).R₁ (fiberConstDescentDatum K M i).M ≤
      productFiberRankBoundN K M := by
  letI : Field (realC (K i)).R₁ := inferInstanceAs (Field (RealNovikovSeries (K i)))
  exact @finrank_le_of_surjective_fin_fun (R := (realC (K i)).R₁)
    (V := (fiberConstDescentDatum K M i).M) _ _ _ (productFiberRankBoundN K M)
    (fiberConstPresentation K M i) (fiberConstPresentation_surjective K M i)

/-- The Novikov-rank of the constant object is the dimension of its underlying
coefficient vector space. -/
private lemma fiberConstModule_finrank_eq
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    Module.finrank (realC (K i)).R₁ (fiberConstDescentDatum K M i).M =
      Module.finrank (K i) (fiberConstModule K M i).M := by
  dsimp [fiberConstDescentDatum, vectToNovikovDescent,
    constantDescentDatumFunctor, constantDescentDatum]
  letI : Field (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).R₀ :=
    inferInstanceAs (Field (K i))
  letI : Field (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).R₁ :=
    inferInstanceAs (Field (RealNovikovSeries (K i)))
  letI : Algebra (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).R₀
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).R₁ :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
  letI : Module (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).R₀
      (fiberConstModule K M i).M := (fiberConstModule K M i).instModule
  change Module.finrank (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).R₁
      (((novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).R₁) ⊗[
        (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).R₀]
        (fiberConstModule K M i).M) =
    Module.finrank (K i) (fiberConstModule K M i).M
  rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
  rfl

/-- The dimensions of the chosen constant fiber modules are uniformly bounded by
the chosen number of product generators. -/
lemma fiberConstModule_finrank_le
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    Module.finrank (K i) (fiberConstModule K M i).M ≤ productFiberRankBoundN K M := by
  rw [← fiberConstModule_finrank_eq K M i]
  exact fiberConstModule_finrank_over_novikov_le K M i

/-- Product of the chosen constant modules for the fibers, using the uniform rank
bound induced by a finite presentation of `M`. -/
noncomputable def productConstModule
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    FiniteProjectiveModule.{u, u} (∀ i, K i) :=
  FiniteProjectiveModule.piOfUniformFinrank K (fiberConstModule K M)
    (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M)

end

end Novikov.Descent
