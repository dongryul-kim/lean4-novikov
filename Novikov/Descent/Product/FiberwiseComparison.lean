import Novikov.Descent.Product.FromConstant

/-!
# Fiberwise comparison for product descent

This file develops base-change extensionality, the explicit constant-fiber model,
and the fiberwise description of the forward comparison `toConstant`.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract
open scoped BigOperators

namespace Novikov.Miscellany

/-- If `R → S` is injective and `M` is flat over `R`, then `m ↦ 1 ⊗ m` is
injective after base change to `S`. -/
lemma one_tmul_injective_of_injective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (hAlg : Function.Injective (algebraMap R S)) :
    Function.Injective (fun m : M => ((1 : S) ⊗ₜ[R] m : S ⊗[R] M)) := by
  let φ : R →ₗ[R] S := Algebra.linearMap R S
  have hφ : Function.Injective φ := hAlg
  have hTensor := Module.Flat.rTensor_preserves_injective_linearMap (M := M) φ hφ
  intro m₁ m₂ h
  apply (TensorProduct.lid R M).symm.injective
  apply hTensor
  simpa [φ, TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul] using h

/-- In a reflexive module, elements are determined by all linear functionals. -/
private lemma eq_of_dual_apply_eq {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [Module.IsReflexive R M]
    {x y : M} (h : ∀ η : Module.Dual R M, η x = η y) : x = y := by
  apply (Module.evalEquiv R M).injective
  apply LinearMap.ext
  intro η
  simpa [Module.evalEquiv_apply, Module.Dual.eval_apply] using h η

/-- Linear maps into a reflexive module are equal if all linear functionals have
identical composites with them. -/
lemma linearMap_ext_of_dual_apply_eq {R X M : Type*} [CommSemiring R]
    [AddCommMonoid X] [Module R X]
    [AddCommMonoid M] [Module R M] [Module.IsReflexive R M]
    {f g : X →ₗ[R] M} (h : ∀ (η : Module.Dual R M) (x : X), η (f x) = η (g x)) :
    f = g := by
  apply LinearMap.ext
  intro x
  exact eq_of_dual_apply_eq (fun η => h η x)

end Novikov.Miscellany

namespace Novikov.Descent

noncomputable section

universe u

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)]

/-- For a product descent datum, `m ↦ 1 ⊗ m` is injective after coefficientwise
base change from Novikov series over the product coefficient ring to the product
of the factorwise Novikov-series rings. -/
private lemma coeffwise_one_tmul_injective
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ := (coeffwiseRealCHom K).f₁.toAlgebra
    Function.Injective (fun m : M.M =>
      ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m :
        (prodRealC K).R₁ ⊗[(realC (∀ i, K i)).R₁] M.M)) := by
  letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ := (coeffwiseRealCHom K).f₁.toAlgebra
  exact Novikov.Miscellany.one_tmul_injective_of_injective
    (R := (realC (∀ i, K i)).R₁) (S := (prodRealC K).R₁) (M := M.M)
    (by
      change Function.Injective (coeffwisePiRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K)
      exact coeffwisePiRingHom_injective (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K)

/-- Equality of morphisms of product descent data can be checked after
coefficientwise base change, at the level of underlying linear maps. -/
private lemma hom_ext_of_coeffwise_baseChange_toLinearMap_eq
    {M N : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)}
    (f g : M ⟶ N)
    (hfg : (DescentDatum.Hom.baseChange (coeffwiseRealCHom K) f).toLinearMap =
      (DescentDatum.Hom.baseChange (coeffwiseRealCHom K) g).toLinearMap) :
    f = g := by
  apply DescentDatum.hom_ext
  apply LinearMap.ext
  intro m
  apply coeffwise_one_tmul_injective K N
  letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ := (coeffwiseRealCHom K).f₁.toAlgebra
  have h := LinearMap.congr_fun hfg ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m)
  simpa [DescentDatum.Hom.baseChange, LinearMap.baseChange_tmul] using h

/-- The product base-change/fiber equivalence intertwines the coefficientwise
base change of a morphism with each fiber base change of that morphism. -/
private lemma prodBaseChangeFiberEquiv_hom_baseChange_apply
    {M N : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)}
    (f : M ⟶ N) (x : (M.baseChange (coeffwiseRealCHom K)).M) (i : I) :
    (prodBaseChangeFiberEquiv K N
      ((DescentDatum.Hom.baseChange (coeffwiseRealCHom K) f).toLinearMap x)) i =
    (DescentDatum.Hom.baseChange (fiberRealCHom K i) f).toLinearMap
      ((prodBaseChangeFiberEquiv K M x) i) := by
  let R := (realC (∀ i, K i)).R₁
  let T := (prodRealC K).R₁
  let S : I → Type u := fun i => (realC (K i)).R₁
  letI : Algebra R T := (coeffwiseRealCHom K).f₁.toAlgebra
  letI : ∀ i, Algebra R (S i) := fun i => (fiberRealCHom K i).f₁.toAlgebra
  have h := LinearMap.congr_fun
    (piBaseChangeMap_comp_tensorProductPiLeftHom S f.toLinearMap) x
  exact (congrFun h i).symm

/-- Equality of product descent morphisms can be checked after every fiber base
change, at the level of underlying linear maps. -/
lemma hom_ext_of_fiber_baseChange_toLinearMap_eq
    {M N : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)}
    (f g : M ⟶ N)
    (hfg : ∀ i, (DescentDatum.Hom.baseChange (fiberRealCHom K i) f).toLinearMap =
      (DescentDatum.Hom.baseChange (fiberRealCHom K i) g).toLinearMap) :
    f = g := by
  apply hom_ext_of_coeffwise_baseChange_toLinearMap_eq K
  apply LinearMap.ext
  intro x
  apply (prodBaseChangeFiberEquiv K N).injective
  ext i
  rw [prodBaseChangeFiberEquiv_hom_baseChange_apply K f x i]
  rw [prodBaseChangeFiberEquiv_hom_baseChange_apply K g x i]
  rw [hfg i]

/-- The compatible source rewrite for `fromConstant` sends a pure constant tensor
`1 ⊗ p` to `1 ⊗` the corresponding source functional. -/
private lemma fromConstantSourceIsoProductConstModuleCompatible_inv_tmul
    [∀ i, IsAlgClosed (K i)]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (p : (productConstModule K M).M) :
    (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
     let R := E.R₁
     letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
     letI : Module E.R₀ (fromConstantModule K M).M := (fromConstantModule K M).instModule
     letI : Algebra E.R₀ R := E.π₀.toAlgebra
     (fromConstantSourceIsoProductConstModuleCompatible K M).inv.toLinearMap
        ((1 : R) ⊗ₜ[E.R₀] p) =
       ((1 : R) ⊗ₜ[E.R₀]
        ((show (productConstModule K M).M →ₗ[(∀ i, K i)] (fromConstantModule K M).M from
            (fromConstantModuleIsoProductConstModuleCompatible K M).inv) p) :
          R ⊗[E.R₀] (fromConstantModule K M).M)) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let R := E.R₁
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Module E.R₀ (fromConstantModule K M).M := (fromConstantModule K M).instModule
  letI : Algebra E.R₀ R := E.π₀.toAlgebra
  change (LinearMap.baseChange R
      (show (productConstModule K M).M →ₗ[E.R₀] (fromConstantModule K M).M from
        (fromConstantModuleIsoProductConstModuleCompatible K M).inv))
      ((1 : R) ⊗ₜ[E.R₀] p) =
    ((1 : R) ⊗ₜ[E.R₀]
      ((show (productConstModule K M).M →ₗ[E.R₀] (fromConstantModule K M).M from
        (fromConstantModuleIsoProductConstModuleCompatible K M).inv) p))
  rw [LinearMap.baseChange_tmul]

/-- Underlying linear maps of base-changed composites are the composites of the
base-changed underlying linear maps. -/
@[simp]
private lemma descentHom_baseChange_comp_toLinearMap {C D : CosimplicialRing}
    (F : CosimplicialRingHom C D) {A B E : DescentDatum C}
    (f : A ⟶ B) (g : B ⟶ E) :
    (DescentDatum.Hom.baseChange F (f ≫ g)).toLinearMap =
      (DescentDatum.Hom.baseChange F g).toLinearMap.comp
        (DescentDatum.Hom.baseChange F f).toLinearMap := by
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  change LinearMap.baseChange D.R₁ (g.toLinearMap.comp f.toLinearMap) =
    (LinearMap.baseChange D.R₁ g.toLinearMap).comp
      (LinearMap.baseChange D.R₁ f.toLinearMap)
  rw [LinearMap.baseChange_comp]

/-- On the normalized tensor `1 ⊗ (1 ⊗ p)`, the fiber base change of
`fromConstant` first applies the compatible source alignment to obtain the source
functional used by `fromConstantFromDual`. -/
lemma fromConstant_baseChange_one_tmul_source
    [∀ i, IsAlgClosed (K i)]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I)
    (p : (productConstModule K M).M) :
    (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
     let R := E.R₁
     let S := (realC (K i)).R₁
     letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
     letI : Module E.R₀ (fromConstantModule K M).M := (fromConstantModule K M).instModule
     letI : Algebra E.R₀ R := E.π₀.toAlgebra
     letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
     let w : (fromConstantModule K M).M :=
       (show (productConstModule K M).M →ₗ[(∀ i, K i)] (fromConstantModule K M).M from
          (fromConstantModuleIsoProductConstModuleCompatible K M).inv) p
     (DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap
       ((1 : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)) =
     (DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstantFromDual K M)).toLinearMap
       ((1 : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M))) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let R := E.R₁
  let S := (realC (K i)).R₁
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Module E.R₀ (fromConstantModule K M).M := (fromConstantModule K M).instModule
  letI : Algebra E.R₀ R := E.π₀.toAlgebra
  letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
  letI : Algebra (realC (∀ i, K i)).R₁ S := (fiberRealCHom K i).f₁.toAlgebra
  let w : (fromConstantModule K M).M :=
       (show (productConstModule K M).M →ₗ[(∀ i, K i)] (fromConstantModule K M).M from
          (fromConstantModuleIsoProductConstModuleCompatible K M).inv) p
  change (DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap
       ((1 : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)) = _
  rw [fromConstant]
  rw [descentHom_baseChange_comp_toLinearMap]
  rw [LinearMap.comp_apply]
  change (DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstantFromDual K M)).toLinearMap
    ((LinearMap.baseChange S (fromConstantSourceIsoProductConstModuleCompatible K M).inv.toLinearMap)
      ((1 : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M))) = _
  change (DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstantFromDual K M)).toLinearMap
    ((LinearMap.baseChange S (fromConstantSourceIsoProductConstModuleCompatible K M).inv.toLinearMap)
      ((1 : S) ⊗ₜ[(realC (∀ i, K i)).R₁]
        ((1 : R) ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M))) = _
  rw [LinearMap.baseChange_tmul]
  have hsrc := fromConstantSourceIsoProductConstModuleCompatible_inv_tmul K M p
  rw [show (fromConstantSourceIsoProductConstModuleCompatible K M).inv.toLinearMap
      ((1 : R) ⊗ₜ[E.R₀] p) =
      ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M) by
    simpa [E, R, w] using hsrc]
  rfl

/-- Pointwise evaluation formula for the source functional obtained from the
compatible source alignment. -/
lemma fromConstantModuleIsoProductConstModuleCompatible_inv_eval
    [∀ i, IsAlgClosed (K i)]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (p : (productConstModule K M).M)
    (q : (productConstModule K M.dual).M) (i : I) :
    (let w : (fromConstantModule K M).M :=
      (show (productConstModule K M).M →ₗ[(∀ i, K i)] (fromConstantModule K M).M from
        (fromConstantModuleIsoProductConstModuleCompatible K M).inv) p
     let F : (productConstModule K M.dual).M →ₗ[(∀ i, K i)] (∀ i, K i) := w
     F q i) =
    (let l : (fiberConstModule K M i).M →ₗ[K i] K i :=
      ((show (fiberConstModule K M.dual i).M →ₗ[K i]
            (FiniteProjectiveModule.dual (K i) (fiberConstModule K M i)).M from
          (fiberConstModuleDualIsoOf K M i (fiberDescentDatumDualIso K M i)).hom) (q i))
     l (p i)) := by
  let h := productConstModule_sourceFunctionalOf_apply K M (fiberDescentDatumDualIso K M) p q i
  simpa [fromConstantModuleIsoProductConstModuleCompatible] using h

/-- The fiber evaluation of the product coefficient algebra map agrees with first
embedding into product Novikov series and then evaluating the `i`-th factor. -/
lemma fiberRealCHom_f₁_π₀_apply (i : I) (a : ∀ i, K i) :
    (letI : Algebra (K i) (realC (K i)).R₁ :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra;
    (algebraMap (K i) (realC (K i)).R₁) (a i)) =
      (fiberRealCHom K i).f₁
        ((novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀ a) := by
  exact (coeffwiseEvalRingHom_algebraMapNovikov
    (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K i a).symm

variable [∀ i, IsAlgClosed (K i)]

/-- The forward comparison morphism has injective underlying linear map. -/
lemma toConstant_injective
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    Function.Injective (toConstant K M).toLinearMap := by
  change Function.Injective (toConstantLinearMap K M)
  intro m₁ m₂ h
  apply coeffwise_one_tmul_injective K M
  let R := (realC (∀ i, K i)).R₁
  let T := (prodRealC K).R₁
  let A := ∀ i, K i
  letI : Algebra A R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  letI : Algebra R T := (coeffwiseRealCHom K).f₁.toAlgebra
  letI : Algebra A T := ((coeffwiseRealCHom K).f₁.comp
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀).toAlgebra
  letI : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  apply toConstantLinearMap_prod_cancel_injective K M
  simp [LinearMap.baseChange_tmul, h]

/-- Base-changing the product constant object to a single algebraically closed
fiber and then evaluating the product module gives the chosen constant object of
that fiber. -/
noncomputable def productConstFiberBaseChangeLinearEquiv
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    let R := (realC (∀ i, K i)).R₁
    let S := (realC (K i)).R₁
    letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
    (S ⊗[R]
        (((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
          (productConstModule K M)).M)) ≃ₗ[S]
      (fiberConstDescentDatum K M i).M := by
  let A := ∀ i, K i
  let R := (realC (∀ i, K i)).R₁
  let S := (realC (K i)).R₁
  let P := fun i => (fiberConstModule K M i).M
  letI : Algebra (∀ i, K i) R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
  letI : Algebra (K i) S :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
  letI : Algebra (∀ i, K i) S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra
  letI : IsScalarTower (∀ i, K i) R S := IsScalarTower.of_algebraMap_eq (by
    intro a
    exact fiberRealCHom_f₁_π₀_apply K i a)
  change S ⊗[R] (R ⊗[A] (∀ i, P i)) ≃ₗ[S] S ⊗[K i] P i
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S (∀ i, P i)).trans
    (evalTensorPiEquiv K P i S)

/-- Pure-tensor formula for `productConstFiberBaseChangeLinearEquiv`: after
cancelling the iterated base change and evaluating the product module at the
`i`-th factor, `s ⊗ (r ⊗ p)` becomes `(r • s) ⊗ p i`. -/
lemma productConstFiberBaseChangeLinearEquiv_tmul_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I)
    (s : (realC (K i)).R₁) (r : (realC (∀ i, K i)).R₁)
    (p : (productConstModule K M).M) :
    (let A := ∀ i, K i
     let R := (realC A).R₁
     let S := (realC (K i)).R₁
     letI : Algebra A R :=
        (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A).π₀.toAlgebra
     letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
     letI : Algebra (K i) S :=
        (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
     letI : Algebra A S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra
     letI : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq (by
        intro a
        exact fiberRealCHom_f₁_π₀_apply K i a)
     (productConstFiberBaseChangeLinearEquiv K M i)
        (s ⊗ₜ[R] (r ⊗ₜ[A] p : R ⊗[A] (productConstModule K M).M)) =
       (r • s) ⊗ₜ[K i] p i) := by
  let A := ∀ i, K i
  let R := (realC A).R₁
  let S := (realC (K i)).R₁
  letI : Algebra A R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A).π₀.toAlgebra
  letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
  letI : Algebra (K i) S :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
  letI : Algebra A S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra
  letI : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq (by
    intro a
    exact fiberRealCHom_f₁_π₀_apply K i a)
  change (productConstFiberBaseChangeLinearEquiv K M i)
      (s ⊗ₜ[R] (r ⊗ₜ[A] p : R ⊗[A] (∀ i, (fiberConstModule K M i).M))) =
    (r • s) ⊗ₜ[K i] p i
  dsimp [productConstFiberBaseChangeLinearEquiv]
  change (evalTensorPiEquiv K (fun i => (fiberConstModule K M i).M) i S)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S
        (∀ i, (fiberConstModule K M i).M)) (s ⊗ₜ[R] (r ⊗ₜ[A] p))) =
    (r • s) ⊗ₜ[K i] p i
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  rw [evalTensorPiEquiv_tmul]

/-- Pairing formula for the explicit fiber description of the product constant
object, when the fiber functional is represented by a pure tensor in the chosen
constant module for the fiber of `M.dual`. -/
lemma productConstFiberBaseChangeLinearEquiv_pairing_of_dual_tmul_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I)
    (t s : (realC (K i)).R₁) (r : (realC (∀ i, K i)).R₁)
    (q : (fiberConstModule K M.dual i).M) (p : (productConstModule K M).M) :
  (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
   let R := E.R₁
   let S := (realC (K i)).R₁
   letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
   letI : Algebra E.R₀ R := E.π₀.toAlgebra
   letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
   letI : Algebra (K i) S :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
   letI : Algebra E.R₀ S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra
   letI : IsScalarTower E.R₀ R S := IsScalarTower.of_algebraMap_eq (by
      intro a
      exact fiberRealCHom_f₁_π₀_apply K i a)
   let Ei := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
   let Qi := fiberConstModule K M.dual i
   letI : Module Ei.R₀ Qi.M := Qi.instModule
   letI : Algebra Ei.R₀ Ei.R₁ := Ei.π₀.toAlgebra
   letI : Algebra (K i) Ei.R₁ := Ei.π₀.toAlgebra
   letI : Algebra Ei.R₀ S := Ei.π₀.toAlgebra
   let η : Module.Dual S (fiberConstDescentDatum K M i).M :=
      ((fiberDescentDatumDualIso K M i).hom.toLinearMap
        ((fiberConstIso K M.dual i).hom.toLinearMap
          ((t : Ei.R₁) ⊗ₜ[Ei.R₀] q))).comp (fiberConstIso K M i).hom.toLinearMap
   let l : (fiberConstModule K M i).M →ₗ[K i] K i :=
      ((show (fiberConstModule K M.dual i).M →ₗ[K i]
            (FiniteProjectiveModule.dual (K i) (fiberConstModule K M i)).M from
          (fiberConstModuleDualIsoOf K M i (fiberDescentDatumDualIso K M i)).hom) q)
   η ((productConstFiberBaseChangeLinearEquiv K M i)
        (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M))) =
   (algebraMap R S r * s) * ((show S from t) *
      (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))))) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let R := E.R₁
  let S := (realC (K i)).R₁
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Algebra E.R₀ R := E.π₀.toAlgebra
  letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
  letI : Algebra (K i) S :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
  letI : Algebra E.R₀ S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra
  letI : IsScalarTower E.R₀ R S := IsScalarTower.of_algebraMap_eq (by
    intro a
    exact fiberRealCHom_f₁_π₀_apply K i a)
  let Ei := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  let Qi := fiberConstModule K M.dual i
  letI : Module Ei.R₀ Qi.M := Qi.instModule
  letI : Algebra Ei.R₀ Ei.R₁ := Ei.π₀.toAlgebra
  letI : Algebra (K i) Ei.R₁ := Ei.π₀.toAlgebra
  letI : Algebra Ei.R₀ S := Ei.π₀.toAlgebra
  let η : Module.Dual S (fiberConstDescentDatum K M i).M :=
      ((fiberDescentDatumDualIso K M i).hom.toLinearMap
        ((fiberConstIso K M.dual i).hom.toLinearMap
          ((t : Ei.R₁) ⊗ₜ[Ei.R₀] q))).comp (fiberConstIso K M i).hom.toLinearMap
  let l : (fiberConstModule K M i).M →ₗ[K i] K i :=
      ((show (fiberConstModule K M.dual i).M →ₗ[K i]
            (FiniteProjectiveModule.dual (K i) (fiberConstModule K M i)).M from
          (fiberConstModuleDualIsoOf K M i (fiberDescentDatumDualIso K M i)).hom) q)
  change η ((productConstFiberBaseChangeLinearEquiv K M i)
        (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M))) =
    (algebraMap R S r * s) * ((show S from t) *
      (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))))
  have hprod : (productConstFiberBaseChangeLinearEquiv K M i)
        (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)) =
      ((algebraMap R S r * s) ⊗ₜ[K i] p i : S ⊗[K i] (fiberConstModule K M i).M) := by
    simpa [E, R, S, Algebra.smul_def] using
      productConstFiberBaseChangeLinearEquiv_tmul_tmul K M i s r p
  rw [hprod]
  have hη1 : η ((1 : S) ⊗ₜ[K i] p i) =
      (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))) := by
    have hθ :
        (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
         let Q := fiberConstModule K M.dual i
         letI : Module E.R₀ Q.M := Q.instModule
         letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
         (fiberConstIso K M.dual i).inv.toLinearMap
           ((fiberDescentDatumDualIso K M i).inv.toLinearMap
             (η.comp (fiberConstIso K M i).inv.toLinearMap)) =
         ((show E.R₁ from t) ⊗ₜ[E.R₀] q)) := by
      let e := fiberConstDescentDatumDualLinearEquiv K M i
      change e.symm (e ((show Ei.R₁ from t) ⊗ₜ[Ei.R₀] q)) =
        ((show Ei.R₁ from t) ⊗ₜ[Ei.R₀] q)
      exact e.symm_apply_apply _
    have h := fiberConstModuleDualIsoOf_pairing_of_tmul_tmul K M i
      (fiberDescentDatumDualIso K M i) η t q (p i) hθ
    simpa [l] using h.symm
  · have hsmul := map_smul η (algebraMap R S r * s) ((1 : S) ⊗ₜ[K i] p i)
    calc
      η (((algebraMap R S r * s) ⊗ₜ[K i] p i : S ⊗[K i] (fiberConstModule K M i).M))
          = (algebraMap R S r * s) • η ((1 : S) ⊗ₜ[K i] p i) := by
            simpa [TensorProduct.smul_tmul'] using hsmul
      _ = (algebraMap R S r * s) * η ((1 : S) ⊗ₜ[K i] p i) := rfl
      _ = (algebraMap R S r * s) * ((show S from t) *
          (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i)))) := by rw [hη1]

/-- Coordinate formula for the chosen inverse fiber trivialization on a pure
base-change tensor. -/
private lemma fiberConstIso_inv_tmul_coord
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I)
    (s : (realC (K i)).R₁) (m : M.M) (c : Fin (productFiberRankBoundN K M)) :
    (letI : Algebra (K i) (realC (K i)).R₁ :=
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra;
    FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i (realC (K i)).R₁
      ((fiberConstIso K M i).inv.toLinearMap
        ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
            (fiberRealCHom K i).f₁.toAlgebra;
          s ⊗ₜ[(realC (∀ i, K i)).R₁] m))) c =
      s * trivializedCoordFamily K M m c i) := by
  let S := (realC (K i)).R₁
  let R := (realC (∀ i, K i)).R₁
  letI : Algebra (K i) S :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
  letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
  let coord := FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i S
  change coord ((fiberConstIso K M i).inv.toLinearMap (s ⊗ₜ[R] m)) c =
    s * trivializedCoordFamily K M m c i
  have hmap : (fiberConstIso K M i).inv.toLinearMap (s ⊗ₜ[R] m) =
      s • (fiberConstIso K M i).inv.toLinearMap ((1 : S) ⊗ₜ[R] m) := by
    have h := map_smul (fiberConstIso K M i).inv.toLinearMap s ((1 : S) ⊗ₜ[R] m)
    simpa [TensorProduct.smul_tmul'] using h
  rw [hmap]
  calc
    coord (s • (fiberConstIso K M i).inv.toLinearMap ((1 : S) ⊗ₜ[R] m)) c
        = (s • coord ((fiberConstIso K M i).inv.toLinearMap ((1 : S) ⊗ₜ[R] m))) c := by
          exact congrFun (map_smul coord s
            ((fiberConstIso K M i).inv.toLinearMap ((1 : S) ⊗ₜ[R] m))) c
    _ = s * (coord ((fiberConstIso K M i).inv.toLinearMap ((1 : S) ⊗ₜ[R] m)) c) := rfl
    _ = s * trivializedCoordFamily K M m c i := by
      have hbase : coord ((fiberConstIso K M i).inv.toLinearMap ((1 : S) ⊗ₜ[R] m)) c =
          trivializedCoordFamily K M m c i := by
        rw [trivializedCoordFamily_apply]
        rw [prodTrivializationCoord_apply]
        rw [prodBaseChangeFiberEquiv_tmul]
        rfl
      rw [hbase]

/-- On pure tensors, the fiber base change of `toConstant` becomes the inverse
of the chosen fiber trivialization after evaluating the product constant module. -/
private lemma productConstFiberBaseChangeLinearEquiv_tmul_toConstant
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I)
    (s : (realC (K i)).R₁) (m : M.M) :
    (productConstFiberBaseChangeLinearEquiv K M i)
      ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
          (fiberRealCHom K i).f₁.toAlgebra;
        (LinearMap.baseChange (realC (K i)).R₁ (toConstant K M).toLinearMap)
          (s ⊗ₜ[(realC (∀ i, K i)).R₁] m))) =
      (fiberConstIso K M i).inv.toLinearMap
        ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
            (fiberRealCHom K i).f₁.toAlgebra;
          s ⊗ₜ[(realC (∀ i, K i)).R₁] m)) := by
  let A := ∀ i, K i
  let R := (realC (∀ i, K i)).R₁
  let S := (realC (K i)).R₁
  let P := fiberConstModule K M
  let N := productFiberRankBoundN K M
  let hN := fiberConstModule_finrank_le K M
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  letI : Module A (productConstModule K M).M := (productConstModule K M).instModule
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Algebra (∀ i, K i) R :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
  letI : Algebra (K i) S :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
  letI : Algebra (∀ i, K i) S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra
  letI : IsScalarTower (∀ i, K i) R S := IsScalarTower.of_algebraMap_eq (by
    intro a
    exact fiberRealCHom_f₁_π₀_apply K i a)
  letI : Algebra A R := inferInstanceAs (Algebra (∀ i, K i) R)
  letI : Algebra A S := inferInstanceAs (Algebra (∀ i, K i) S)
  letI : IsScalarTower A R S := inferInstanceAs (IsScalarTower (∀ i, K i) R S)
  apply FiniteProjectiveModule.fiberBaseChangeCoord_injective K P N hN i S
  ext c
  rw [LinearMap.baseChange_tmul]
  dsimp [productConstFiberBaseChangeLinearEquiv]
  let z : S ⊗[A] (∀ i, (P i).M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S (∀ i, (P i).M))
      (s ⊗ₜ[R] (toConstantModuleElement K M m))
  have hcoord := FiniteProjectiveModule.fiberBaseChangeCoord_evalTensorPiEquiv K P N hN i S z c
  change FiniteProjectiveModule.fiberBaseChangeCoord K P N i S
      ((evalTensorPiEquiv K (fun i => (P i).M) i S) z) c =
    FiniteProjectiveModule.fiberBaseChangeCoord K P N i S
      ((fiberConstIso K M i).inv.toLinearMap (s ⊗ₜ[R] m)) c
  rw [hcoord]
  let z1 : S ⊗[A] (∀ i, (P i).M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S (∀ i, (P i).M))
      ((1 : S) ⊗ₜ[R] (toConstantModuleElement K M m))
  have hz : z = s • z1 := by
    have h := map_smul
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S (∀ i, (P i).M))
      s ((1 : S) ⊗ₜ[R] (toConstantModuleElement K M m))
    simpa [z, z1, TensorProduct.smul_tmul'] using h
  rw [hz]
  calc
    FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN S (s • z1) c
        = s * (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN S z1 c) := by
          exact congrFun (map_smul (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN S)
            s z1) c
    _ = s * (fiberRealCHom K i).f₁
        (FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN R
          (toConstantModuleElement K M m) c) := by
          congr 1
          letI : Algebra (∀ i, K i) R :=
            (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
          letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
          letI : Algebra (K i) S :=
            (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
          letI : Algebra (∀ i, K i) S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra
          letI : IsScalarTower (∀ i, K i) R S := IsScalarTower.of_algebraMap_eq (by
            intro a
            exact fiberRealCHom_f₁_π₀_apply K i a)
          have hone := @FiniteProjectiveModule.piUniformBaseChangeCoord_cancelBaseChange
            I K (by infer_instance) P N hN R S
            (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)
            (by infer_instance) (by infer_instance) (toConstantModuleElement K M m)
          exact congrFun hone c
    _ = FiniteProjectiveModule.fiberBaseChangeCoord K P N i S
        ((fiberConstIso K M i).inv.toLinearMap (s ⊗ₜ[R] m)) c := by
          have hconst := toConstantModuleElement_coord_apply K M m c
          have hconst' :
              FiniteProjectiveModule.piUniformBaseChangeCoord K P N hN R
                (toConstantModuleElement K M m) c = trivializedCoordLift K M m c := by
            simpa [P, N, hN, R] using hconst
          rw [hconst']
          change s * ((coeffwiseRealCHom K).f₁ (trivializedCoordLift K M m c) i) =
            FiniteProjectiveModule.fiberBaseChangeCoord K P N i S
              ((fiberConstIso K M i).inv.toLinearMap (s ⊗ₜ[R] m)) c
          rw [coeffwiseRealCHom_f₁_trivializedCoordLift_apply]
          rw [fiberConstIso_inv_tmul_coord]

/-- Linear-map form of the fiber description of `toConstant`. -/
lemma productConstFiberBaseChangeLinearEquiv_toConstant_toLinearMap
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    (productConstFiberBaseChangeLinearEquiv K M i).toLinearMap.comp
      (DescentDatum.Hom.baseChange (fiberRealCHom K i) (toConstant K M)).toLinearMap =
    (fiberConstIso K M i).inv.toLinearMap := by
  let R := (realC (∀ i, K i)).R₁
  let S := (realC (K i)).R₁
  letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
  letI : Module R (fiberConstDescentDatum K M i).M :=
    RestrictScalars.module R S (fiberConstDescentDatum K M i).M
  letI : IsScalarTower R S (fiberConstDescentDatum K M i).M :=
    RestrictScalars.isScalarTower R S (fiberConstDescentDatum K M i).M
  apply TensorProduct.AlgebraTensorModule.ext
  intro s m
  change (productConstFiberBaseChangeLinearEquiv K M i)
      ((LinearMap.baseChange S (toConstant K M).toLinearMap) (s ⊗ₜ[R] m)) =
    (fiberConstIso K M i).inv.toLinearMap (s ⊗ₜ[R] m)
  exact productConstFiberBaseChangeLinearEquiv_tmul_toConstant K M i s m

end

end Novikov.Descent
