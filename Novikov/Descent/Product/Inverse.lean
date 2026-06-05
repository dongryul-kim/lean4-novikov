import Novikov.Descent.Product.FiberwiseComparison

/-!
# Reverse fiber comparison and inverse identities for product descent

This file identifies the fiberwise action of `fromConstant` through normalized
dual pairings, deduces that `toConstant` and `fromConstant` are inverse, and
packages the resulting isomorphism.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract
open scoped BigOperators

namespace Novikov.Descent

noncomputable section

universe u

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)]
variable [∀ i, IsAlgClosed (K i)]

/-- To prove the expected fiberwise description of `fromConstant`, it is enough
to pair both sides with every linear functional on the chosen constant fiber
module. -/
private lemma fromConstant_fiber_inv_of_dual_apply
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hpair : ∀ i
      (η : Module.Dual (realC (K i)).R₁ (fiberConstDescentDatum K M i).M)
      (x : (((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (productConstModule K M)).baseChange (fiberRealCHom K i)).M),
        η ((fiberConstIso K M i).inv.toLinearMap
          ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap x)) =
        η ((productConstFiberBaseChangeLinearEquiv K M i) x)) :
    ∀ i,
      (fiberConstIso K M i).inv.toLinearMap.comp
        (DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap =
          (productConstFiberBaseChangeLinearEquiv K M i).toLinearMap := by
  intro i
  apply Novikov.Miscellany.linearMap_ext_of_dual_apply_eq
  intro η x
  exact hpair i η x

/-- To prove the pure-tensor paired comparison for all fiber functionals, it is
sufficient to check it for functionals represented by pure tensors in the chosen
constant module for the fiber of `M.dual`. -/
private lemma fromConstant_dual_apply_tmul_tmul_of_represented
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hrep : ∀ i (t : (realC (K i)).R₁) (q : (fiberConstModule K M.dual i).M)
      (s : (realC (K i)).R₁) (r : (realC (∀ i, K i)).R₁)
      (p : (productConstModule K M).M),
      (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
       let R := E.R₁
       let S := (realC (K i)).R₁
       letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
       letI : Algebra E.R₀ R := E.π₀.toAlgebra
       letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
       let Ei := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
       let Qi := fiberConstModule K M.dual i
       letI : Module Ei.R₀ Qi.M := Qi.instModule
       letI : Algebra Ei.R₀ Ei.R₁ := Ei.π₀.toAlgebra
       let η : Module.Dual S (fiberConstDescentDatum K M i).M :=
          ((fiberDescentDatumDualIso K M i).hom.toLinearMap
            ((fiberConstIso K M.dual i).hom.toLinearMap
              ((t : Ei.R₁) ⊗ₜ[Ei.R₀] q))).comp (fiberConstIso K M i).hom.toLinearMap
       η ((fiberConstIso K M i).inv.toLinearMap
          ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap
            (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)))) =
       η ((productConstFiberBaseChangeLinearEquiv K M i)
            (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M))))) :
    ∀ i
      (η : Module.Dual (realC (K i)).R₁ (fiberConstDescentDatum K M i).M)
      (s : (realC (K i)).R₁) (r : (realC (∀ i, K i)).R₁)
      (p : (productConstModule K M).M),
      (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
       let R := E.R₁
       let S := (realC (K i)).R₁
       letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
       letI : Algebra E.R₀ R := E.π₀.toAlgebra
       letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
       η ((fiberConstIso K M i).inv.toLinearMap
          ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap
            (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)))) =
       η ((productConstFiberBaseChangeLinearEquiv K M i)
            (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)))) := by
  intro i η s r p
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let R := E.R₁
  let S := (realC (K i)).R₁
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Algebra E.R₀ R := E.π₀.toAlgebra
  letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
  let Ei := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  let Qi := fiberConstModule K M.dual i
  letI : Module Ei.R₀ Qi.M := Qi.instModule
  letI : Algebra Ei.R₀ Ei.R₁ := Ei.π₀.toAlgebra
  letI : Algebra Ei.R₀ S := Ei.π₀.toAlgebra
  let e := fiberConstDescentDatumDualLinearEquiv K M i
  let Φ : (S ⊗[Ei.R₀] Qi.M) →ₗ[S]
      Module.Dual S (fiberConstDescentDatum K M i).M := e.toLinearMap
  let Lval : (fiberConstDescentDatum K M i).M :=
    (fiberConstIso K M i).inv.toLinearMap
      ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap
        (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)))
  let Gval : (fiberConstDescentDatum K M i).M :=
    (productConstFiberBaseChangeLinearEquiv K M i)
      (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M))
  letI : IsScalarTower Ei.R₀ S S := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hmaps : (LinearMap.applyₗ Lval).comp Φ = (LinearMap.applyₗ Gval).comp Φ := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro t q
    change (Φ (t ⊗ₜ[Ei.R₀] q)) Lval = (Φ (t ⊗ₜ[Ei.R₀] q)) Gval
    exact hrep i t q s r p
  let θ := e.symm η
  have hrecon : Φ θ = η := e.apply_symm_apply η
  change η Lval = η Gval
  rw [← hrecon]
  exact LinearMap.congr_fun hmaps θ

/-- To prove the paired fiberwise description of `fromConstant`, it is enough to
check pure tensors `s ⊗ (r ⊗ p)` in the iterated base change of the product
constant object. -/
private lemma fromConstant_fiber_inv_of_dual_apply_tmul_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hpure : ∀ i
      (η : Module.Dual (realC (K i)).R₁ (fiberConstDescentDatum K M i).M)
      (s : (realC (K i)).R₁) (r : (realC (∀ i, K i)).R₁)
      (p : (productConstModule K M).M),
      (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
       let R := E.R₁
       let S := (realC (K i)).R₁
       letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
       letI : Algebra E.R₀ R := E.π₀.toAlgebra
       letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
       η ((fiberConstIso K M i).inv.toLinearMap
          ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap
            (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)))) =
       η ((productConstFiberBaseChangeLinearEquiv K M i)
            (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M))))) :
    ∀ i,
      (fiberConstIso K M i).inv.toLinearMap.comp
        (DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap =
          (productConstFiberBaseChangeLinearEquiv K M i).toLinearMap := by
  apply fromConstant_fiber_inv_of_dual_apply K M
  intro i η x
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let R := E.R₁
  let S := (realC (K i)).R₁
  let P := (productConstModule K M).M
  letI : Module E.R₀ P := (productConstModule K M).instModule
  letI : Algebra E.R₀ R := E.π₀.toAlgebra
  letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
  let L : S ⊗[R] (R ⊗[E.R₀] P) →ₗ[S] S :=
    η.comp ((fiberConstIso K M i).inv.toLinearMap.comp
      (DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap)
  let G : S ⊗[R] (R ⊗[E.R₀] P) →ₗ[S] S :=
    η.comp (productConstFiberBaseChangeLinearEquiv K M i).toLinearMap
  have hLG : L = G := by
    letI : Algebra E.R₀ S := ((fiberRealCHom K i).f₁.comp E.π₀).toAlgebra
    letI : IsScalarTower E.R₀ R S := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let e := TensorProduct.AlgebraTensorModule.cancelBaseChange E.R₀ R S S P
    apply (LinearMap.cancel_right e.symm.surjective).mp
    apply TensorProduct.AlgebraTensorModule.ext
    intro s p
    change L (e.symm (s ⊗ₜ[E.R₀] p)) = G (e.symm (s ⊗ₜ[E.R₀] p))
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
    exact hpure i η s 1 p
  exact LinearMap.congr_fun hLG x

/-- It is enough to compute the represented left-hand pairing on the normalized
pure tensor `1 ⊗ (1 ⊗ p)`: the general `s ⊗ (r ⊗ p)` case follows by
linearity. -/
private lemma fromConstant_represented_left_scalar_of_core
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hcore : ∀ i (t : (realC (K i)).R₁) (q : (fiberConstModule K M.dual i).M)
      (p : (productConstModule K M).M),
      (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
       let R := E.R₁
       let S := (realC (K i)).R₁
       letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
       letI : Algebra E.R₀ R := E.π₀.toAlgebra
       letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
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
       η ((fiberConstIso K M i).inv.toLinearMap
          ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap
            ((1 : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)))) =
       (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))))) :
    ∀ i (t : (realC (K i)).R₁) (q : (fiberConstModule K M.dual i).M)
      (s : (realC (K i)).R₁) (r : (realC (∀ i, K i)).R₁)
      (p : (productConstModule K M).M),
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
       η ((fiberConstIso K M i).inv.toLinearMap
          ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap
            (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)))) =
       (algebraMap R S r * s) * ((show S from t) *
          (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))))) := by
  intro i t q s r p
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
  let L : S ⊗[R] (R ⊗[E.R₀] (productConstModule K M).M) →ₗ[S] S :=
    η.comp ((fiberConstIso K M i).inv.toLinearMap.comp
      (DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap)
  let a : S := algebraMap R S r * s
  let x0 : S ⊗[R] (R ⊗[E.R₀] (productConstModule K M).M) :=
    (1 : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)
  have hx : (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)) = a • x0 := by
    dsimp [a, x0]
    rw [show (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M) =
        (show R from r) • ((1 : R) ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M) by
      rw [TensorProduct.smul_tmul']; simp]
    rw [TensorProduct.tmul_smul]
    change ((algebraMap R S r * s) ⊗ₜ[R]
        ((1 : R) ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)) =
      (((algebraMap R S r * s) • (1 : S)) ⊗ₜ[R]
        ((1 : R) ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M))
    simp
  have hcore' : L x0 = (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))) := by
    simpa [L, x0, η, l, E, R, S, Ei, Qi] using hcore i t q p
  change L (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)) =
    a * ((show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))))
  rw [hx]
  rw [map_smul]
  rw [hcore']
  rfl

/-- A scalar computation of the left-hand represented pairing, together with the
explicit computation of the product-constant side, implies the fiberwise
`fromConstant` description. -/
private lemma fromConstant_fiber_inv_of_represented_dual_apply_scalar
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hleft : ∀ i (t : (realC (K i)).R₁) (q : (fiberConstModule K M.dual i).M)
      (s : (realC (K i)).R₁) (r : (realC (∀ i, K i)).R₁)
      (p : (productConstModule K M).M),
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
       η ((fiberConstIso K M i).inv.toLinearMap
          ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap
            (s ⊗ₜ[R] (r ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)))) =
       (algebraMap R S r * s) * ((show S from t) *
          (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i)))))) :
    ∀ i,
      (fiberConstIso K M i).inv.toLinearMap.comp
        (DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap =
          (productConstFiberBaseChangeLinearEquiv K M i).toLinearMap := by
  apply fromConstant_fiber_inv_of_dual_apply_tmul_tmul K M
  apply fromConstant_dual_apply_tmul_tmul_of_represented K M
  intro i t q s r p
  have hl := hleft i t q s r p
  have hr := productConstFiberBaseChangeLinearEquiv_pairing_of_dual_tmul_tmul K M i t s r q p
  exact hl.trans hr.symm

/-- It is enough to prove the normalized represented computation after rewriting
`fromConstant` through `fromConstantFromDual`: the source-alignment and
trivialization cancellations then recover the original normalized computation. -/
private lemma fromConstant_represented_left_core_of_fromDualConstantLinearMap
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hdual : ∀ i (t : (realC (K i)).R₁) (q : (fiberConstModule K M.dual i).M)
      (p : (productConstModule K M).M),
      (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
       let R := E.R₁
       let S := (realC (K i)).R₁
       letI : Module E.R₀ (fromConstantModule K M).M := (fromConstantModule K M).instModule
       letI : Algebra E.R₀ R := E.π₀.toAlgebra
       letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
       let Ei := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
       let Qi := fiberConstModule K M.dual i
       letI : Module Ei.R₀ Qi.M := Qi.instModule
       letI : Algebra Ei.R₀ Ei.R₁ := Ei.π₀.toAlgebra
       letI : Algebra (K i) Ei.R₁ := Ei.π₀.toAlgebra
       letI : Algebra Ei.R₀ S := Ei.π₀.toAlgebra
       let β : Module.Dual S (fiberDescentDatum K M i).M :=
          (fiberDescentDatumDualIso K M i).hom.toLinearMap
            ((fiberConstIso K M.dual i).hom.toLinearMap
              ((t : Ei.R₁) ⊗ₜ[Ei.R₀] q))
       let l : (fiberConstModule K M i).M →ₗ[K i] K i :=
          ((show (fiberConstModule K M.dual i).M →ₗ[K i]
                (FiniteProjectiveModule.dual (K i) (fiberConstModule K M i)).M from
              (fiberConstModuleDualIsoOf K M i (fiberDescentDatumDualIso K M i)).hom) q)
       let w : (fromConstantModule K M).M :=
          (show (productConstModule K M).M →ₗ[(∀ i, K i)] (fromConstantModule K M).M from
            (fromConstantModuleIsoProductConstModuleCompatible K M).inv) p
       β ((1 : S) ⊗ₜ[R]
          (fromDualConstantLinearMap K M
            ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M))) =
       (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))))) :
    ∀ i (t : (realC (K i)).R₁) (q : (fiberConstModule K M.dual i).M)
      (p : (productConstModule K M).M),
      (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
       let R := E.R₁
       let S := (realC (K i)).R₁
       letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
       letI : Algebra E.R₀ R := E.π₀.toAlgebra
       letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
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
       η ((fiberConstIso K M i).inv.toLinearMap
          ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap
            ((1 : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)))) =
       (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i)))) := by
  intro i t q p
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let R := E.R₁
  let S := (realC (K i)).R₁
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Module E.R₀ (fromConstantModule K M).M := (fromConstantModule K M).instModule
  letI : Algebra E.R₀ R := E.π₀.toAlgebra
  letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
  letI : Algebra (realC (∀ i, K i)).R₁ S := (fiberRealCHom K i).f₁.toAlgebra
  let Ei := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  let Qi := fiberConstModule K M.dual i
  letI : Module Ei.R₀ Qi.M := Qi.instModule
  letI : Algebra Ei.R₀ Ei.R₁ := Ei.π₀.toAlgebra
  letI : Algebra (K i) Ei.R₁ := Ei.π₀.toAlgebra
  letI : Algebra Ei.R₀ S := Ei.π₀.toAlgebra
  let θ : (fiberConstDescentDatum K M.dual i).M := ((t : Ei.R₁) ⊗ₜ[Ei.R₀] q)
  let β : Module.Dual S (fiberDescentDatum K M i).M :=
    (fiberDescentDatumDualIso K M i).hom.toLinearMap
      ((fiberConstIso K M.dual i).hom.toLinearMap θ)
  let η : Module.Dual S (fiberConstDescentDatum K M i).M :=
    β.comp (fiberConstIso K M i).hom.toLinearMap
  let l : (fiberConstModule K M i).M →ₗ[K i] K i :=
      ((show (fiberConstModule K M.dual i).M →ₗ[K i]
            (FiniteProjectiveModule.dual (K i) (fiberConstModule K M i)).M from
          (fiberConstModuleDualIsoOf K M i (fiberDescentDatumDualIso K M i)).hom) q)
  let w : (fromConstantModule K M).M :=
       (show (productConstModule K M).M →ₗ[(∀ i, K i)] (fromConstantModule K M).M from
          (fromConstantModuleIsoProductConstModuleCompatible K M).inv) p
  change η ((fiberConstIso K M i).inv.toLinearMap
          ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap
            ((1 : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[E.R₀] p : R ⊗[E.R₀] (productConstModule K M).M)))) =
       (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i)))
  rw [fromConstant_baseChange_one_tmul_source K M i p]
  change β ((fiberConstIso K M i).hom.toLinearMap ((fiberConstIso K M i).inv.toLinearMap
    ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstantFromDual K M)).toLinearMap
       ((1 : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M))))) =
       (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i)))
  have hlin : (fiberConstIso K M i).hom.toLinearMap.comp
      (fiberConstIso K M i).inv.toLinearMap = LinearMap.id := by
    exact congrArg DescentDatum.Hom.toLinearMap (fiberConstIso K M i).inv_hom_id
  rw [show (fiberConstIso K M i).hom.toLinearMap ((fiberConstIso K M i).inv.toLinearMap
    ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstantFromDual K M)).toLinearMap
       ((1 : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M)))) =
    ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstantFromDual K M)).toLinearMap
       ((1 : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M))) from
      LinearMap.congr_fun hlin _]
  change β ((LinearMap.baseChange S (fromConstantFromDual K M).toLinearMap)
      ((1 : S) ⊗ₜ[(realC (∀ i, K i)).R₁]
        ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M))) =
    (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i)))
  rw [LinearMap.baseChange_tmul]
  change β ((1 : S) ⊗ₜ[R] (fromDualConstantLinearMap K M
      ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M))) =
    (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i)))
  simpa [β, l, w, E, R, S, Ei, Qi, θ] using hdual i t q p

/-- The final remaining normalized pairing statement after rewriting
`fromConstant` through `fromDualConstantLinearMap`. -/
def fromDualConstantLinearMapPairingCore
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) : Prop :=
  ∀ i (t : (realC (K i)).R₁) (q : (fiberConstModule K M.dual i).M)
    (p : (productConstModule K M).M),
    (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
     let R := E.R₁
     let S := (realC (K i)).R₁
     letI : Module E.R₀ (fromConstantModule K M).M := (fromConstantModule K M).instModule
     letI : Algebra E.R₀ R := E.π₀.toAlgebra
     letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
     let Ei := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
     let Qi := fiberConstModule K M.dual i
     letI : Module Ei.R₀ Qi.M := Qi.instModule
     letI : Algebra Ei.R₀ Ei.R₁ := Ei.π₀.toAlgebra
     letI : Algebra (K i) Ei.R₁ := Ei.π₀.toAlgebra
     letI : Algebra Ei.R₀ S := Ei.π₀.toAlgebra
     let β : Module.Dual S (fiberDescentDatum K M i).M :=
        (fiberDescentDatumDualIso K M i).hom.toLinearMap
          ((fiberConstIso K M.dual i).hom.toLinearMap
            ((t : Ei.R₁) ⊗ₜ[Ei.R₀] q))
     let l : (fiberConstModule K M i).M →ₗ[K i] K i :=
        ((show (fiberConstModule K M.dual i).M →ₗ[K i]
              (FiniteProjectiveModule.dual (K i) (fiberConstModule K M i)).M from
            (fiberConstModuleDualIsoOf K M i (fiberDescentDatumDualIso K M i)).hom) q)
     let w : (fromConstantModule K M).M :=
        (show (productConstModule K M).M →ₗ[(∀ i, K i)] (fromConstantModule K M).M from
          (fromConstantModuleIsoProductConstModuleCompatible K M).inv) p
     β ((1 : S) ⊗ₜ[R]
        (fromDualConstantLinearMap K M
          ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M))) =
     (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))))

/-- The final normalized pairing statement used to identify `fromConstant` with
the fiberwise inverse of `toConstant`. -/
lemma fromDualConstantLinearMapPairingCore_holds
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    fromDualConstantLinearMapPairingCore K M := by
  classical
  intro i t q p
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  let R := E.R₁
  let S := (realC (K i)).R₁
  letI : Module E.R₀ (fromConstantModule K M).M := (fromConstantModule K M).instModule
  letI : Module E.R₀ (productConstModule K M.dual).M := (productConstModule K M.dual).instModule
  letI : Algebra E.R₀ R := E.π₀.toAlgebra
  letI : Algebra (∀ i, K i) R := E.π₀.toAlgebra
  letI : Algebra (∀ i, K i) (realC (∀ i, K i)).R₁ :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)).π₀.toAlgebra
  letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
  letI : Algebra (realC (∀ i, K i)).R₁ S := (fiberRealCHom K i).f₁.toAlgebra
  let Ei := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  let Qi := fiberConstModule K M.dual i
  letI : Module Ei.R₀ Qi.M := Qi.instModule
  letI : Algebra Ei.R₀ Ei.R₁ := Ei.π₀.toAlgebra
  letI : Algebra (K i) Ei.R₁ := Ei.π₀.toAlgebra
  letI : Algebra Ei.R₀ S := Ei.π₀.toAlgebra
  letI : Algebra (K i) S := Ei.π₀.toAlgebra
  let θ : (fiberConstDescentDatum K M.dual i).M := ((t : Ei.R₁) ⊗ₜ[Ei.R₀] q)
  let y : (fiberDescentDatum K M.dual i).M := (fiberConstIso K M.dual i).hom.toLinearMap θ
  let β : Module.Dual S (fiberDescentDatum K M i).M :=
        (fiberDescentDatumDualIso K M i).hom.toLinearMap y
  let l : (fiberConstModule K M i).M →ₗ[K i] K i :=
        ((show (fiberConstModule K M.dual i).M →ₗ[K i]
              (FiniteProjectiveModule.dual (K i) (fiberConstModule K M i)).M from
            (fiberConstModuleDualIsoOf K M i (fiberDescentDatumDualIso K M i)).hom) q)
  let w : (fromConstantModule K M).M :=
        (show (productConstModule K M).M →ₗ[(∀ i, K i)] (fromConstantModule K M).M from
          (fromConstantModuleIsoProductConstModuleCompatible K M).inv) p
  change β ((1 : S) ⊗ₜ[R]
        (fromDualConstantLinearMap K M
          ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M))) =
     (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i)))
  let B : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i) :=
    (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
      (productConstModule K M.dual)
  let f : M.dual ⟶ B := toDualConstant K M
  let x0 : ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (fromConstantModule K M)).M :=
    ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M)
  let x : (B.dual.baseChange (fiberRealCHom K i)).M :=
    (DescentDatum.Hom.baseChange (fiberRealCHom K i)
      (productConstDescentDatumDualIso K M.dual).hom).toLinearMap
        ((1 : S) ⊗ₜ[R] x0)
  have hnat := (fiberRealCHom K i).baseChangeDualLinearEquiv_dual_eval_symm_apply M f x y
  have hleftArg :
      (1 : S) ⊗ₜ[R] (fromDualConstantLinearMap K M x0) =
        ((letI : Algebra (realC (∀ i, K i)).R₁ S := (fiberRealCHom K i).f₁.toAlgebra
          LinearMap.baseChange S (Module.evalEquiv (realC (∀ i, K i)).R₁ M.M).symm.toLinearMap)
          ((DescentDatum.Hom.baseChange (fiberRealCHom K i) f.dual).toLinearMap x)) := by
    let evalM : M.dual.dual.M →ₗ[(realC (∀ i, K i)).R₁] M.M :=
      (Module.evalEquiv (realC (∀ i, K i)).R₁ M.M).symm.toLinearMap
    let dmap : B.dual.M →ₗ[(realC (∀ i, K i)).R₁] M.dual.dual.M := f.dual.toLinearMap
    let amap : ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (fromConstantModule K M)).M →ₗ[(realC (∀ i, K i)).R₁] B.dual.M :=
      (productConstDescentDatumDualIso K M.dual).hom.toLinearMap
    have hbase :
        ((LinearMap.baseChange S evalM)
          (((LinearMap.baseChange S dmap)
            ((LinearMap.baseChange S amap) ((1 : S) ⊗ₜ[R] x0))))) =
        (LinearMap.baseChange S (evalM.comp (dmap.comp amap))) ((1 : S) ⊗ₜ[R] x0) := by
      rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]
      rfl
    calc
      (1 : S) ⊗ₜ[R] (fromDualConstantLinearMap K M x0) =
          (LinearMap.baseChange S (evalM.comp (dmap.comp amap))) ((1 : S) ⊗ₜ[R] x0) := by
            change (1 : S) ⊗ₜ[(realC (∀ i, K i)).R₁]
                ((evalM.comp (dmap.comp amap)) x0) =
              (LinearMap.baseChange S (evalM.comp (dmap.comp amap)))
                ((1 : S) ⊗ₜ[(realC (∀ i, K i)).R₁] x0)
            exact (LinearMap.baseChange_tmul (evalM.comp (dmap.comp amap)) (1 : S) x0).symm
      _ = (LinearMap.baseChange S evalM)
          (((LinearMap.baseChange S dmap)
            ((LinearMap.baseChange S amap) ((1 : S) ⊗ₜ[R] x0)))) := hbase.symm
      _ = ((letI : Algebra (realC (∀ i, K i)).R₁ S := (fiberRealCHom K i).f₁.toAlgebra
          LinearMap.baseChange S (Module.evalEquiv (realC (∀ i, K i)).R₁ M.M).symm.toLinearMap)
          ((DescentDatum.Hom.baseChange (fiberRealCHom K i) f.dual).toLinearMap x)) := by
            rfl
  change β ((1 : S) ⊗ₜ[R] (fromDualConstantLinearMap K M x0)) =
     (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i)))
  calc
    β ((1 : S) ⊗ₜ[R] (fromDualConstantLinearMap K M x0)) =
        β (((letI : Algebra (realC (∀ i, K i)).R₁ S := (fiberRealCHom K i).f₁.toAlgebra
          LinearMap.baseChange S (Module.evalEquiv (realC (∀ i, K i)).R₁ M.M).symm.toLinearMap)
          ((DescentDatum.Hom.baseChange (fiberRealCHom K i) f.dual).toLinearMap x))) := by
          exact congrArg β hleftArg
    _ = (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))) := by
      have hnat' :
          β
            (((letI : Algebra (realC (∀ i, K i)).R₁ S := (fiberRealCHom K i).f₁.toAlgebra
              LinearMap.baseChange S (Module.evalEquiv (realC (∀ i, K i)).R₁ M.M).symm.toLinearMap)
              ((DescentDatum.Hom.baseChange (fiberRealCHom K i) f.dual).toLinearMap x))) =
          (let α : (B.baseChange (fiberRealCHom K i)).M →ₗ[S] S :=
              (fiberRealCHom K i).baseChangeDualLinearEquiv B x
           α ((DescentDatum.Hom.baseChange (fiberRealCHom K i) f).toLinearMap y)) := by
        simpa [β, fiberDescentDatumDualIso, fiberDescentDatumDualCanonicalIso,
          fiberDescentDatumDualHom_toLinearMap] using hnat
      rw [hnat']
      let α : (B.baseChange (fiberRealCHom K i)).M →ₗ[S] S :=
        (fiberRealCHom K i).baseChangeDualLinearEquiv B x
      let qsingle : (productConstModule K M.dual).M := Pi.single i q
      let z : (B.baseChange (fiberRealCHom K i)).M :=
        (DescentDatum.Hom.baseChange (fiberRealCHom K i) f).toLinearMap y
      have hto : (productConstFiberBaseChangeLinearEquiv K M.dual i) z = θ := by
        have hlin := productConstFiberBaseChangeLinearEquiv_toConstant_toLinearMap K M.dual i
        have happ := LinearMap.congr_fun hlin y
        change (productConstFiberBaseChangeLinearEquiv K M.dual i)
            ((DescentDatum.Hom.baseChange (fiberRealCHom K i) (toConstant K M.dual)).toLinearMap y) =
          (fiberConstIso K M.dual i).inv.toLinearMap y at happ
        have hy : (fiberConstIso K M.dual i).inv.toLinearMap y = θ := by
          dsimp [y]
          have hlin' : (fiberConstIso K M.dual i).inv.toLinearMap.comp
              (fiberConstIso K M.dual i).hom.toLinearMap = LinearMap.id := by
            exact congrArg DescentDatum.Hom.toLinearMap (fiberConstIso K M.dual i).hom_inv_id
          exact LinearMap.congr_fun hlin' θ
        simpa [z, f] using happ.trans hy
      have hpure_image :
          (productConstFiberBaseChangeLinearEquiv K M.dual i)
            ((t : S) ⊗ₜ[R]
              ((1 : R) ⊗ₜ[E.R₀] qsingle : R ⊗[E.R₀] (productConstModule K M.dual).M)) = θ := by
        have h := productConstFiberBaseChangeLinearEquiv_tmul_tmul K M.dual i (t : S) (1 : R) qsingle
        change (productConstFiberBaseChangeLinearEquiv K M.dual i)
            ((t : S) ⊗ₜ[(realC (∀ i, K i)).R₁]
              ((1 : (realC (∀ i, K i)).R₁) ⊗ₜ[(∀ i, K i)] qsingle :
                (realC (∀ i, K i)).R₁ ⊗[(∀ i, K i)] (productConstModule K M.dual).M)) =
          ((t : S) ⊗ₜ[K i] q)
        calc
          (productConstFiberBaseChangeLinearEquiv K M.dual i)
              ((t : S) ⊗ₜ[(realC (∀ i, K i)).R₁]
                ((1 : (realC (∀ i, K i)).R₁) ⊗ₜ[(∀ i, K i)] qsingle :
                  (realC (∀ i, K i)).R₁ ⊗[(∀ i, K i)] (productConstModule K M.dual).M)) =
              (((1 : (realC (∀ i, K i)).R₁) • (t : S)) ⊗ₜ[K i] q) := by
                simpa only [qsingle, Pi.single_eq_same] using h
          _ = (t : S) ⊗ₜ[K i] q := by simp
      have hz : z =
          ((t : S) ⊗ₜ[R]
              ((1 : R) ⊗ₜ[E.R₀] qsingle : R ⊗[E.R₀] (productConstModule K M.dual).M)) := by
        apply (productConstFiberBaseChangeLinearEquiv K M.dual i).injective
        exact hto.trans hpure_image.symm
      change α z = (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i)))
      rw [hz]
      let pure : (B.baseChange (fiberRealCHom K i)).M :=
        ((t : S) ⊗ₜ[R]
          ((1 : R) ⊗ₜ[E.R₀] qsingle : R ⊗[E.R₀] (productConstModule K M.dual).M))
      change α pure = (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i)))
      have hα := CosimplicialRingHom.baseChangeDualLinearEquiv_apply (fiberRealCHom K i) B x pure
      have hα' : α pure =
          (baseChangeSelfEquiv (fiberRealCHom K i).f₁)
            (((homBaseChangeEquiv S) x) pure) := by
        simpa [α] using hα
      rw [hα']
      dsimp [pure, x, x0]
      rw [show (DescentDatum.Hom.baseChange (fiberRealCHom K i)
              (productConstDescentDatumDualIso K M.dual).hom).toLinearMap
                ((1 : S) ⊗ₜ[R]
                  ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M)) =
            ((1 : S) ⊗ₜ[R]
              ((productConstDescentDatumDualIso K M.dual).hom.toLinearMap
                ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M)) :
                S ⊗[R] B.dual.M) by
          exact LinearMap.baseChange_tmul
            (productConstDescentDatumDualIso K M.dual).hom.toLinearMap (1 : S)
            ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M)]
      let ffun : B.M →ₗ[R] R :=
        (productConstDescentDatumDualIso K M.dual).hom.toLinearMap
          ((1 : R) ⊗ₜ[E.R₀] w : R ⊗[E.R₀] (fromConstantModule K M).M)
      have hhom := @homBaseChangeEquiv_tmul R _ B.M R _ _ _ _ _ _
        (Module.Finite.self R) (inferInstance) S _ _ (1 : S) ffun
      change (baseChangeSelfEquiv (fiberRealCHom K i).f₁)
          (((homBaseChangeEquiv S) ((1 : S) ⊗ₜ[R] ffun)) pure) =
        (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i)))
      calc
        (baseChangeSelfEquiv (fiberRealCHom K i).f₁)
            (((homBaseChangeEquiv S) ((1 : S) ⊗ₜ[R] ffun)) pure) =
          (baseChangeSelfEquiv (fiberRealCHom K i).f₁)
            (((1 : S) • LinearMap.baseChange S ffun) pure) := by
            exact congrArg (fun L : (B.baseChange (fiberRealCHom K i)).M →ₗ[S] (S ⊗[R] R) =>
              (baseChangeSelfEquiv (fiberRealCHom K i).f₁) (L pure)) hhom
        _ = (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))) := by
          simp only [one_smul]
          let qconst : B.M :=
            ((1 : R) ⊗ₜ[E.R₀] qsingle : R ⊗[E.R₀] (productConstModule K M.dual).M)
          have hbc : (LinearMap.baseChange S ffun) pure =
              ((t : S) ⊗ₜ[R] (ffun qconst) : S ⊗[R] R) := by
            dsimp [pure, qconst]
            exact LinearMap.baseChange_tmul ffun (t : S) qconst
          let wlin : (productConstModule K M.dual).M →ₗ[E.R₀] E.R₀ := w
          have hffun : ffun qconst = E.π₀ (wlin qsingle) := by
            let P : FiniteProjectiveModule E.R₀ := productConstModule K M.dual
            let Q : FiniteProjectiveModule E.R₀ := fromConstantModule K M
            have heval := constantDescentDatum_dual_hom_map_eval E P Q (Iso.refl _) w qsingle
            simpa [ffun, qconst, productConstDescentDatumDualIso, E, R, P, Q, wlin,
              constantDescentDatumMap_toLinearMap] using heval
          have hw : (wlin qsingle) i = l (p i) := by
            have h := fromConstantModuleIsoProductConstModuleCompatible_inv_eval K M p qsingle i
            simpa [wlin, w, l, qsingle] using h
          have hF : (fiberRealCHom K i).f₁ (ffun qconst) =
              (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))) := by
            rw [hffun]
            have hcoeff := fiberRealCHom_f₁_π₀_apply K i (wlin qsingle)
            rw [← hcoeff]
            rw [hw]
            rfl
          have hbc' : (LinearMap.baseChange S ffun) pure =
              ((t : S) ⊗ₜ[(realC (∀ i, K i)).R₁]
                (show (realC (∀ i, K i)).R₁ from ffun qconst)) := by
            simpa [R] using hbc
          calc
            (baseChangeSelfEquiv (fiberRealCHom K i).f₁) ((LinearMap.baseChange S ffun) pure)
                = (baseChangeSelfEquiv (fiberRealCHom K i).f₁)
                    ((t : S) ⊗ₜ[(realC (∀ i, K i)).R₁]
                      (show (realC (∀ i, K i)).R₁ from ffun qconst)) := by
                    exact congrArg (baseChangeSelfEquiv (fiberRealCHom K i).f₁) hbc'
            _ = (fiberRealCHom K i).f₁ (ffun qconst) * (t : S) := by
                    exact baseChangeSelfEquiv_tmul (fiberRealCHom K i).f₁ (t : S)
                      (show (realC (∀ i, K i)).R₁ from ffun qconst)
            _ = (show S from t) * (show S from algebraMap Ei.R₀ Ei.R₁ (l (p i))) := by
                    rw [hF]
                    rw [mul_comm]

/-- The reverse comparison has the expected fiberwise inverse description. -/
lemma fromConstant_fiber_inv
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    ∀ i,
      (fiberConstIso K M i).inv.toLinearMap.comp
        (DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap =
          (productConstFiberBaseChangeLinearEquiv K M i).toLinearMap := by
  have hcore := fromDualConstantLinearMapPairingCore_holds K M
  have hnormalized :=
    fromConstant_represented_left_core_of_fromDualConstantLinearMap K M hcore
  have hscalar := fromConstant_represented_left_scalar_of_core K M hnormalized
  exact fromConstant_fiber_inv_of_represented_dual_apply_scalar K M hscalar


/-- If the reverse comparison has the expected fiberwise description, then the
constant-object composite is the identity.  This isolates the remaining Step 10
fiber calculation. -/
private lemma fromConstant_toConstant_of_fiber_inv
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hfrom : ∀ i,
      (fiberConstIso K M i).inv.toLinearMap.comp
        (DescentDatum.Hom.baseChange (fiberRealCHom K i) (fromConstant K M)).toLinearMap =
          (productConstFiberBaseChangeLinearEquiv K M i).toLinearMap) :
    fromConstant K M ≫ toConstant K M =
      𝟙 ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (productConstModule K M)) := by
  apply hom_ext_of_fiber_baseChange_toLinearMap_eq K
  intro i
  let R := (realC (∀ i, K i)).R₁
  let S := (realC (K i)).R₁
  letI : Algebra R S := (fiberRealCHom K i).f₁.toAlgebra
  let E := productConstFiberBaseChangeLinearEquiv K M i
  have hto := productConstFiberBaseChangeLinearEquiv_toConstant_toLinearMap K M i
  have hf := hfrom i
  have hcomp : (fromConstant K M ≫ toConstant K M).toLinearMap =
      (toConstant K M).toLinearMap.comp (fromConstant K M).toLinearMap := rfl
  let C := (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
    (productConstModule K M)
  have hid : ((𝟙 C : C ⟶ C).toLinearMap) = LinearMap.id := rfl
  simp only [DescentDatum.Hom.baseChange]
  rw [hcomp, hid, LinearMap.baseChange_comp, LinearMap.baseChange_id]
  change E.toLinearMap.comp (LinearMap.baseChange S (toConstant K M).toLinearMap) =
    (fiberConstIso K M i).inv.toLinearMap at hto
  change (fiberConstIso K M i).inv.toLinearMap.comp
      (LinearMap.baseChange S (fromConstant K M).toLinearMap) = E.toLinearMap at hf
  apply (LinearMap.cancel_left E.injective).mp
  rw [← LinearMap.comp_assoc, hto]
  simpa only [LinearMap.comp_id] using hf

/-- Once the constant-object composite is the identity, injectivity of
`toConstant` gives the other composite. -/
private lemma toConstant_fromConstant_of_fromConstant_toConstant
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hC : fromConstant K M ≫ toConstant K M =
      𝟙 ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (productConstModule K M))) :
    toConstant K M ≫ fromConstant K M = 𝟙 M := by
  apply DescentDatum.hom_ext
  have hlin := congrArg DescentDatum.Hom.toLinearMap hC
  change (fromConstant K M).toLinearMap.comp (toConstant K M).toLinearMap = LinearMap.id
  change (toConstant K M).toLinearMap.comp (fromConstant K M).toLinearMap =
    LinearMap.id at hlin
  apply (LinearMap.cancel_left (toConstant_injective K M)).mp
  rw [← LinearMap.comp_assoc, hlin]
  rfl

/-- The composite on the product constant object is the identity. -/
lemma fromConstant_toConstant
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    fromConstant K M ≫ toConstant K M =
      𝟙 ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (productConstModule K M)) :=
  fromConstant_toConstant_of_fiber_inv K M (fromConstant_fiber_inv K M)

/-- The composite on the original descent datum is the identity. -/
lemma toConstant_fromConstant
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    toConstant K M ≫ fromConstant K M = 𝟙 M :=
  toConstant_fromConstant_of_fromConstant_toConstant K M
    (fromConstant_toConstant K M)

/-- Every product descent datum is isomorphic to the constant datum attached to
its product of algebraically closed fiber constants. -/
noncomputable def toConstantIso
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    M ≅ (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
      (productConstModule K M) where
  hom := toConstant K M
  inv := fromConstant K M
  hom_inv_id := toConstant_fromConstant K M
  inv_hom_id := fromConstant_toConstant K M

end

end Novikov.Descent
