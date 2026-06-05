import Novikov.Descent.Product.Fiber
import Novikov.Descent.Abstract.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Duals of uniformly bounded products

This file records the explicit identification between the dual of a product
module over a product of fields and the product of the fiberwise dual modules.
It packages the statement for the uniformly bounded finite-projective products
used in the product descent argument, and relates the ordinary dual of the
product constant module to the dual of its constant descent datum.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract
open scoped BigOperators

namespace Novikov.Miscellany

noncomputable section

universe u

namespace FiniteProjectiveModule

variable (A : Type u) [CommRing A]

/-- Bundle a linear equivalence as an isomorphism of finite projective modules. -/
private noncomputable def isoOfLinearEquiv {P Q : FiniteProjectiveModule A}
    (e : P.M ≃ₗ[A] Q.M) : P ≅ Q where
  hom := e.toLinearMap
  inv := e.symm.toLinearMap
  hom_inv_id := by
    apply LinearMap.ext
    exact e.symm_apply_apply
  inv_hom_id := by
    apply LinearMap.ext
    exact e.apply_symm_apply

/-- Regard an isomorphism of finite projective modules as a linear equivalence. -/
private noncomputable def linearEquivOfIso {P Q : FiniteProjectiveModule A}
    (e : P ≅ Q) : P.M ≃ₗ[A] Q.M :=
  LinearEquiv.ofLinear e.hom e.inv e.inv_hom_id e.hom_inv_id

/-- The ground ring as a finite projective module over itself. -/
noncomputable def self : FiniteProjectiveModule A where
  M := A
  instAddCommGroup := inferInstance
  instModule := inferInstance
  instFinite := inferInstance
  instProjective := inferInstance

/-- The ordinary linear dual of a finite projective module. -/
noncomputable def dual (P : FiniteProjectiveModule A) : FiniteProjectiveModule A :=
  FiniteProjectiveModule.homModule P (FiniteProjectiveModule.self A)

/-- A finite projective module is canonically isomorphic to its double dual. -/
noncomputable def doubleDualIso (P : FiniteProjectiveModule A) :
    P ≅ dual A (dual A P) :=
  isoOfLinearEquiv A (Module.evalEquiv A P.M)

/-- Taking ordinary duals sends an isomorphism of finite projective modules to
an isomorphism in the opposite direction. -/
noncomputable def dualIso {P Q : FiniteProjectiveModule A} (e : P ≅ Q) :
    dual A Q ≅ dual A P :=
  isoOfLinearEquiv A (linearEquivOfIso A e).dualMap

end FiniteProjectiveModule

section PiDual

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)]
variable (P : I → Type u) [∀ i, AddCommGroup (P i)] [∀ i, Module (K i) (P i)]

/-- The dual of a product module over a product of fields is the product of the
fiber duals. -/
private noncomputable def piDualLinearEquiv :
    ((∀ i, P i) →ₗ[(∀ i, K i)] (∀ i, K i)) ≃ₗ[(∀ i, K i)]
      (∀ i, P i →ₗ[K i] K i) where
  toFun f i := by
    classical
    refine {
      toFun := fun p => f (Pi.single i p) i
      map_add' := ?_
      map_smul' := ?_ }
    · intro p q
      have hsingle : Pi.single i (p + q) = Pi.single i p + Pi.single i q := by
        ext j
        by_cases h : j = i
        · subst j
          simp
        · simp [Pi.single_eq_of_ne h]
      rw [hsingle]
      exact congrFun (map_add f (Pi.single i p) (Pi.single i q)) i
    · intro a p
      have hsingle : Pi.single i (a • p) = (Pi.single i a : ∀ i, K i) • Pi.single i p := by
        ext j
        by_cases h : j = i
        · subst j
          simp
        · simp [Pi.single_eq_of_ne h]
      rw [hsingle]
      rw [map_smul]
      simp
  invFun g := {
    toFun := fun p i => g i (p i)
    map_add' := by
      intro p q
      ext i
      exact map_add (g i) (p i) (q i)
    map_smul' := by
      intro a p
      ext i
      exact map_smul (g i) (a i) (p i) }
  left_inv f := by
    classical
    ext p i
    change f (Pi.single i (p i)) i = f p i
    have hsingle : Pi.single i (p i) = (Pi.single i (1 : K i) : ∀ i, K i) • p := by
      ext j
      by_cases h : j = i
      · subst j
        simp
      · simp [Pi.single_eq_of_ne h]
    rw [hsingle]
    rw [map_smul]
    simp
  right_inv g := by
    classical
    ext i p
    simp
  map_add' f g := by
    classical
    ext i p
    rfl
  map_smul' a f := by
    classical
    ext i p
    rfl

end PiDual

namespace FiniteProjectiveModule

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)]
variable (P : ∀ i, FiniteProjectiveModule (K i))
variable (N : ℕ) (hN : ∀ i, Module.finrank (K i) (P i).M ≤ N)

/-- The fiber duals satisfy the same uniform rank bound. -/
lemma piOfUniformFinrank_dual_finrank_le
    (hN : ∀ i, Module.finrank (K i) (P i).M ≤ N) (i : I) :
    Module.finrank (K i) ((dual (K i) (P i)).M) ≤ N := by
  dsimp [dual, self, FiniteProjectiveModule.homModule]
  change Module.finrank (K i) (Module.Dual (K i) (P i).M) ≤ N
  rw [Subspace.dual_finrank_eq]
  exact hN i

/-- The dual of `piOfUniformFinrank` is explicitly the product of the fiber duals. -/
noncomputable def piOfUniformFinrankDualLinearEquiv :
    (dual (∀ i, K i) (piOfUniformFinrank K P N hN)).M ≃ₗ[(∀ i, K i)]
      (piOfUniformFinrank K (fun i => dual (K i) (P i)) N
        (fun i => piOfUniformFinrank_dual_finrank_le K P N hN i)).M := by
  change (((∀ i, (P i).M) →ₗ[(∀ i, K i)] (∀ i, K i)) ≃ₗ[(∀ i, K i)]
      (∀ i, ((P i).M →ₗ[K i] K i)))
  exact piDualLinearEquiv K (fun i => (P i).M)

/-- The dual of `piOfUniformFinrank` as an isomorphism of bundled finite
projective modules. -/
noncomputable def piOfUniformFinrankDualIso :
    dual (∀ i, K i) (piOfUniformFinrank K P N hN) ≅
      piOfUniformFinrank K (fun i => dual (K i) (P i)) N
        (fun i => piOfUniformFinrank_dual_finrank_le K P N hN i) :=
  isoOfLinearEquiv (∀ i, K i) (piOfUniformFinrankDualLinearEquiv K P N hN)

end FiniteProjectiveModule

end

end Novikov.Miscellany

namespace Novikov.Descent

noncomputable section

universe u

/-- Evaluating the constant-descent dual comparison on a pure tensor computes by
base-changing the ordinary coefficient-level pairing. -/
lemma constantDescentDatum_dual_hom_map_eval (E : ExtendedCosimplicialRing)
    (P Q : FiniteProjectiveModule E.R₀)
    (e : Q ≅ FiniteProjectiveModule.dual E.R₀ P)
    (q : Q.M) (p : P.M) :
    (show Module.Dual E.R₁ (constantDescentDatum E P.M).M from
      (constantDescentDatum_dual E P.M).hom.toLinearMap
        ((constantDescentDatumMap E Q (FiniteProjectiveModule.dual E.R₀ P) e.hom).toLinearMap
          ((letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra; (1 : E.R₁) ⊗ₜ[E.R₀] q))))
      ((letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra; (1 : E.R₁) ⊗ₜ[E.R₀] p)) =
    E.π₀ ((show P.M →ₗ[E.R₀] E.R₀ from
      (show Q.M →ₗ[E.R₀] (FiniteProjectiveModule.dual E.R₀ P).M from e.hom) q) p) := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  change (show Module.Dual E.R₁ (constantDescentDatum E P.M).M from
      (constantDescentDatum_dual E P.M).hom.toLinearMap
        ((constantDescentDatumMap E Q (FiniteProjectiveModule.dual E.R₀ P) e.hom).toLinearMap
          ((1 : E.R₁) ⊗ₜ[E.R₀] q)))
      ((1 : E.R₁) ⊗ₜ[E.R₀] p) = E.π₀ ((show P.M →ₗ[E.R₀] E.R₀ from
        (show Q.M →ₗ[E.R₀] (FiniteProjectiveModule.dual E.R₀ P).M from e.hom) q) p)
  rw [constantDescentDatumMap_toLinearMap]
  change (show Module.Dual E.R₁ (constantDescentDatum E P.M).M from
      (constantDescentDatum_dual E P.M).hom.toLinearMap
        ((LinearMap.baseChange E.R₁ (show Q.M →ₗ[E.R₀]
          (FiniteProjectiveModule.dual E.R₀ P).M from e.hom))
          ((1 : E.R₁) ⊗ₜ[E.R₀] q)))
      ((1 : E.R₁) ⊗ₜ[E.R₀] p) = E.π₀ ((show P.M →ₗ[E.R₀] E.R₀ from
        (show Q.M →ₗ[E.R₀] (FiniteProjectiveModule.dual E.R₀ P).M from e.hom) q) p)
  have hb := LinearMap.baseChange_tmul
    (show Q.M →ₗ[E.R₀] (FiniteProjectiveModule.dual E.R₀ P).M from e.hom)
    (1 : E.R₁) q
  rw [hb]
  change ((baseChangeSelfEquiv E.π₀).toLinearMap.comp
      ((homBaseChangeEquiv (R := E.R₀) (M := P.M) (N := E.R₀) E.R₁)
        ((1 : E.R₁) ⊗ₜ[E.R₀] (show P.M →ₗ[E.R₀] E.R₀ from
          (show Q.M →ₗ[E.R₀] (FiniteProjectiveModule.dual E.R₀ P).M from e.hom) q))))
      ((1 : E.R₁) ⊗ₜ[E.R₀] p) =
    E.π₀ ((show P.M →ₗ[E.R₀] E.R₀ from
      (show Q.M →ₗ[E.R₀] (FiniteProjectiveModule.dual E.R₀ P).M from e.hom) q) p)
  rw [homBaseChangeEquiv_tmul]
  simp [LinearMap.baseChange_tmul, baseChangeSelfEquiv_tmul]

/-- Scalar version of `constantDescentDatum_dual_hom_map_eval`. -/
private lemma constantDescentDatum_dual_hom_map_eval_tmul (E : ExtendedCosimplicialRing)
    (P Q : FiniteProjectiveModule E.R₀)
    (e : Q ≅ FiniteProjectiveModule.dual E.R₀ P)
    (t : E.R₁) (q : Q.M) (p : P.M) :
    (show Module.Dual E.R₁ (constantDescentDatum E P.M).M from
      (constantDescentDatum_dual E P.M).hom.toLinearMap
        ((constantDescentDatumMap E Q (FiniteProjectiveModule.dual E.R₀ P) e.hom).toLinearMap
          ((letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra; t ⊗ₜ[E.R₀] q))))
      ((letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra; (1 : E.R₁) ⊗ₜ[E.R₀] p)) =
    t * E.π₀ ((show P.M →ₗ[E.R₀] E.R₀ from
      (show Q.M →ₗ[E.R₀] (FiniteProjectiveModule.dual E.R₀ P).M from e.hom) q) p) := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  change (show Module.Dual E.R₁ (constantDescentDatum E P.M).M from
      (constantDescentDatum_dual E P.M).hom.toLinearMap
        ((constantDescentDatumMap E Q (FiniteProjectiveModule.dual E.R₀ P) e.hom).toLinearMap
          (t ⊗ₜ[E.R₀] q)))
      ((1 : E.R₁) ⊗ₜ[E.R₀] p) = t * E.π₀ ((show P.M →ₗ[E.R₀] E.R₀ from
        (show Q.M →ₗ[E.R₀] (FiniteProjectiveModule.dual E.R₀ P).M from e.hom) q) p)
  rw [constantDescentDatumMap_toLinearMap]
  change (show Module.Dual E.R₁ (constantDescentDatum E P.M).M from
      (constantDescentDatum_dual E P.M).hom.toLinearMap
        ((LinearMap.baseChange E.R₁ (show Q.M →ₗ[E.R₀]
          (FiniteProjectiveModule.dual E.R₀ P).M from e.hom))
          (t ⊗ₜ[E.R₀] q)))
      ((1 : E.R₁) ⊗ₜ[E.R₀] p) = t * E.π₀ ((show P.M →ₗ[E.R₀] E.R₀ from
        (show Q.M →ₗ[E.R₀] (FiniteProjectiveModule.dual E.R₀ P).M from e.hom) q) p)
  have hb := LinearMap.baseChange_tmul
    (show Q.M →ₗ[E.R₀] (FiniteProjectiveModule.dual E.R₀ P).M from e.hom)
    t q
  rw [hb]
  change ((baseChangeSelfEquiv E.π₀).toLinearMap.comp
      ((homBaseChangeEquiv (R := E.R₀) (M := P.M) (N := E.R₀) E.R₁)
        (t ⊗ₜ[E.R₀] (show P.M →ₗ[E.R₀] E.R₀ from
          (show Q.M →ₗ[E.R₀] (FiniteProjectiveModule.dual E.R₀ P).M from e.hom) q))))
      ((1 : E.R₁) ⊗ₜ[E.R₀] p) =
    t * E.π₀ ((show P.M →ₗ[E.R₀] E.R₀ from
      (show Q.M →ₗ[E.R₀] (FiniteProjectiveModule.dual E.R₀ P).M from e.hom) q) p)
  rw [homBaseChangeEquiv_tmul]
  simp [LinearMap.baseChange_tmul, baseChangeSelfEquiv_tmul, Algebra.smul_def, mul_comm]

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)] [∀ i, IsAlgClosed (K i)]

/-- The underlying linear equivalence between the fiber of the dual descent datum
and the dual of the fiber descent datum. -/
noncomputable def fiberDescentDatumDualLinearEquiv
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    (fiberDescentDatum K M.dual i).M ≃ₗ[(realC (K i)).R₁]
      (fiberDescentDatum K M i).dual.M :=
  (fiberRealCHom K i).baseChangeDualLinearEquiv M

omit [∀ i, IsAlgClosed (K i)] in
/-- The canonical descent-data morphism from the fiber of `M.dual` to the dual
of the fiber of `M`. -/
noncomputable def fiberDescentDatumDualHom
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    fiberDescentDatum K M.dual i ⟶ (fiberDescentDatum K M i).dual :=
  (fiberRealCHom K i).baseChangeDualHom M

omit [∀ i, IsAlgClosed (K i)] in
@[simp]
lemma fiberDescentDatumDualHom_toLinearMap
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    (fiberDescentDatumDualHom K M i).toLinearMap =
      (fiberDescentDatumDualLinearEquiv K M i).toLinearMap := by
  exact CosimplicialRingHom.baseChangeDualHom_toLinearMap (fiberRealCHom K i) M

omit [∀ i, IsAlgClosed (K i)] in
/-- The canonical descent-level identification of the fiber of `M.dual` with the
dual of the fiber of `M`, induced by abstract dual/base-change compatibility. -/
noncomputable def fiberDescentDatumDualCanonicalIso
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    fiberDescentDatum K M.dual i ≅ (fiberDescentDatum K M i).dual :=
  DescentDatum.isoOfLinearEquiv (fiberDescentDatumDualHom K M i)
    (fiberDescentDatumDualLinearEquiv K M i)
    (fiberDescentDatumDualHom_toLinearMap K M i)

omit [∀ i, IsAlgClosed (K i)] in
@[simp]
private lemma fiberDescentDatumDualCanonicalIso_hom_toLinearMap
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    (fiberDescentDatumDualCanonicalIso K M i).hom.toLinearMap =
      (fiberDescentDatumDualLinearEquiv K M i).toLinearMap := by
  rfl

omit [∀ i, IsAlgClosed (K i)] in
@[simp]
private lemma fiberDescentDatumDualCanonicalIso_inv_toLinearMap
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    (fiberDescentDatumDualCanonicalIso K M i).inv.toLinearMap =
      (fiberDescentDatumDualLinearEquiv K M i).symm.toLinearMap := by
  rfl

/-- The descent-level identification of the fiber of `M.dual` with the dual of
the fiber of `M` used in the source alignment.  It is the canonical comparison
induced by abstract dual/base-change compatibility. -/
noncomputable def fiberDescentDatumDualIso
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    fiberDescentDatum K M.dual i ≅ (fiberDescentDatum K M i).dual :=
  fiberDescentDatumDualCanonicalIso K M i

/-- The chosen constant object for the fiber of `M.dual`, identified with the
linear dual of the chosen constant object for the fiber of `M`. -/
noncomputable def fiberConstDescentDatumDualLinearEquiv
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I) :
    (fiberConstDescentDatum K M.dual i).M ≃ₗ[(realC (K i)).R₁]
      Module.Dual (realC (K i)).R₁ (fiberConstDescentDatum K M i).M := by
  let e : fiberConstDescentDatum K M.dual i ≅ (fiberConstDescentDatum K M i).dual :=
    (fiberConstIso K M.dual i).trans
      ((fiberDescentDatumDualIso K M i).trans
        (DescentDatum.dualIso (fiberConstIso K M i)))
  exact LinearEquiv.ofLinear e.hom.toLinearMap e.inv.toLinearMap
    (congrArg DescentDatum.Hom.toLinearMap e.inv_hom_id)
    (congrArg DescentDatum.Hom.toLinearMap e.hom_inv_id)

/-- If the fiber of `M.dual` has been identified with the dual of the fiber of
`M` at descent level, then the chosen constant datum for `M.dual` is identified
with the constant datum attached to the ordinary dual of the chosen constant
fiber module for `M` by the compatible chain of trivializations. -/
private noncomputable def fiberConstDescentDatumDualIsoOf
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I)
    (hDual : fiberDescentDatum K M.dual i ≅ (fiberDescentDatum K M i).dual) :
    fiberConstDescentDatum K M.dual i ≅
      (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (K i)).obj
        (FiniteProjectiveModule.dual (K i) (fiberConstModule K M i)) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  let Ftor := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (K i)
  let P := fiberConstModule K M i
  letI : Module E.R₀ P.M := P.instModule
  letI : Module.Finite E.R₀ P.M := P.instFinite
  letI : Module.Projective E.R₀ P.M := P.instProjective
  let eDualConst : Ftor.obj (FiniteProjectiveModule.dual (K i) P) ≅
      (fiberConstDescentDatum K M i).dual := by
    change constantDescentDatum E (P.M →ₗ[E.R₀] E.R₀) ≅
      (constantDescentDatum E P.M).dual
    exact Abstract.constantDescentDatum_dual E P.M
  exact ((fiberConstIso K M.dual i).trans hDual).trans
    ((DescentDatum.dualIso (fiberConstIso K M i)).trans eDualConst.symm)

/-- The corresponding compatible finite-projective-module isomorphism, obtained
by fully faithful descent from `fiberConstDescentDatumDualIsoOf`.  This is the
replacement needed for the final inverse proof once a descent-level fiber/dual
comparison is available. -/
noncomputable def fiberConstModuleDualIsoOf
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I)
    (hDual : fiberDescentDatum K M.dual i ≅ (fiberDescentDatum K M i).dual) :
    fiberConstModule K M.dual i ≅ FiniteProjectiveModule.dual (K i) (fiberConstModule K M i) := by
  let Ftor := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (K i)
  have hFF : Ftor.FullyFaithful := vectToNovikovDescent_fullyFaithful (⊤ : AddSubgroup ℝ) (K i)
  letI : Ftor.Full := hFF.full
  letI : Ftor.Faithful := hFF.faithful
  exact Ftor.preimageIso (fiberConstDescentDatumDualIsoOf K M i hDual)

/-- Applying constant descent to `fiberConstModuleDualIsoOf` recovers the
specified compatible descent-level comparison. -/
private lemma fiberConstModuleDualIsoOf_mapIso
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I)
    (hDual : fiberDescentDatum K M.dual i ≅ (fiberDescentDatum K M i).dual) :
    ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (K i)).mapIso
      (fiberConstModuleDualIsoOf K M i hDual)) =
    fiberConstDescentDatumDualIsoOf K M i hDual := by
  let Ftor := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (K i)
  have hFF : Ftor.FullyFaithful := vectToNovikovDescent_fullyFaithful (⊤ : AddSubgroup ℝ) (K i)
  letI : Ftor.Full := hFF.full
  letI : Ftor.Faithful := hFF.faithful
  ext
  simp only [fiberConstModuleDualIsoOf, Functor.mapIso_hom, Functor.preimageIso_hom,
    Functor.map_preimage]

/-- Pairing formula for `fiberConstModuleDualIsoOf`: if the chosen constant
module for `M.dual` represents a fiber-dual functional by the pure tensor
`t ⊗ q`, evaluation is multiplication by `t` of the coefficient-level pairing. -/
lemma fiberConstModuleDualIsoOf_pairing_of_tmul_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) (i : I)
    (hDual : fiberDescentDatum K M.dual i ≅ (fiberDescentDatum K M i).dual)
    (η : Module.Dual (realC (K i)).R₁ (fiberConstDescentDatum K M i).M)
    (t : (realC (K i)).R₁)
    (q : (fiberConstModule K M.dual i).M) (p : (fiberConstModule K M i).M)
    (hθ : (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
      let Q := fiberConstModule K M.dual i
      letI : Module E.R₀ Q.M := Q.instModule
      letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
      (fiberConstIso K M.dual i).inv.toLinearMap
        (hDual.inv.toLinearMap (η.comp (fiberConstIso K M i).inv.toLinearMap)) =
      ((show E.R₁ from t) ⊗ₜ[E.R₀] q))) :
    (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
     letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
     (show E.R₁ from t) * algebraMap E.R₀ E.R₁
      ((show (fiberConstModule K M i).M →ₗ[K i] K i from
        ((show (fiberConstModule K M.dual i).M →ₗ[K i]
            (FiniteProjectiveModule.dual (K i) (fiberConstModule K M i)).M from
          (fiberConstModuleDualIsoOf K M i hDual).hom) q)) p)) =
      (let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
       letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
       η ((1 : E.R₁) ⊗ₜ[E.R₀] p)) := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  let Ftor := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (K i)
  let P := fiberConstModule K M i
  let Q := fiberConstModule K M.dual i
  letI : Module E.R₀ P.M := P.instModule
  letI : Module.Finite E.R₀ P.M := P.instFinite
  letI : Module.Projective E.R₀ P.M := P.instProjective
  letI : Module E.R₀ Q.M := Q.instModule
  let e := fiberConstModuleDualIsoOf K M i hDual
  let eDualConst : Ftor.obj (FiniteProjectiveModule.dual (K i) P) ≅
      (fiberConstDescentDatum K M i).dual := by
    change constantDescentDatum E (P.M →ₗ[E.R₀] E.R₀) ≅
      (constantDescentDatum E P.M).dual
    exact Abstract.constantDescentDatum_dual E P.M
  have heval := constantDescentDatum_dual_hom_map_eval_tmul E P Q e t q p
  have hmap := fiberConstModuleDualIsoOf_mapIso K M i hDual
  have hhom := congrArg Iso.hom hmap
  have happ := LinearMap.congr_fun (congrArg DescentDatum.Hom.toLinearMap hhom)
    (t ⊗ₜ[E.R₀] q)
  have happ2 := congrArg (fun z => eDualConst.hom.toLinearMap z) happ
  have happ3 := congrArg (fun l : Module.Dual E.R₁ (fiberConstDescentDatum K M i).M =>
    l ((1 : E.R₁) ⊗ₜ[E.R₀] p)) happ2
  have hcomp :
      (show Module.Dual E.R₁ (fiberConstDescentDatum K M i).M from
        eDualConst.hom.toLinearMap
          (((fiberConstIso K M.dual i).hom ≫ hDual.hom ≫
            (DescentDatum.dualIso (fiberConstIso K M i)).hom ≫
            (constantDescentDatum_dual E P.M).inv).toLinearMap
            (t ⊗ₜ[E.R₀] q)))
        ((1 : E.R₁) ⊗ₜ[E.R₀] p) = η ((1 : E.R₁) ⊗ₜ[E.R₀] p) := by
    rw [← hθ]
    change (show Module.Dual E.R₁ (fiberConstDescentDatum K M i).M from
      (constantDescentDatum_dual E P.M).hom.toLinearMap
        ((constantDescentDatum_dual E P.M).inv.toLinearMap
          ((DescentDatum.dualIso (fiberConstIso K M i)).hom.toLinearMap
            (hDual.hom.toLinearMap
              ((fiberConstIso K M.dual i).hom.toLinearMap
                ((fiberConstIso K M.dual i).inv.toLinearMap
                  (hDual.inv.toLinearMap
                    (η.comp (fiberConstIso K M i).inv.toLinearMap))))))))
        ((1 : E.R₁) ⊗ₜ[E.R₀] p) = η ((1 : E.R₁) ⊗ₜ[E.R₀] p)
    have h₁ : (fiberConstIso K M.dual i).hom.toLinearMap.comp
          (fiberConstIso K M.dual i).inv.toLinearMap = LinearMap.id := by
      exact congrArg DescentDatum.Hom.toLinearMap (fiberConstIso K M.dual i).inv_hom_id
    have h₂ : hDual.hom.toLinearMap.comp hDual.inv.toLinearMap = LinearMap.id := by
      exact congrArg DescentDatum.Hom.toLinearMap hDual.inv_hom_id
    have h₃ : (constantDescentDatum_dual E P.M).hom.toLinearMap.comp
          (constantDescentDatum_dual E P.M).inv.toLinearMap = LinearMap.id := by
      exact congrArg DescentDatum.Hom.toLinearMap (constantDescentDatum_dual E P.M).inv_hom_id
    have h₄ : (fiberConstIso K M i).inv.toLinearMap.comp
          (fiberConstIso K M i).hom.toLinearMap = LinearMap.id := by
      exact congrArg DescentDatum.Hom.toLinearMap (fiberConstIso K M i).hom_inv_id
    rw [show (fiberConstIso K M.dual i).hom.toLinearMap
          ((fiberConstIso K M.dual i).inv.toLinearMap
            (hDual.inv.toLinearMap (η.comp (fiberConstIso K M i).inv.toLinearMap))) =
        hDual.inv.toLinearMap (η.comp (fiberConstIso K M i).inv.toLinearMap) from
      LinearMap.congr_fun h₁ _]
    rw [show hDual.hom.toLinearMap
          (hDual.inv.toLinearMap (η.comp (fiberConstIso K M i).inv.toLinearMap)) =
        η.comp (fiberConstIso K M i).inv.toLinearMap from LinearMap.congr_fun h₂ _]
    rw [show (constantDescentDatum_dual E P.M).hom.toLinearMap
          ((constantDescentDatum_dual E P.M).inv.toLinearMap
            ((DescentDatum.dualIso (fiberConstIso K M i)).hom.toLinearMap
              (η.comp (fiberConstIso K M i).inv.toLinearMap))) =
        (DescentDatum.dualIso (fiberConstIso K M i)).hom.toLinearMap
          (η.comp (fiberConstIso K M i).inv.toLinearMap) from LinearMap.congr_fun h₃ _]
    change η ((fiberConstIso K M i).inv.toLinearMap ((fiberConstIso K M i).hom.toLinearMap
        ((1 : E.R₁) ⊗ₜ[E.R₀] p))) = η ((1 : E.R₁) ⊗ₜ[E.R₀] p)
    rw [show (fiberConstIso K M i).inv.toLinearMap ((fiberConstIso K M i).hom.toLinearMap
        ((1 : E.R₁) ⊗ₜ[E.R₀] p)) = ((1 : E.R₁) ⊗ₜ[E.R₀] p) from
      LinearMap.congr_fun h₄ _]
  have hlink :
      (show Module.Dual E.R₁ (fiberConstDescentDatum K M i).M from
        eDualConst.hom.toLinearMap (((Ftor.map e.hom).toLinearMap
          (t ⊗ₜ[E.R₀] q))))
        ((1 : E.R₁) ⊗ₜ[E.R₀] p) =
      (show Module.Dual E.R₁ (fiberConstDescentDatum K M i).M from
        eDualConst.hom.toLinearMap
          (((fiberConstIso K M.dual i).hom ≫ hDual.hom ≫
            (DescentDatum.dualIso (fiberConstIso K M i)).hom ≫
            (constantDescentDatum_dual E P.M).inv).toLinearMap
            (t ⊗ₜ[E.R₀] q)))
        ((1 : E.R₁) ⊗ₜ[E.R₀] p) := by
    simpa [e, eDualConst, fiberConstDescentDatumDualIsoOf, E, P, Q] using happ3
  exact heval.symm.trans (hlink.trans hcomp)

/-- Product of the duals of the chosen constant fiber modules. -/
noncomputable def productConstModuleFiberDuals
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    FiniteProjectiveModule (∀ i, K i) :=
  FiniteProjectiveModule.piOfUniformFinrank K
    (fun i => FiniteProjectiveModule.dual (K i) (fiberConstModule K M i))
    (productFiberRankBoundN K M)
    (fun i => FiniteProjectiveModule.piOfUniformFinrank_dual_finrank_le K
      (fiberConstModule K M) (productFiberRankBoundN K M)
      (fiberConstModule_finrank_le K M) i)

/-- The product constant module for `M.dual`, identified with the product of
fiber duals using a fiberwise descent-level dual comparison. -/
noncomputable def productConstModuleDualFiberIsoOf
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hDual : ∀ i, fiberDescentDatum K M.dual i ≅ (fiberDescentDatum K M i).dual) :
    productConstModule K M.dual ≅ productConstModuleFiberDuals K M :=
  FiniteProjectiveModule.piOfUniformFinrankIso K
    (fiberConstModule K M.dual)
    (productFiberRankBoundN K M.dual)
    (fiberConstModule_finrank_le K M.dual)
    (Q := fun i => FiniteProjectiveModule.dual (K i) (fiberConstModule K M i))
    (NQ := productFiberRankBoundN K M)
    (hQ := fun i => FiniteProjectiveModule.piOfUniformFinrank_dual_finrank_le K
      (fiberConstModule K M) (productFiberRankBoundN K M)
      (fiberConstModule_finrank_le K M) i)
    (fun i => fiberConstModuleDualIsoOf K M i (hDual i))

/-- The ordinary dual of the product constant module is the product of the fiber
duals. -/
private noncomputable def productConstModuleDualLinearEquiv
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    (FiniteProjectiveModule.dual (∀ i, K i) (productConstModule K M)).M
      ≃ₗ[(∀ i, K i)]
    (FiniteProjectiveModule.piOfUniformFinrank K
      (fun i => FiniteProjectiveModule.dual (K i) (fiberConstModule K M i))
      (productFiberRankBoundN K M)
      (fun i => FiniteProjectiveModule.piOfUniformFinrank_dual_finrank_le K
        (fiberConstModule K M) (productFiberRankBoundN K M)
        (fiberConstModule_finrank_le K M) i)).M :=
  FiniteProjectiveModule.piOfUniformFinrankDualLinearEquiv K
    (fiberConstModule K M) (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M)

/-- Bundled isomorphism from the ordinary dual of the product constant module to
product of the fiber duals. -/
private noncomputable def productConstModuleDualIso
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    FiniteProjectiveModule.dual (∀ i, K i) (productConstModule K M) ≅
      productConstModuleFiberDuals K M :=
  FiniteProjectiveModule.piOfUniformFinrankDualIso K
    (fiberConstModule K M) (productFiberRankBoundN K M) (fiberConstModule_finrank_le K M)

/-- The product constant module is canonically isomorphic to its double dual. -/
private noncomputable def productConstModuleDoubleDualIso
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    productConstModule K M ≅
      FiniteProjectiveModule.dual (∀ i, K i)
        (FiniteProjectiveModule.dual (∀ i, K i) (productConstModule K M)) :=
  FiniteProjectiveModule.doubleDualIso (∀ i, K i) (productConstModule K M)

/-- Dualizing the product-dual identification identifies the dual of the product
of fiber duals with the double dual of the product constant module. -/
private noncomputable def productConstModuleFiberDualsDualIsoDoubleDual
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    FiniteProjectiveModule.dual (∀ i, K i) (productConstModuleFiberDuals K M) ≅
      FiniteProjectiveModule.dual (∀ i, K i)
        (FiniteProjectiveModule.dual (∀ i, K i) (productConstModule K M)) :=
  FiniteProjectiveModule.dualIso (∀ i, K i) (productConstModuleDualIso K M)

/-- The dual of the product of fiber duals is the original product constant
module. -/
noncomputable def productConstModuleFiberDualsDualIsoProduct
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    FiniteProjectiveModule.dual (∀ i, K i) (productConstModuleFiberDuals K M) ≅
      productConstModule K M :=
  (productConstModuleFiberDualsDualIsoDoubleDual K M).trans
    (productConstModuleDoubleDualIso K M).symm

/-- Pointwise formula for the inverse of
`productConstModuleFiberDualsDualIsoProduct`: it is double-dual evaluation on
fiberwise duals. -/
@[simp]
private lemma productConstModuleFiberDualsDualIsoProduct_inv_apply
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (p : (productConstModule K M).M)
    (q : (productConstModuleFiberDuals K M).M) (i : I) :
    (let L : (productConstModule K M).M →ₗ[(∀ i, K i)]
          (FiniteProjectiveModule.dual (∀ i, K i) (productConstModuleFiberDuals K M)).M :=
        (productConstModuleFiberDualsDualIsoProduct K M).inv;
      let F : (productConstModuleFiberDuals K M).M →ₗ[(∀ i, K i)] (∀ i, K i) := L p;
      F q i) =
      (let l : (fiberConstModule K M i).M →ₗ[K i] K i := q i;
       l (p i)) := by
  dsimp
  change (let e : FiniteProjectiveModule.dual (∀ i, K i) (productConstModule K M) ≅
        productConstModuleFiberDuals K M := productConstModuleDualIso K M;
      let L : (productConstModuleFiberDuals K M).M →ₗ[(∀ i, K i)]
          (FiniteProjectiveModule.dual (∀ i, K i) (productConstModule K M)).M := e.inv;
      let F : (productConstModule K M).M →ₗ[(∀ i, K i)] (∀ i, K i) := L q;
      F p i) = _
  rfl

/-- Evaluation formula for the source functional obtained by identifying the
product constant module of `M.dual` with the product of ordinary duals using a
specified fiberwise descent-level dual comparison. -/
lemma productConstModule_sourceFunctionalOf_apply
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hDual : ∀ i, fiberDescentDatum K M.dual i ≅ (fiberDescentDatum K M i).dual)
    (p : (productConstModule K M).M)
    (q : (productConstModule K M.dual).M) (i : I) :
    (let L : (productConstModule K M).M →ₗ[(∀ i, K i)]
        (FiniteProjectiveModule.dual (∀ i, K i) (productConstModule K M.dual)).M :=
      ((productConstModuleFiberDualsDualIsoProduct K M).inv ≫
        (FiniteProjectiveModule.dualIso (∀ i, K i)
          (productConstModuleDualFiberIsoOf K M hDual)).hom);
     let F : (productConstModule K M.dual).M →ₗ[(∀ i, K i)] (∀ i, K i) := L p;
     F q i) =
    (let e : (fiberConstModule K M.dual i).M →ₗ[K i]
        (FiniteProjectiveModule.dual (K i) (fiberConstModule K M i)).M :=
        (fiberConstModuleDualIsoOf K M i (hDual i)).hom;
     let l : (fiberConstModule K M i).M →ₗ[K i] K i := e (q i);
     l (p i)) := by
  dsimp
  change (let L : (productConstModule K M).M →ₗ[(∀ i, K i)]
        (FiniteProjectiveModule.dual (∀ i, K i) (productConstModuleFiberDuals K M)).M :=
      (productConstModuleFiberDualsDualIsoProduct K M).inv;
    let F : (productConstModuleFiberDuals K M).M →ₗ[(∀ i, K i)] (∀ i, K i) := L p;
    F ((show (productConstModule K M.dual).M →ₗ[(∀ i, K i)]
        (productConstModuleFiberDuals K M).M from
      (productConstModuleDualFiberIsoOf K M hDual).hom) q) i) = _
  rw [productConstModuleFiberDualsDualIsoProduct_inv_apply]
  unfold productConstModuleDualFiberIsoOf
  have happ := FiniteProjectiveModule.piOfUniformFinrankIso_hom_apply
    (K := K) (P := fiberConstModule K M.dual)
    (N := productFiberRankBoundN K M.dual)
    (hN := fiberConstModule_finrank_le K M.dual)
    (Q := fun i => FiniteProjectiveModule.dual (K i) (fiberConstModule K M i))
    (NQ := productFiberRankBoundN K M)
    (hQ := fun i => FiniteProjectiveModule.piOfUniformFinrank_dual_finrank_le K
      (fiberConstModule K M) (productFiberRankBoundN K M)
      (fiberConstModule_finrank_le K M) i)
    (e := fun i => fiberConstModuleDualIsoOf K M i (hDual i)) q i
  exact congrArg (fun l : (fiberConstModule K M i).M →ₗ[K i] K i => l (p i)) happ

/-- Constant descent commutes with taking the ordinary dual of the product
constant module. -/
noncomputable def productConstDescentDatumDualIso
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (FiniteProjectiveModule.dual (∀ i, K i) (productConstModule K M)) ≅
      ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (productConstModule K M)).dual := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (∀ i, K i)
  letI : Module E.R₀ (productConstModule K M).M := (productConstModule K M).instModule
  letI : Module.Finite E.R₀ (productConstModule K M).M :=
    (productConstModule K M).instFinite
  letI : Module.Projective E.R₀ (productConstModule K M).M :=
    (productConstModule K M).instProjective
  change constantDescentDatum E ((productConstModule K M).M →ₗ[E.R₀] E.R₀) ≅
    (constantDescentDatum E (productConstModule K M).M).dual
  exact Abstract.constantDescentDatum_dual E (productConstModule K M).M

end

end Novikov.Descent
