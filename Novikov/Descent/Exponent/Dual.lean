import Novikov.Descent.Exponent.Restrict
import Novikov.Descent.Abstract.Dual

/-!
# Duality for exponent restriction

This file applies exponent restriction to the dual descent datum.  The resulting
map on duals is used to construct a right inverse to the restricted real
trivialization, proving that the latter is an isomorphism.
-/

open CategoryTheory TensorProduct
open Novikov.Miscellany Novikov.Descent.Abstract

namespace Novikov.Descent

noncomputable section

universe u

variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ]
variable (Γ : S)
variable {A : Type u} [CommRing A]

private noncomputable def exponentBaseChangeDualIso
    (M : NovikovDescentDatum Γ A) :
    M.dual.baseChange (exponentInclusionCHom Γ A) ≅
      (M.baseChange (exponentInclusionCHom Γ A)).dual :=
  DescentDatum.isoOfLinearEquiv
    ((exponentInclusionCHom Γ A).baseChangeDualHom M)
    ((exponentInclusionCHom Γ A).baseChangeDualLinearEquiv M)
    ((exponentInclusionCHom Γ A).baseChangeDualHom_toLinearMap M)

/-- Constant Novikov descent commutes with taking finite-projective duals. -/
noncomputable def novikovConstantDualIso
    (P : FiniteProjectiveModule.{u, u} A) :
    (vectToNovikovDescent Γ A).obj (FiniteProjectiveModule.dual A P) ≅
      ((vectToNovikovDescent Γ A).obj P).dual := by
  let E := novikovExtendedCosimplicialRing Γ A
  letI : Module E.R₀ P.M := P.instModule
  letI : Module.Finite E.R₀ P.M := P.instFinite
  letI : Module.Projective E.R₀ P.M := P.instProjective
  letI : Module E.R₀ (P.M →ₗ[A] A) := by
    change Module A (P.M →ₗ[A] A)
    infer_instance
  letI : Module.Finite E.R₀ (P.M →ₗ[A] A) := by
    change Module.Finite A (P.M →ₗ[A] A)
    infer_instance
  letI : Module.Projective E.R₀ (P.M →ₗ[A] A) := by
    change Module.Projective A (P.M →ₗ[A] A)
    infer_instance
  change constantDescentDatum E (P.M →ₗ[A] A) ≅
    (constantDescentDatum E P.M).dual
  exact constantDescentDatum_dual E P.M

/-- The real trivialization induced on the dual datum.  Its final comparison is
chosen through the base change of `novikovConstantDualIso`; this makes the
restricted primal and dual maps formally adjoint after exponent base change. -/
noncomputable def realDualTrivialization
    (M : NovikovDescentDatum Γ A)
    (P : FiniteProjectiveModule.{u, u} A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    M.dual.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj
        (FiniteProjectiveModule.dual A P) := by
  let F := exponentInclusionCHom Γ A
  let K := (vectToNovikovDescent Γ A).obj P
  let B := (vectToNovikovDescent Γ A).obj (FiniteProjectiveModule.dual A P)
  let kP := exponentConstantBaseChangeIso Γ A P
  let kD := exponentConstantBaseChangeIso Γ A (FiniteProjectiveModule.dual A P)
  let c := novikovConstantDualIso Γ P
  let b : B.baseChange F ≅ (K.baseChange F).dual :=
    ((Novikov.Descent.Abstract.baseChangeFunctor F).mapIso c).trans
      (exponentBaseChangeDualIso Γ K)
  exact (exponentBaseChangeDualIso Γ M).trans
    ((DescentDatum.dualIso e).symm.trans
      ((DescentDatum.dualIso kP).trans (b.symm.trans kD)))

/-- Restrict the induced real trivialization of the dual descent datum. -/
noncomputable def restrictRealDualTrivialization
    (M : NovikovDescentDatum Γ A)
    (P : FiniteProjectiveModule.{u, u} A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    M.dual ⟶ (vectToNovikovDescent Γ A).obj
      (FiniteProjectiveModule.dual A P) :=
  restrictRealTrivialization M.dual (FiniteProjectiveModule.dual A P)
    (realDualTrivialization Γ M P e)

private lemma restrictRealDualTrivialization_comp_dual
    (M : NovikovDescentDatum Γ A)
    (P : FiniteProjectiveModule.{u, u} A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    (restrictRealDualTrivialization Γ M P e).toLinearMap.comp
        (restrictRealTrivialization M P e).dual.toLinearMap =
      (novikovConstantDualIso Γ P).inv.toLinearMap := by
  let C := novikovCosimplicialRing Γ A
  let D := novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A
  let F := exponentInclusionCHom Γ A
  let K := (vectToNovikovDescent Γ A).obj P
  let B := (vectToNovikovDescent Γ A).obj (FiniteProjectiveModule.dual A P)
  let g := restrictRealTrivialization M P e
  let h := restrictRealDualTrivialization Γ M P e
  let c := novikovConstantDualIso Γ P
  letI : Algebra C.R₁ D.R₁ := F.f₁.toAlgebra
  apply linearMap_eq_of_baseChange_eq_of_injective
    (exponentInclusionCHom_f₁_injective Γ A)
  rw [LinearMap.baseChange_comp]
  apply LinearMap.ext
  intro x
  let kP := exponentConstantBaseChangeIso Γ A P
  let kD := exponentConstantBaseChangeIso Γ A (FiniteProjectiveModule.dual A P)
  let d := realDualTrivialization Γ M P e
  let gdR := LinearMap.baseChange D.R₁ g.dual.toLinearMap
  let hR := LinearMap.baseChange D.R₁ h.toLinearMap
  let cInvR := LinearMap.baseChange D.R₁ c.inv.toLinearMap
  let kDe : (B.baseChange F).M ≃ₗ[D.R₁]
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj
        (FiniteProjectiveModule.dual A P)).M :=
    LinearEquiv.ofLinear kD.hom.toLinearMap kD.inv.toLinearMap
      (congrArg DescentDatum.Hom.toLinearMap kD.inv_hom_id)
      (congrArg DescentDatum.Hom.toLinearMap kD.hom_inv_id)
  apply kDe.injective
  have hh := LinearMap.congr_fun
    (restrictRealTrivialization_baseChange M.dual
      (FiniteProjectiveModule.dual A P) d) (gdR x)
  change kD.hom.toLinearMap (hR (gdR x)) = _
  calc
    kD.hom.toLinearMap (hR (gdR x)) = d.hom.toLinearMap (gdR x) := hh
    _ = kD.hom.toLinearMap (cInvR x) := by
      let βM := exponentBaseChangeDualIso Γ M
      let βK := exponentBaseChangeDualIso Γ K
      let cR := (Novikov.Descent.Abstract.baseChangeFunctor F).mapIso c
      let b : B.baseChange F ≅ (K.baseChange F).dual := cR.trans βK
      let z := (DescentDatum.dualIso kP).hom.toLinearMap
        ((DescentDatum.dualIso e).inv.toLinearMap
          (βM.hom.toLinearMap (gdR x)))
      change kD.hom.toLinearMap (b.inv.toLinearMap z) =
        kD.hom.toLinearMap (cInvR x)
      change kDe (b.inv.toLinearMap z) = kDe (cInvR x)
      apply congrArg kDe
      let bE : (B.baseChange F).M ≃ₗ[D.R₁] (K.baseChange F).dual.M :=
        LinearEquiv.ofLinear b.hom.toLinearMap b.inv.toLinearMap
          (congrArg DescentDatum.Hom.toLinearMap b.inv_hom_id)
          (congrArg DescentDatum.Hom.toLinearMap b.hom_inv_id)
      apply bE.injective
      have hleft : b.hom.toLinearMap (b.inv.toLinearMap z) = z := by
        exact LinearMap.congr_fun
          (congrArg DescentDatum.Hom.toLinearMap b.inv_hom_id) z
      change b.hom.toLinearMap (b.inv.toLinearMap z) =
        b.hom.toLinearMap (cInvR x)
      rw [hleft]
      have hright : b.hom.toLinearMap (cInvR x) = βK.hom.toLinearMap x := by
        dsimp [b, cR, cInvR]
        change βK.hom.toLinearMap
            ((LinearMap.baseChange D.R₁ c.hom.toLinearMap)
              ((LinearMap.baseChange D.R₁ c.inv.toLinearMap) x)) =
          βK.hom.toLinearMap x
        congr 1
        rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
        have hc : c.hom.toLinearMap.comp c.inv.toLinearMap = LinearMap.id :=
          congrArg DescentDatum.Hom.toLinearMap c.inv_hom_id
        rw [hc, LinearMap.baseChange_id]
        rfl
      rw [hright]
      dsimp [z]
      apply LinearMap.ext
      intro q
      let qM := e.inv.toLinearMap (kP.hom.toLinearMap q)
      let gR := LinearMap.baseChange D.R₁ g.toLinearMap
      let φM : Module.Dual D.R₁ (M.baseChange F).M := βM.hom.toLinearMap (gdR x)
      let φK : Module.Dual D.R₁ (K.baseChange F).M := βK.hom.toLinearMap x
      have hnat := F.baseChangeDualLinearEquiv_dual_apply g x qM
      change φM qM = φK (gR qM) at hnat
      have hgMap := restrictRealTrivialization_baseChange M P e
      have hg := LinearMap.congr_fun hgMap qM
      change kP.hom.toLinearMap (gR qM) = e.hom.toLinearMap qM at hg
      let kPe : (K.baseChange F).M ≃ₗ[D.R₁]
          ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M :=
        LinearEquiv.ofLinear kP.hom.toLinearMap kP.inv.toLinearMap
          (congrArg DescentDatum.Hom.toLinearMap kP.inv_hom_id)
          (congrArg DescentDatum.Hom.toLinearMap kP.hom_inv_id)
      have hgq : gR qM = q := by
        apply kPe.injective
        change kP.hom.toLinearMap (gR qM) = kP.hom.toLinearMap q
        rw [hg]
        dsimp [qM]
        exact LinearMap.congr_fun
          (congrArg DescentDatum.Hom.toLinearMap e.inv_hom_id)
          (kP.hom.toLinearMap q)
      change φM qM = φK q
      rw [hnat, hgq]

private noncomputable def constantToDualDual
    (P : FiniteProjectiveModule.{u, u} A) :
    (vectToNovikovDescent Γ A).obj P ⟶
      ((vectToNovikovDescent Γ A).obj
        (FiniteProjectiveModule.dual A P)).dual := by
  let K := (vectToNovikovDescent Γ A).obj P
  let c := novikovConstantDualIso Γ P
  exact (DescentDatum.doubleDualIso K).hom ≫ (DescentDatum.dualIso c).hom

private noncomputable def restrictedDualToDoubleDual
    (M : NovikovDescentDatum Γ A)
    (P : FiniteProjectiveModule.{u, u} A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    (vectToNovikovDescent Γ A).obj P ⟶ M.dual.dual :=
  constantToDualDual Γ P ≫ (restrictRealDualTrivialization Γ M P e).dual

/-- The map from the constant object back to `M`, obtained by dualizing the
restricted dual trivialization and applying double-dual evaluation. -/
noncomputable def fromRestrictedDual
    (M : NovikovDescentDatum Γ A)
    (P : FiniteProjectiveModule.{u, u} A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    (vectToNovikovDescent Γ A).obj P ⟶ M :=
  restrictedDualToDoubleDual Γ M P e ≫ (DescentDatum.doubleDualIso M).inv

/-- The duality-produced map is a right inverse to the restricted real
trivialization. -/
lemma restrictRealTrivialization_comp_fromRestrictedDual
    (M : NovikovDescentDatum Γ A)
    (P : FiniteProjectiveModule.{u, u} A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    (restrictRealTrivialization M P e).toLinearMap.comp
        (fromRestrictedDual Γ M P e).toLinearMap = LinearMap.id := by
  let C := novikovCosimplicialRing Γ A
  let K := (vectToNovikovDescent Γ A).obj P
  let B := (vectToNovikovDescent Γ A).obj (FiniteProjectiveModule.dual A P)
  let g := restrictRealTrivialization M P e
  let h := restrictRealDualTrivialization Γ M P e
  let c := novikovConstantDualIso Γ P
  let a := constantToDualDual Γ P
  let q := fromRestrictedDual Γ M P e
  apply LinearMap.ext
  intro p
  apply (Module.evalEquiv C.R₁ K.M).injective
  apply LinearMap.ext
  intro l
  let gd : Module.Dual C.R₁ M.M := g.dual.toLinearMap l
  let ap : Module.Dual C.R₁ B.M := a.toLinearMap p
  let hd : Module.Dual C.R₁ M.dual.M := h.dual.toLinearMap ap
  have hrel := LinearMap.congr_fun
    (restrictRealDualTrivialization_comp_dual Γ M P e) l
  change h.toLinearMap gd = c.inv.toLinearMap l at hrel
  have hc : c.hom.toLinearMap (c.inv.toLinearMap l) = l := by
    exact LinearMap.congr_fun
      (congrArg DescentDatum.Hom.toLinearMap c.inv_hom_id) l
  change l (g.toLinearMap (q.toLinearMap p)) = l p
  calc
    l (g.toLinearMap (q.toLinearMap p)) = gd (q.toLinearMap p) := rfl
    _ = gd ((Module.evalEquiv C.R₁ M.M).symm hd) := by rfl
    _ = hd gd := Module.apply_evalEquiv_symm_apply C.R₁ M.M gd hd
    _ = ap (h.toLinearMap gd) := rfl
    _ = ap (c.inv.toLinearMap l) := congrArg ap hrel
    _ = (Module.evalEquiv C.R₁ K.M p)
        (c.hom.toLinearMap (c.inv.toLinearMap l)) := by rfl
    _ = (Module.evalEquiv C.R₁ K.M p) l := congrArg _ hc
    _ = l p := rfl

/-- Restricting a real trivialization gives a bijection on underlying modules. -/
lemma restrictRealTrivialization_bijective
    (M : NovikovDescentDatum Γ A)
    (P : FiniteProjectiveModule.{u, u} A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    Function.Bijective (restrictRealTrivialization M P e).toLinearMap := by
  refine ⟨restrictRealTrivialization_injective M P e, ?_⟩
  intro p
  refine ⟨(fromRestrictedDual Γ M P e).toLinearMap p, ?_⟩
  exact LinearMap.congr_fun
    (restrictRealTrivialization_comp_fromRestrictedDual Γ M P e) p

/-- A real trivialization descends to an isomorphism over the original exponent
monoid. -/
noncomputable def restrictRealTrivializationIso
    (M : NovikovDescentDatum Γ A)
    (P : FiniteProjectiveModule.{u, u} A)
    (e : M.baseChange (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) :
    M ≅ (vectToNovikovDescent Γ A).obj P :=
  DescentDatum.isoOfLinearEquiv (restrictRealTrivialization M P e)
    (LinearEquiv.ofBijective (restrictRealTrivialization M P e).toLinearMap
      (restrictRealTrivialization_bijective Γ M P e)) rfl

end

end Novikov.Descent
