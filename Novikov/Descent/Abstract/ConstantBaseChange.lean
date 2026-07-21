import Novikov.Descent.Abstract.BaseChange
import Novikov.Descent.Abstract.Constant
import Mathlib.CategoryTheory.Iso

/-!
# Constant descent and base change

A morphism of extended cosimplicial rings consists of compatible maps in
levels zero through three. This file proves that base-changing a constant
descent datum along such a morphism agrees with first base-changing its
underlying finite projective module and then forming constant descent.
-/

open CategoryTheory TensorProduct

namespace Novikov.Descent.Abstract

open Novikov.Miscellany

universe uE₀ uE₁ uE₂ uE₃ uD₀ uD₁ uD₂ uD₃ uP

/-- A morphism of extended cosimplicial rings. -/
structure ExtendedCosimplicialRingHom (E D : ExtendedCosimplicialRing)
    extends CosimplicialRingHom E.toCosimplicialRing D.toCosimplicialRing where
  f₀ : E.R₀ →+* D.R₀
  comm_π₀ : f₁.comp E.π₀ = D.π₀.comp f₀

namespace ExtendedCosimplicialRingHom

variable {E D H : ExtendedCosimplicialRing}

@[ext]
lemma ext {F G : ExtendedCosimplicialRingHom E D}
    (h₀ : F.f₀ = G.f₀) (h₁ : F.f₁ = G.f₁)
    (h₂ : F.f₂ = G.f₂) (h₃ : F.f₃ = G.f₃) : F = G := by
  have h : F.toCosimplicialRingHom = G.toCosimplicialRingHom :=
    CosimplicialRingHom.ext h₁ h₂ h₃
  cases F
  cases G
  cases h₀
  cases h
  rfl

@[simp]
lemma map_π₀_apply (F : ExtendedCosimplicialRingHom E D) (x : E.R₀) :
    F.f₁ (E.π₀ x) = D.π₀ (F.f₀ x) :=
  RingHom.congr_fun F.comm_π₀ x

/-- The identity morphism of an extended cosimplicial ring. -/
def id (E : ExtendedCosimplicialRing) : ExtendedCosimplicialRingHom E E where
  toCosimplicialRingHom := CosimplicialRingHom.id E.toCosimplicialRing
  f₀ := RingHom.id _
  comm_π₀ := by ext x; rfl

/-- Composition of morphisms of extended cosimplicial rings. -/
def comp (G : ExtendedCosimplicialRingHom D H)
    (F : ExtendedCosimplicialRingHom E D) : ExtendedCosimplicialRingHom E H where
  toCosimplicialRingHom := G.toCosimplicialRingHom.comp F.toCosimplicialRingHom
  f₀ := G.f₀.comp F.f₀
  comm_π₀ := by
    ext x
    change G.f₁ (F.f₁ (E.π₀ x)) = H.π₀ (G.f₀ (F.f₀ x))
    rw [F.map_π₀_apply, G.map_π₀_apply]

@[simp] lemma id_f₀ (E : ExtendedCosimplicialRing) : (id E).f₀ = RingHom.id _ := rfl
@[simp] lemma id_f₁ (E : ExtendedCosimplicialRing) : (id E).f₁ = RingHom.id _ := rfl
@[simp] lemma id_f₂ (E : ExtendedCosimplicialRing) : (id E).f₂ = RingHom.id _ := rfl
@[simp] lemma id_f₃ (E : ExtendedCosimplicialRing) : (id E).f₃ = RingHom.id _ := rfl
@[simp] lemma id_toCosimplicialRingHom (E : ExtendedCosimplicialRing) :
    (id E).toCosimplicialRingHom = CosimplicialRingHom.id E.toCosimplicialRing := rfl
@[simp] lemma comp_f₀ (G : ExtendedCosimplicialRingHom D H)
    (F : ExtendedCosimplicialRingHom E D) : (G.comp F).f₀ = G.f₀.comp F.f₀ := rfl
@[simp] lemma comp_f₁ (G : ExtendedCosimplicialRingHom D H)
    (F : ExtendedCosimplicialRingHom E D) : (G.comp F).f₁ = G.f₁.comp F.f₁ := rfl
@[simp] lemma comp_f₂ (G : ExtendedCosimplicialRingHom D H)
    (F : ExtendedCosimplicialRingHom E D) : (G.comp F).f₂ = G.f₂.comp F.f₂ := rfl
@[simp] lemma comp_f₃ (G : ExtendedCosimplicialRingHom D H)
    (F : ExtendedCosimplicialRingHom E D) : (G.comp F).f₃ = G.f₃.comp F.f₃ := rfl
@[simp] lemma comp_toCosimplicialRingHom (G : ExtendedCosimplicialRingHom D H)
    (F : ExtendedCosimplicialRingHom E D) :
    (G.comp F).toCosimplicialRingHom =
      G.toCosimplicialRingHom.comp F.toCosimplicialRingHom := rfl

end ExtendedCosimplicialRingHom

variable {E D : ExtendedCosimplicialRing}

/-- The underlying module comparison between base-changed constant descent and
constant descent of the base-changed module. -/
noncomputable def constantDescentDatumBaseChangeEquiv
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀) :
    ((constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom).M
      ≃ₗ[D.R₁] (constantDescentDatum D (P.baseChange F.f₀).M).M := by
  letI : Algebra E.R₀ D.R₁ := (D.π₀.comp F.f₀).toAlgebra
  let eL :
      ((constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom).M
        ≃ₗ[D.R₁] D.R₁ ⊗[E.R₀] P.M := by
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    letI : Algebra E.R₁ D.R₁ := F.f₁.toAlgebra
    change (D.R₁ ⊗[E.R₁] (E.R₁ ⊗[E.R₀] P.M))
      ≃ₗ[D.R₁] D.R₁ ⊗[E.R₀] P.M
    exact baseChange_assoc_eq E.π₀ F.f₁ F.comm_π₀ P.M
  let eR :
      (constantDescentDatum D (P.baseChange F.f₀).M).M
        ≃ₗ[D.R₁] D.R₁ ⊗[E.R₀] P.M := by
    letI : Algebra E.R₀ D.R₀ := F.f₀.toAlgebra
    letI : Algebra D.R₀ D.R₁ := D.π₀.toAlgebra
    change (D.R₁ ⊗[D.R₀] (D.R₀ ⊗[E.R₀] P.M))
      ≃ₗ[D.R₁] D.R₁ ⊗[E.R₀] P.M
    exact baseChange_assoc F.f₀ D.π₀ P.M
  exact eL.trans eR.symm

/-- Pure-tensor formula for `constantDescentDatumBaseChangeEquiv`. -/
@[simp]
lemma constantDescentDatumBaseChangeEquiv_tmul
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (s : D.R₁) (t : E.R₁) (p : P.M) :
    constantDescentDatumBaseChangeEquiv F P
      (letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
       letI : Algebra E.R₁ D.R₁ := F.f₁.toAlgebra
       (s ⊗ₜ[E.R₁] (t ⊗ₜ[E.R₀] p) :
         D.R₁ ⊗[E.R₁] (E.R₁ ⊗[E.R₀] P.M))) =
      (letI : Algebra E.R₀ D.R₀ := F.f₀.toAlgebra
       letI : Algebra D.R₀ D.R₁ := D.π₀.toAlgebra
       ((F.f₁ t * s) ⊗ₜ[D.R₀] ((1 : D.R₀) ⊗ₜ[E.R₀] p) :
         D.R₁ ⊗[D.R₀] (D.R₀ ⊗[E.R₀] P.M))) := by
  rw [constantDescentDatumBaseChangeEquiv]
  simp only [id_eq]
  rw [LinearEquiv.trans_apply]
  erw [baseChange_assoc_eq_tmul]
  erw [baseChange_assoc_symm_tmul]
  rfl

private noncomputable def constantBaseChangeBaseElem
    (P : FiniteProjectiveModule E.R₀) (t : E.R₁) (p : P.M) :
    (constantDescentDatum E P.M).M := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  exact t ⊗ₜ[E.R₀] p

private noncomputable def constantBaseChangeSourceElem
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (s : D.R₁) (t : E.R₁) (p : P.M) :
    ((constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom).M := by
  letI : Algebra E.R₁ D.R₁ := F.f₁.toAlgebra
  change D.R₁ ⊗[E.R₁] (constantDescentDatum E P.M).M
  exact s ⊗ₜ[E.R₁] constantBaseChangeBaseElem P t p

private noncomputable def constantBaseChangeQElem
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀) (p : P.M) :
    (P.baseChange F.f₀).M := by
  letI : Algebra E.R₀ D.R₀ := F.f₀.toAlgebra
  change D.R₀ ⊗[E.R₀] P.M
  exact (1 : D.R₀) ⊗ₜ[E.R₀] p

private noncomputable def constantBaseChangeTargetElem
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀) (s : D.R₁) (p : P.M) :
    (constantDescentDatum D (P.baseChange F.f₀).M).M := by
  letI : Algebra D.R₀ D.R₁ := D.π₀.toAlgebra
  exact s ⊗ₜ[D.R₀] constantBaseChangeQElem F P p

private noncomputable def constantBaseChangeSourceXπ₁Elem
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (t : E.R₁) (p : P.M) :
    let X := (constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom
    π₁s D.toCosimplicialRing X.M := by
  letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
  letI : Algebra E.R₁ D.R₁ := F.f₁.toAlgebra
  exact r ⊗ₜ[D.R₁]
    (s ⊗ₜ[E.R₁] constantBaseChangeBaseElem P t p)

private noncomputable def constantBaseChangeSourceXπ₂Elem
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (t : E.R₁) (p : P.M) :
    let X := (constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom
    π₂s D.toCosimplicialRing X.M := by
  letI : Algebra E.R₁ D.R₁ := F.f₁.toAlgebra
  letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
  exact r ⊗ₜ[D.R₁] constantBaseChangeSourceElem F P s t p

private lemma constantBaseChangeSource_tmul_eq_X
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀) (r : D.R₂) (p : P.M) :
    letI : Algebra E.R₁ D.R₁ := F.f₁.toAlgebra
    letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    (show π₂s D.toCosimplicialRing
        (baseChange_along F.f₁ (constantDescentDatum E P.M).M) from
      (r ⊗ₜ[D.R₁]
        ((1 : D.R₁) ⊗ₜ[E.R₁] constantBaseChangeBaseElem P 1 p) :
        D.R₂ ⊗[D.R₁]
          (D.R₁ ⊗[E.R₁] (constantDescentDatum E P.M).M))) =
      constantBaseChangeSourceXπ₂Elem F P r 1 1 p := by
  rw [constantBaseChangeSourceXπ₂Elem, constantBaseChangeSourceElem]
  rfl

private noncomputable def constantBaseChangeTargetπ₁Elem
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (p : P.M) :
    let Y := constantDescentDatum D (P.baseChange F.f₀).M
    π₁s D.toCosimplicialRing Y.M := by
  letI : Algebra D.R₀ D.R₁ := D.π₀.toAlgebra
  letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
  exact r ⊗ₜ[D.R₁] constantBaseChangeTargetElem F P s p

private noncomputable def constantBaseChangeTargetYπ₂Elem
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (p : P.M) :
    let Y := constantDescentDatum D (P.baseChange F.f₀).M
    π₂s D.toCosimplicialRing Y.M := by
  letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
  exact r ⊗ₜ[D.R₁] constantBaseChangeTargetElem F P s p

private lemma constantBaseChangeTarget_tmul_eq_target
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀) (r : D.R₂) (p : P.M) :
    let Q := P.baseChange F.f₀
    let Y := constantDescentDatum D Q.M
    letI : Algebra D.R₀ D.R₁ := D.π₀.toAlgebra
    letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    (show π₂s D.toCosimplicialRing Y.M from
      (r ⊗ₜ[D.R₁]
        ((1 : D.R₁) ⊗ₜ[D.R₀] constantBaseChangeQElem F P p) :
        D.R₂ ⊗[D.R₁] (D.R₁ ⊗[D.R₀] Q.M))) =
      constantBaseChangeTargetYπ₂Elem F P r 1 p := by
  rw [constantBaseChangeTargetYπ₂Elem, constantBaseChangeTargetElem]
  rfl

private lemma constantBaseChangeEquiv_sourceElem
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (s : D.R₁) (t : E.R₁) (p : P.M) :
    constantDescentDatumBaseChangeEquiv F P
        (constantBaseChangeSourceElem F P s t p) =
      constantBaseChangeTargetElem F P (F.f₁ t * s) p := by
  rw [constantBaseChangeSourceElem, constantBaseChangeTargetElem,
    constantBaseChangeQElem]
  simpa only [id_eq] using
    constantDescentDatumBaseChangeEquiv_tmul F P s t p

private lemma baseChange_constantBaseChangeSourceXπ₁Elem
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (t : E.R₁) (p : P.M) :
    baseChangeMap D.π₁ (constantDescentDatumBaseChangeEquiv F P).toLinearMap
        (constantBaseChangeSourceXπ₁Elem F P r s t p) =
      constantBaseChangeTargetπ₁Elem F P r (F.f₁ t * s) p := by
  rw [constantBaseChangeSourceXπ₁Elem, constantBaseChangeTargetπ₁Elem]
  erw [baseChangeMap_tmul]
  congr 1
  have he := constantBaseChangeEquiv_sourceElem F P s t p
  rw [constantBaseChangeSourceElem] at he
  exact he

private lemma baseChange_constantBaseChangeSourceXπ₂Elem
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (t : E.R₁) (p : P.M) :
    baseChangeMap D.π₂ (constantDescentDatumBaseChangeEquiv F P).toLinearMap
        (constantBaseChangeSourceXπ₂Elem F P r s t p) =
      constantBaseChangeTargetYπ₂Elem F P r (F.f₁ t * s) p := by
  rw [constantBaseChangeSourceXπ₂Elem, constantBaseChangeTargetYπ₂Elem,
    constantBaseChangeTargetElem]
  erw [baseChangeMap_tmul]
  congr 1
  have he := constantBaseChangeEquiv_sourceElem F P s t p
  rw [constantBaseChangeSourceElem] at he
  exact he

private lemma constantBaseChangeTarget_φ
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (p : P.M) :
    let Y := constantDescentDatum D (P.baseChange F.f₀).M
    Y.φ (constantBaseChangeTargetπ₁Elem F P r s p) =
      constantBaseChangeTargetYπ₂Elem F P (D.π₁ s * r) 1 p := by
  dsimp only
  have hφ := constantDescentDatum_φ_tmul D (P.baseChange F.f₀).M r s
    (constantBaseChangeQElem F P p)
  rw [constantBaseChangeTargetπ₁Elem, constantBaseChangeTargetElem]
  with_reducible
    erw [hφ]
  have hbridge := constantBaseChangeTarget_tmul_eq_target F P (D.π₁ s * r) p
  dsimp only at hbridge
  with_reducible
    exact hbridge

private lemma constantBaseChangeSource_φ
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (t : E.R₁) (p : P.M) :
    let M := constantDescentDatum E P.M
    F.toCosimplicialRingHom.baseChangePhi M
        (constantBaseChangeSourceXπ₁Elem F P r s t p) =
      constantBaseChangeSourceXπ₂Elem F P
        (F.f₂ (E.π₁ t) * (D.π₁ s * r)) 1 1 p := by
  let G := F.toCosimplicialRingHom
  let M := constantDescentDatum E P.M
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₁ D.R₁ := F.f₁.toAlgebra
  dsimp only
  rw [constantBaseChangeSourceXπ₁Elem]
  simp only [CosimplicialRingHom.baseChangePhi, LinearEquiv.trans_apply]
  have hpull := G.pullbackBaseChangeπ₁_tmul M.M r s
    (constantBaseChangeBaseElem P t p)
  dsimp only [G] at hpull
  with_reducible
    erw [hpull]
  rw [LinearEquiv.baseChange_tmul]
  rw [constantBaseChangeBaseElem]
  have hM := constantDescentDatum_φ_tmul E P.M (1 : E.R₂) t p
  with_reducible
    erw [hM]
  rw [mul_one]
  letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
  have hpb := G.pullbackBaseChangeπ₂_symm_tmul' M.M (s • r)
    (E.π₁ t) (constantBaseChangeBaseElem P 1 p)
  rw [constantBaseChangeBaseElem] at hpb
  with_reducible
    erw [hpb]
  letI : Algebra E.R₂ D.R₂ := F.f₂.toAlgebra
  simp only [Algebra.smul_def]
  have hf₂ : algebraMap E.R₂ D.R₂ = F.f₂ := rfl
  have hπ₁ : algebraMap D.R₁ D.R₂ = D.π₁ := rfl
  rw [hf₂, hπ₁]
  letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
  have hbridge := constantBaseChangeSource_tmul_eq_X F P
    (F.f₂ (E.π₁ t) * (D.π₁ s * r)) p
  dsimp only at hbridge
  rw [constantBaseChangeBaseElem] at hbridge
  exact hbridge

private lemma baseChange_constantBaseChangeSource_φ
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (t : E.R₁) (p : P.M) :
    let M := constantDescentDatum E P.M
    baseChangeMap D.π₂ (constantDescentDatumBaseChangeEquiv F P).toLinearMap
        (F.toCosimplicialRingHom.baseChangePhi M
          (constantBaseChangeSourceXπ₁Elem F P r s t p)) =
      baseChangeMap D.π₂ (constantDescentDatumBaseChangeEquiv F P).toLinearMap
        (constantBaseChangeSourceXπ₂Elem F P
          (F.f₂ (E.π₁ t) * (D.π₁ s * r)) 1 1 p) := by
  exact congrArg
    (baseChangeMap D.π₂ (constantDescentDatumBaseChangeEquiv F P).toLinearMap)
    (constantBaseChangeSource_φ F P r s t p)

private lemma constantBaseChangeSourceXπ₁Elem_formula_X
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (t : E.R₁) (p : P.M) :
    let X := (constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    letI : Algebra E.R₁ D.R₁ := F.f₁.toAlgebra
    letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
    (show π₁s D.toCosimplicialRing X.M from
      (r ⊗ₜ[D.R₁] (s ⊗ₜ[E.R₁] (t ⊗ₜ[E.R₀] p)))) =
      constantBaseChangeSourceXπ₁Elem F P r s t p := by
  rw [constantBaseChangeSourceXπ₁Elem, constantBaseChangeBaseElem]

private lemma constantBaseChange_coeff
    (F : ExtendedCosimplicialRingHom E D)
    (r : D.R₂) (s : D.R₁) (t : E.R₁) :
    D.π₁ (F.f₁ t * s) * r =
      F.f₂ (E.π₁ t) * (D.π₁ s * r) := by
  rw [map_mul, ← F.toCosimplicialRingHom.map_π₁_apply]
  ring

private lemma constantBaseChange_pure_commute
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (t : E.R₁) (p : P.M) :
    let M := constantDescentDatum E P.M
    let Y := constantDescentDatum D (P.baseChange F.f₀).M
    Y.φ (baseChangeMap D.π₁
      (constantDescentDatumBaseChangeEquiv F P).toLinearMap
      (constantBaseChangeSourceXπ₁Elem F P r s t p)) =
    baseChangeMap D.π₂
      (constantDescentDatumBaseChangeEquiv F P).toLinearMap
      (F.toCosimplicialRingHom.baseChangePhi M
        (constantBaseChangeSourceXπ₁Elem F P r s t p)) := by
  dsimp only
  rw [baseChange_constantBaseChangeSourceXπ₁Elem]
  rw [constantBaseChangeTarget_φ]
  rw [baseChange_constantBaseChangeSource_φ F P r s t p]
  rw [baseChange_constantBaseChangeSourceXπ₂Elem]
  rw [map_one, one_mul]
  congr 1
  exact constantBaseChange_coeff F r s t

private lemma constantBaseChange_pure_commute_X
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (t : E.R₁) (p : P.M) :
    let X := (constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom
    let Y := constantDescentDatum D (P.baseChange F.f₀).M
    Y.φ (baseChangeMap D.π₁
      (constantDescentDatumBaseChangeEquiv F P).toLinearMap
      (constantBaseChangeSourceXπ₁Elem F P r s t p)) =
    baseChangeMap D.π₂
      (constantDescentDatumBaseChangeEquiv F P).toLinearMap
      (X.φ (constantBaseChangeSourceXπ₁Elem F P r s t p)) := by
  let G := F.toCosimplicialRingHom
  let M := constantDescentDatum E P.M
  let X := M.baseChange G
  dsimp only
  have hXφ : X.φ = G.baseChangePhi M := rfl
  rw [hXφ]
  exact constantBaseChange_pure_commute F P r s t p

private lemma constantBaseChange_pure_commute_raw
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀)
    (r : D.R₂) (s : D.R₁) (t : E.R₁) (p : P.M) :
    let X := (constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom
    let Y := constantDescentDatum D (P.baseChange F.f₀).M
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    letI : Algebra E.R₁ D.R₁ := F.f₁.toAlgebra
    letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
    let x : π₁s D.toCosimplicialRing X.M :=
      r ⊗ₜ[D.R₁] (s ⊗ₜ[E.R₁] (t ⊗ₜ[E.R₀] p))
    (show π₂s D.toCosimplicialRing Y.M from
      Y.φ (baseChangeMap D.π₁
        (constantDescentDatumBaseChangeEquiv F P).toLinearMap x)) =
    baseChangeMap D.π₂
      (constantDescentDatumBaseChangeEquiv F P).toLinearMap (X.φ x) := by
  let X := (constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom
  let Y := constantDescentDatum D (P.baseChange F.f₀).M
  dsimp only
  have hx := constantBaseChangeSourceXπ₁Elem_formula_X F P r s t p
  dsimp only at hx
  have hl := congrArg
    (fun x : π₁s D.toCosimplicialRing X.M =>
      Y.φ (baseChangeMap D.π₁
        (constantDescentDatumBaseChangeEquiv F P).toLinearMap x)) hx
  have hr := congrArg
    (fun x : π₁s D.toCosimplicialRing X.M =>
      baseChangeMap D.π₂
        (constantDescentDatumBaseChangeEquiv F P).toLinearMap (X.φ x)) hx
  have hp := constantBaseChange_pure_commute_X F P r s t p
  dsimp only at hp
  exact hl.trans (hp.trans hr.symm)

attribute [local irreducible]
  constantDescentDatumBaseChangeEquiv
  constantBaseChangeBaseElem
  constantBaseChangeSourceElem
  constantBaseChangeQElem
  constantBaseChangeTargetElem
  constantBaseChangeSourceXπ₁Elem
  constantBaseChangeSourceXπ₂Elem
  constantBaseChangeTargetπ₁Elem
  constantBaseChangeTargetYπ₂Elem
  constantDescentDatum

attribute [local semireducible] constantDescentDatum

private lemma addMonoidHom_ext_tmul
    {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] (f g : M ⊗[R] N →+ P)
    (h : ∀ m n, f (m ⊗ₜ[R] n) = g (m ⊗ₜ[R] n)) : f = g := by
  apply AddMonoidHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact f.map_zero.trans g.map_zero.symm
  | add x y hx hy =>
      calc
        f (x + y) = f x + f y := f.map_add x y
        _ = g x + g y := congrArg₂ HAdd.hAdd hx hy
        _ = g (x + y) := (g.map_add x y).symm
  | tmul m n => exact h m n

private def addMonoidHomCompTmul
    {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] (f : M ⊗[R] N →+ P) (m : M) : N →+ P where
  toFun n := f (m ⊗ₜ[R] n)
  map_zero' := by rw [TensorProduct.tmul_zero, f.map_zero]
  map_add' x y := by rw [TensorProduct.tmul_add, f.map_add]

@[simp]
private lemma addMonoidHomCompTmul_apply
    {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] (f : M ⊗[R] N →+ P) (m : M) (n : N) :
    addMonoidHomCompTmul f m n = f (m ⊗ₜ[R] n) := rfl

@[simp]
private lemma linearMap_toAddMonoidHom_apply
    {R S M N : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
    {σ : R →+* S} (f : M →ₛₗ[σ] N) (x : M) :
    f.toAddMonoidHom x = f x := rfl

private lemma linearEquiv_toLinearMap_apply_heq
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (x : M) : HEq (e.toLinearMap x) (e x) := by
  rfl

private lemma linearMap_eq_of_toAddMonoidHom_eq
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f g : M →ₗ[R] N)
    (h : f.toAddMonoidHom = g.toAddMonoidHom) : f = g :=
  LinearMap.toAddMonoidHom_injective h

private lemma constantDescentDatumBaseChangeEquiv_commute
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀) :
    let X := (constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom
    let Y := constantDescentDatum D (P.baseChange F.f₀).M
    Y.φ.toLinearMap ∘ₗ
        baseChangeMap D.π₁ (constantDescentDatumBaseChangeEquiv F P).toLinearMap =
      baseChangeMap D.π₂
          (constantDescentDatumBaseChangeEquiv F P).toLinearMap ∘ₗ
        X.φ.toLinearMap := by
  dsimp only
  let G := F.toCosimplicialRingHom
  let M := constantDescentDatum E P.M
  letI mAdd : AddCommGroup M.M := M.instAddCommGroup
  letI mModule : Module E.R₁ M.M := M.instModule
  let X := M.baseChange G
  let Q := P.baseChange F.f₀
  let Y := constantDescentDatum D Q.M
  letI xAdd : AddCommGroup X.M := X.instAddCommGroup
  letI xModule : Module D.R₁ X.M := X.instModule
  letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
  letI sourceAdd : AddCommGroup (π₁s D.toCosimplicialRing X.M) := inferInstance
  letI sourceModule : Module D.R₂ (π₁s D.toCosimplicialRing X.M) := inferInstance
  letI yπ₁Add : AddCommGroup (π₁s D.toCosimplicialRing Y.M) := inferInstance
  letI yπ₁Module : Module D.R₂ (π₁s D.toCosimplicialRing Y.M) := inferInstance
  letI xπ₂Add : AddCommGroup (π₂s D.toCosimplicialRing X.M) := by
    letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    infer_instance
  letI xπ₂Module : Module D.R₂ (π₂s D.toCosimplicialRing X.M) := by
    letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    infer_instance
  letI targetAdd : AddCommGroup (π₂s D.toCosimplicialRing Y.M) := by
    letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    infer_instance
  letI targetModule : Module D.R₂ (π₂s D.toCosimplicialRing Y.M) := by
    letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    infer_instance
  let L : π₁s D.toCosimplicialRing X.M →ₗ[D.R₂]
      π₂s D.toCosimplicialRing Y.M :=
    Y.φ.toLinearMap ∘ₗ
      baseChangeMap D.π₁ (constantDescentDatumBaseChangeEquiv F P).toLinearMap
  let R : π₁s D.toCosimplicialRing X.M →ₗ[D.R₂]
      π₂s D.toCosimplicialRing Y.M :=
    baseChangeMap D.π₂
      (constantDescentDatumBaseChangeEquiv F P).toLinearMap ∘ₗ X.φ.toLinearMap
  change L = R
  have houter : L.toAddMonoidHom = R.toAddMonoidHom := by
    with_reducible
      apply addMonoidHom_ext_tmul (R := D.R₁) (M := D.R₂) (N := X.M)
    intro r y
    let L₁ := addMonoidHomCompTmul L.toAddMonoidHom r
    let R₁ := addMonoidHomCompTmul R.toAddMonoidHom r
    have hmiddle : L₁ = R₁ := by
      letI : Algebra E.R₁ D.R₁ := F.f₁.toAlgebra
      apply addMonoidHom_ext_tmul (R := E.R₁) (M := D.R₁) (N := M.M)
      intro s z
      let L₂ := addMonoidHomCompTmul L₁ s
      let R₂ := addMonoidHomCompTmul R₁ s
      have hinner : L₂ = R₂ := by
        letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
        apply addMonoidHom_ext_tmul (R := E.R₀) (M := E.R₁) (N := P.M)
        intro t p
        calc
          L₂ (t ⊗ₜ[E.R₀] p) =
              L₁ (s ⊗ₜ[E.R₁] (t ⊗ₜ[E.R₀] p)) :=
            addMonoidHomCompTmul_apply L₁ s (t ⊗ₜ[E.R₀] p)
          _ = L.toAddMonoidHom
              (r ⊗ₜ[D.R₁] (s ⊗ₜ[E.R₁] (t ⊗ₜ[E.R₀] p))) :=
            addMonoidHomCompTmul_apply L.toAddMonoidHom r
              (s ⊗ₜ[E.R₁] (t ⊗ₜ[E.R₀] p))
          _ = R.toAddMonoidHom
              (r ⊗ₜ[D.R₁] (s ⊗ₜ[E.R₁] (t ⊗ₜ[E.R₀] p))) := by
            rw [linearMap_toAddMonoidHom_apply, linearMap_toAddMonoidHom_apply]
            dsimp only [L, R]
            rw [LinearMap.comp_apply, LinearMap.comp_apply]
            dsimp only [X, Y, Q, M, G]
            rw [LinearEquiv.coe_toLinearMap]
            have hpure := constantBaseChange_pure_commute_raw F P r s t p
            dsimp only at hpure
            have hcoe := linearEquiv_toLinearMap_apply_heq
              (constantDescentDatum D (P.baseChange F.f₀).M).φ
              (baseChangeMap D.π₁
                (constantDescentDatumBaseChangeEquiv F P).toLinearMap
                (r ⊗ₜ[D.R₁] (s ⊗ₜ[E.R₁] (t ⊗ₜ[E.R₀] p))))
            have hall := HEq.trans hcoe (heq_of_eq hpure)
            exact eq_of_heq hall
          _ = R₁ (s ⊗ₜ[E.R₁] (t ⊗ₜ[E.R₀] p)) :=
            (addMonoidHomCompTmul_apply R.toAddMonoidHom r
              (s ⊗ₜ[E.R₁] (t ⊗ₜ[E.R₀] p))).symm
          _ = R₂ (t ⊗ₜ[E.R₀] p) :=
            (addMonoidHomCompTmul_apply R₁ s (t ⊗ₜ[E.R₀] p)).symm
      calc
        L₁ (s ⊗ₜ[E.R₁] z) = L₂ z :=
          (addMonoidHomCompTmul_apply L₁ s z).symm
        _ = R₂ z := DFunLike.congr_fun hinner z
        _ = R₁ (s ⊗ₜ[E.R₁] z) := addMonoidHomCompTmul_apply R₁ s z
    calc
      L.toAddMonoidHom (r ⊗ₜ[D.R₁] y) = L₁ y :=
        (addMonoidHomCompTmul_apply L.toAddMonoidHom r y).symm
      _ = R₁ y := DFunLike.congr_fun hmiddle y
      _ = R.toAddMonoidHom (r ⊗ₜ[D.R₁] y) :=
        addMonoidHomCompTmul_apply R.toAddMonoidHom r y
  with_reducible
    exact linearMap_eq_of_toAddMonoidHom_eq L R houter

private lemma linearMap_comp_symm_of_comp
    {R : Type*} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type*}
    [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    [AddCommMonoid N₁] [Module R N₁] [AddCommMonoid N₂] [Module R N₂]
    {Φ : M₂ →ₗ[R] N₂} {Ψ : M₁ →ₗ[R] N₁}
    {B : M₁ ≃ₗ[R] M₂} {C : N₁ ≃ₗ[R] N₂}
    (h : Φ ∘ₗ B.toLinearMap = C.toLinearMap ∘ₗ Ψ) :
    Ψ ∘ₗ B.symm.toLinearMap = C.symm.toLinearMap ∘ₗ Φ := by
  ext x
  have hx := LinearMap.congr_fun h (B.symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, B.apply_symm_apply] at hx
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hx, C.symm_apply_apply]

private lemma constantDescentDatumBaseChangeEquiv_commute_symm
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule E.R₀) :
    let X := (constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom
    let Y := constantDescentDatum D (P.baseChange F.f₀).M
    X.φ.toLinearMap ∘ₗ
        baseChangeMap D.π₁ (constantDescentDatumBaseChangeEquiv F P).symm.toLinearMap =
      baseChangeMap D.π₂
          (constantDescentDatumBaseChangeEquiv F P).symm.toLinearMap ∘ₗ
        Y.φ.toLinearMap := by
  dsimp only
  let e := constantDescentDatumBaseChangeEquiv F P
  let X := (constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom
  let Y := constantDescentDatum D (P.baseChange F.f₀).M
  let e₁ : π₁s D.toCosimplicialRing X.M ≃ₗ[D.R₂]
      π₁s D.toCosimplicialRing Y.M := by
    letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
    exact LinearEquiv.baseChange D.R₁ D.R₂ X.M Y.M e
  let e₂ : π₂s D.toCosimplicialRing X.M ≃ₗ[D.R₂]
      π₂s D.toCosimplicialRing Y.M := by
    letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    exact LinearEquiv.baseChange D.R₁ D.R₂ X.M Y.M e
  have he₁ : baseChangeMap D.π₁ e.symm.toLinearMap = e₁.symm.toLinearMap := by
    letI : Algebra D.R₁ D.R₂ := D.π₁.toAlgebra
    exact congrArg LinearEquiv.toLinearMap
      (LinearEquiv.baseChange_symm D.R₁ D.R₂ X.M Y.M e)
  have he₂ : baseChangeMap D.π₂ e.symm.toLinearMap = e₂.symm.toLinearMap := by
    letI : Algebra D.R₁ D.R₂ := D.π₂.toAlgebra
    exact congrArg LinearEquiv.toLinearMap
      (LinearEquiv.baseChange_symm D.R₁ D.R₂ X.M Y.M e)
  rw [he₁, he₂]
  apply linearMap_comp_symm_of_comp
  have he₁' : baseChangeMap D.π₁ e.toLinearMap = e₁.toLinearMap := by rfl
  have he₂' : baseChangeMap D.π₂ e.toLinearMap = e₂.toLinearMap := by rfl
  rw [← he₁', ← he₂']
  exact constantDescentDatumBaseChangeEquiv_commute F P

/-- Constant descent data commute with base change along a morphism of extended
cosimplicial rings. -/
noncomputable def constantDescentDatum_baseChangeIso
    {E : ExtendedCosimplicialRing.{uE₀, uE₃, uE₂, uE₁}}
    {D : ExtendedCosimplicialRing.{uD₀, uD₃, uD₂, uD₁}}
    (F : ExtendedCosimplicialRingHom E D)
    (P : FiniteProjectiveModule.{uE₀, max uE₁ uD₀ uD₁ uP} E.R₀) :
    (constantDescentDatum E P.M).baseChange F.toCosimplicialRingHom ≅
      constantDescentDatum D (P.baseChange F.f₀).M where
  hom :=
    { toLinearMap := (constantDescentDatumBaseChangeEquiv F P).toLinearMap
      commute_φ := constantDescentDatumBaseChangeEquiv_commute F P }
  inv :=
    { toLinearMap := (constantDescentDatumBaseChangeEquiv F P).symm.toLinearMap
      commute_φ := constantDescentDatumBaseChangeEquiv_commute_symm F P }
  hom_inv_id := by
    apply DescentDatum.hom_ext
    change (constantDescentDatumBaseChangeEquiv F P).symm.toLinearMap.comp
        (constantDescentDatumBaseChangeEquiv F P).toLinearMap = LinearMap.id
    ext x
    exact (constantDescentDatumBaseChangeEquiv F P).symm_apply_apply x
  inv_hom_id := by
    apply DescentDatum.hom_ext
    change (constantDescentDatumBaseChangeEquiv F P).toLinearMap.comp
        (constantDescentDatumBaseChangeEquiv F P).symm.toLinearMap = LinearMap.id
    ext x
    exact (constantDescentDatumBaseChangeEquiv F P).apply_symm_apply x

end Novikov.Descent.Abstract
