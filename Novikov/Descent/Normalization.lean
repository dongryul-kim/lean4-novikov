import Novikov.Descent.Abstract.Transport
import Novikov.Descent.Isocrystal
import Novikov.Miscellany.BaseChange

/-!
# Normalized descent endomorphisms

This file identifies pullbacks of a constant real Novikov module with common
tensor presentations. It packages a descent isomorphism as a normalized
endomorphism and transports its cocycle identity through the level-three
comparisons.
-/

namespace Novikov.Descent

open Novikov Novikov.Miscellany TensorProduct
open Abstract

private noncomputable def constantCancelHom
    {A ι κ : Type*} [CommRing A] [Fintype ι] [Fintype κ]
    (f : NovikovSeries (⊤ : AddSubgroup ℝ) ι A →+*
      NovikovSeries (⊤ : AddSubgroup ℝ) κ A)
    (hf : f.comp algebraMapNovikov = algebraMapNovikov)
    (P : FiniteProjectiveModule A) :
    let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι A
    let S := NovikovSeries (⊤ : AddSubgroup ℝ) κ A
    letI : Algebra A R := algebraMapNovikov.toAlgebra
    letI : Algebra R S := f.toAlgebra
    (S ⊗[R] baseChange_along
      (algebraMapNovikov : A →+* R) P.M) ≃ₗ[S] S ⊗[A] P.M := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι A
  let S := NovikovSeries (⊤ : AddSubgroup ℝ) κ A
  let aR : Algebra A R := algebraMapNovikov.toAlgebra
  let aS : Algebra A S := inferInstance
  letI : Algebra A R := aR
  letI : SMul A R := aR.toSMul
  letI : Module A R := aR.toModule
  letI : Algebra A S := aS
  letI : SMul A S := aS.toSMul
  letI : Module A S := aS.toModule
  let rSAlg : Algebra R S := f.toAlgebra
  letI : Algebra R S := rSAlg
  letI : SMul R S := rSAlg.toSMul
  letI : Module R S := rSAlg.toModule
  letI : IsScalarTower A R S :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (RingHom.congr_fun hf a).symm)
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S P.M

/-- Identify the first pullback of a constant real Novikov module with its
canonical level-two tensor presentation. -/
noncomputable def realConstantPullbackπ₁Equiv
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A) :
    let R₁ := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
    let R₂ := NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A
    letI : Algebra A R₁ := algebraMapNovikov.toAlgebra
    letI : Algebra R₁ R₂ :=
      (substituteRingHom (fun _ : Unit => (0 : Fin 2))).toAlgebra
    (R₂ ⊗[R₁] baseChange_along
      (algebraMapNovikov : A →+* R₁) P.M) ≃ₗ[R₂] R₂ ⊗[A] P.M := by
  let f := substituteRingHom (Γ := (⊤ : AddSubgroup ℝ))
    (A := A) (fun _ : Unit => (0 : Fin 2))
  have hf : f.comp algebraMapNovikov = algebraMapNovikov := by
    apply RingHom.ext
    intro a
    exact substitute_algebraMap (Γ := (⊤ : AddSubgroup ℝ)) _ a
  exact constantCancelHom f hf P

/-- Identify the second pullback of a constant real Novikov module with its
canonical level-two tensor presentation. -/
noncomputable def realConstantPullbackπ₂Equiv
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A) :
    let R₁ := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
    let R₂ := NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A
    letI : Algebra A R₁ := algebraMapNovikov.toAlgebra
    letI : Algebra R₁ R₂ :=
      (substituteRingHom (fun _ : Unit => (1 : Fin 2))).toAlgebra
    (R₂ ⊗[R₁] baseChange_along
      (algebraMapNovikov : A →+* R₁) P.M) ≃ₗ[R₂] R₂ ⊗[A] P.M := by
  let f := substituteRingHom (Γ := (⊤ : AddSubgroup ℝ))
    (A := A) (fun _ : Unit => (1 : Fin 2))
  have hf : f.comp algebraMapNovikov = algebraMapNovikov := by
    apply RingHom.ext
    intro a
    exact substitute_algebraMap (Γ := (⊤ : AddSubgroup ℝ)) _ a
  exact constantCancelHom f hf P

/-- Normalize a descent isomorphism on the constant underlying module as an
endomorphism of the canonical level-two tensor presentation. -/
noncomputable def normalizedPhi
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (φ : π₁s (realC A)
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M ≃ₗ[(realC A).R₂]
      π₂s (realC A)
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M) :
    Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A ⊗[A] P.M) :=
  (realConstantPullbackπ₂Equiv P).toLinearMap ∘ₗ
    φ.toLinearMap ∘ₗ (realConstantPullbackπ₁Equiv P).symm.toLinearMap

/-- Base change an endomorphism and conjugate by the canonical cancellation
isomorphism to retain the normalized tensor presentation. -/
noncomputable def normalizedEndBaseChange
    {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S]
    (f : R →ₐ[A] S) (P : FiniteProjectiveModule A) :
    Module.End R (R ⊗[A] P.M) →+* Module.End S (S ⊗[A] P.M) := by
  letI : Algebra R S := f.toRingHom.toAlgebra
  letI : IsScalarTower A R S :=
    IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  let e : S ⊗[R] (R ⊗[A] P.M) ≃ₗ[S] S ⊗[A] P.M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S P.M
  exact e.conjRingEquiv.toRingHom.comp
    (Module.End.baseChangeHom R S (R ⊗[A] P.M)).toRingHom

/-- Normalized endomorphism pullback along the first level-one face map. -/
noncomputable def π₁End {C : Type*} [CommRing C]
    (P : FiniteProjectiveModule C) :
    Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit C ⊗[C] P.M) →+*
      Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C ⊗[C] P.M) :=
  normalizedEndBaseChange
    (substituteAlgHom (fun _ : Unit => (0 : Fin 2))) P

/-- Normalized endomorphism pullback along the second level-one face map. -/
noncomputable def π₂End {C : Type*} [CommRing C]
    (P : FiniteProjectiveModule C) :
    Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit C ⊗[C] P.M) →+*
      Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C ⊗[C] P.M) :=
  normalizedEndBaseChange
    (substituteAlgHom (fun _ : Unit => (1 : Fin 2))) P

/-- Normalized endomorphism pullback along the `12` level-two face map. -/
noncomputable def π₁₂End {C : Type*} [CommRing C]
    (P : FiniteProjectiveModule C) :
    Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C ⊗[C] P.M) →+*
      Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) C ⊗[C] P.M) :=
  normalizedEndBaseChange (substituteAlgHom Fin.castSucc) P

/-- Normalized endomorphism pullback along the `13` level-two face map. -/
noncomputable def π₁₃End {C : Type*} [CommRing C]
    (P : FiniteProjectiveModule C) :
    Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C ⊗[C] P.M) →+*
      Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) C ⊗[C] P.M) :=
  normalizedEndBaseChange (substituteAlgHom (Fin.succAbove 1)) P

/-- Normalized endomorphism pullback along the `23` level-two face map. -/
noncomputable def π₂₃End {C : Type*} [CommRing C]
    (P : FiniteProjectiveModule C) :
    Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C ⊗[C] P.M) →+*
      Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) C ⊗[C] P.M) :=
  normalizedEndBaseChange (substituteAlgHom Fin.succ) P

private noncomputable def normalizedCancelHom
    {A ι κ : Type*} [CommRing A] [Fintype ι] [Fintype κ]
    (f : NovikovSeries (⊤ : AddSubgroup ℝ) ι A →+*
      NovikovSeries (⊤ : AddSubgroup ℝ) κ A)
    (hf : f.comp algebraMapNovikov = algebraMapNovikov)
    (P : FiniteProjectiveModule A) :
    let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι A
    let S := NovikovSeries (⊤ : AddSubgroup ℝ) κ A
    letI : Algebra R S := f.toAlgebra
    (S ⊗[R] (R ⊗[A] P.M)) ≃ₗ[S] S ⊗[A] P.M := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι A
  let S := NovikovSeries (⊤ : AddSubgroup ℝ) κ A
  letI : Algebra R S := f.toAlgebra
  letI : IsScalarTower A R S :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (RingHom.congr_fun hf a).symm)
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S P.M

/-- Identify the underlying module of constant real Novikov descent with its
canonical coefficient-normalized tensor presentation. -/
noncomputable def realConstantModuleEquiv
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A) :
    let R := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
    let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
    let Y := R ⊗[A] P.M
    let yAdd : AddCommGroup Y := inferInstance
    let yMod : Module R Y := inferInstance
    letI : AddCommGroup K.M := K.instAddCommGroup
    letI : Module R K.M := K.instModule
    letI : AddCommGroup Y := yAdd
    letI : Module R Y := yMod
    K.M ≃ₗ[R] Y := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
  let f : R →+* R := RingHom.id R
  have hf : f.comp (algebraMapNovikov : A →+* R) = algebraMapNovikov := by
    rfl
  let c := constantCancelHom f hf P
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  let X := K.M
  let xAdd : AddCommGroup X := K.instAddCommGroup
  let xMod : Module R X := K.instModule
  letI : AddCommGroup X := xAdd
  letI : Module R X := xMod
  let l : (letI : Algebra R R := f.toAlgebra; R ⊗[R] X) ≃ₗ[R] X :=
    TensorProduct.lid R X
  exact l.symm.trans c

private noncomputable def realConstantElem
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (r : NovikovSeries (⊤ : AddSubgroup ℝ) Unit A) (p : P.M) :
    ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A
  letI : Module E.R₀ P.M := P.instModule
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  exact (show E.R₁ from r) ⊗ₜ[E.R₀] p

private theorem realConstantModuleEquiv_tmul
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (r : NovikovSeries (⊤ : AddSubgroup ℝ) Unit A) (p : P.M) :
    realConstantModuleEquiv P (realConstantElem P r p) =
      r ⊗ₜ[A] p := by
  simp only [Lean.Elab.WF.paramLet]
  change (r * 1) ⊗ₜ[A] p = r ⊗ₜ[A] p
  rw [mul_one]

private theorem constantCancelHom_tetrahedron
    {A ι κ ν : Type*} [CommRing A]
    [Fintype ι] [Fintype κ] [Fintype ν]
    (f : NovikovSeries (⊤ : AddSubgroup ℝ) ι A →+*
      NovikovSeries (⊤ : AddSubgroup ℝ) κ A)
    (g : NovikovSeries (⊤ : AddSubgroup ℝ) κ A →+*
      NovikovSeries (⊤ : AddSubgroup ℝ) ν A)
    (fg : NovikovSeries (⊤ : AddSubgroup ℝ) ι A →+*
      NovikovSeries (⊤ : AddSubgroup ℝ) ν A)
    (hcomp : g.comp f = fg)
    (hf : f.comp algebraMapNovikov = algebraMapNovikov)
    (hg : g.comp algebraMapNovikov = algebraMapNovikov)
    (hfg : fg.comp algebraMapNovikov = algebraMapNovikov)
    (P : FiniteProjectiveModule A) :
    let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι A
    letI : Algebra A R := algebraMapNovikov.toAlgebra
    let X := baseChange_along (algebraMapNovikov : A →+* R) P.M
    let xMod : Module R X := inferInstance
    letI : Module R X := xMod
    let a := constantCancelHom f hf P
    let b := constantCancelHom fg hfg P
    let c := normalizedCancelHom g hg P
    let d := baseChange_assoc_eq f g hcomp X
    c.toLinearMap ∘ₗ baseChangeMap g a.toLinearMap ∘ₗ d.symm.toLinearMap =
      b.toLinearMap := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι A
  let S := NovikovSeries (⊤ : AddSubgroup ℝ) κ A
  let T := NovikovSeries (⊤ : AddSubgroup ℝ) ν A
  let aRAlg : Algebra A R := algebraMapNovikov.toAlgebra
  letI : Algebra A R := aRAlg
  letI : SMul A R := aRAlg.toSMul
  letI : Module A R := aRAlg.toModule
  let rSAlg : Algebra R S := f.toAlgebra
  letI : Algebra R S := rSAlg
  letI : SMul R S := rSAlg.toSMul
  letI : Module R S := rSAlg.toModule
  let sTAlg : Algebra S T := g.toAlgebra
  letI : Algebra S T := sTAlg
  letI : SMul S T := sTAlg.toSMul
  letI : Module S T := sTAlg.toModule
  let rTAlg : Algebra R T := fg.toAlgebra
  letI : Algebra R T := rTAlg
  letI : SMul R T := rTAlg.toSMul
  letI : Module R T := rTAlg.toModule
  let X := baseChange_along (algebraMapNovikov : A →+* R) P.M
  let xMod : Module R X := inferInstance
  letI : Module R X := xMod
  let a := constantCancelHom f hf P
  let b := constantCancelHom fg hfg P
  let c := normalizedCancelHom g hg P
  let d := baseChange_assoc_eq f g hcomp X
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
          simp only [TensorProduct.tmul_add, map_add, hy, hz]
      | tmul s p =>
          simp only [LinearMap.comp_apply]
          let z : X := s ⊗ₜ[A] p
          change c (baseChangeMap g a.toLinearMap
            (d.symm (r ⊗ₜ[R] z))) = b (r ⊗ₜ[R] z)
          have hd : d.symm (r ⊗ₜ[R] z) =
              r ⊗ₜ[S] ((1 : S) ⊗ₜ[R] z) := by
            exact baseChange_assoc_eq_symm_tmul f g hcomp X r z
          rw [hd]
          rw [show baseChangeMap g a.toLinearMap
            (r ⊗ₜ[S] ((1 : S) ⊗ₜ[R] z)) =
              r ⊗ₜ[S] a ((1 : S) ⊗ₜ[R] z) by
                exact LinearMap.baseChange_tmul a.toLinearMap r
                  ((1 : S) ⊗ₜ[R] z)]
          dsimp only [a, b, c]
          dsimp only [z]
          rw [constantCancelHom,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
          rw [normalizedCancelHom,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
          rw [constantCancelHom,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
          congr 1
          change g (f s * 1) * r = fg s * r
          rw [mul_one]
          exact congrArg (fun z : T => z * r) (RingHom.congr_fun hcomp s)

private theorem normalized_pullback
    {A ι κ ν : Type*} [CommRing A]
    [Fintype ι] [Fintype κ] [Fintype ν]
    (f₁ f₂ : NovikovSeries (⊤ : AddSubgroup ℝ) ι A →+*
      NovikovSeries (⊤ : AddSubgroup ℝ) κ A)
    (g : NovikovSeries (⊤ : AddSubgroup ℝ) κ A →+*
      NovikovSeries (⊤ : AddSubgroup ℝ) ν A)
    (gf₁ gf₂ : NovikovSeries (⊤ : AddSubgroup ℝ) ι A →+*
      NovikovSeries (⊤ : AddSubgroup ℝ) ν A)
    (hcomp₁ : g.comp f₁ = gf₁) (hcomp₂ : g.comp f₂ = gf₂)
    (hf₁ : f₁.comp algebraMapNovikov = algebraMapNovikov)
    (hf₂ : f₂.comp algebraMapNovikov = algebraMapNovikov)
    (hg : g.comp algebraMapNovikov = algebraMapNovikov)
    (hgf₁ : gf₁.comp algebraMapNovikov = algebraMapNovikov)
    (hgf₂ : gf₂.comp algebraMapNovikov = algebraMapNovikov)
    (P : FiniteProjectiveModule A)
    (φ : let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι A
      letI : Algebra A R := algebraMapNovikov.toAlgebra
      let X := baseChange_along (algebraMapNovikov : A →+* R) P.M
      baseChange_along f₁ X ≃ₗ[NovikovSeries (⊤ : AddSubgroup ℝ) κ A]
        baseChange_along f₂ X) :
    let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι A
    letI : Algebra A R := algebraMapNovikov.toAlgebra
    let X := baseChange_along (algebraMapNovikov : A →+* R) P.M
    let a₁ := constantCancelHom f₁ hf₁ P
    let a₂ := constantCancelHom f₂ hf₂ P
    let b₁ := constantCancelHom gf₁ hgf₁ P
    let b₂ := constantCancelHom gf₂ hgf₂ P
    let c := normalizedCancelHom g hg P
    let ψ := a₂.toLinearMap ∘ₗ φ.toLinearMap ∘ₗ a₁.symm.toLinearMap
    c.toLinearMap ∘ₗ baseChangeMap g ψ ∘ₗ c.symm.toLinearMap =
      b₂.toLinearMap ∘ₗ
        (pullbackMap f₁ f₂ g hcomp₁ hcomp₂ X X φ).toLinearMap ∘ₗ
          b₁.symm.toLinearMap := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι A
  let S := NovikovSeries (⊤ : AddSubgroup ℝ) κ A
  let T := NovikovSeries (⊤ : AddSubgroup ℝ) ν A
  let aRAlg : Algebra A R := algebraMapNovikov.toAlgebra
  letI : Algebra A R := aRAlg
  letI : SMul A R := aRAlg.toSMul
  letI : Module A R := aRAlg.toModule
  let gAlg : Algebra S T := g.toAlgebra
  letI : Algebra S T := gAlg
  letI : SMul S T := gAlg.toSMul
  letI : Module S T := gAlg.toModule
  let X := baseChange_along (algebraMapNovikov : A →+* R) P.M
  let xMod : Module R X := inferInstance
  letI : Module R X := xMod
  let a₁ := constantCancelHom f₁ hf₁ P
  let a₂ := constantCancelHom f₂ hf₂ P
  let b₁ := constantCancelHom gf₁ hgf₁ P
  let b₂ := constantCancelHom gf₂ hgf₂ P
  let c := normalizedCancelHom g hg P
  let d₁ := baseChange_assoc_eq f₁ g hcomp₁ X
  let d₂ := baseChange_assoc_eq f₂ g hcomp₂ X
  let a₁D := LinearEquiv.baseChange S T _ _ a₁
  let a₂D := LinearEquiv.baseChange S T _ _ a₂
  let φD := LinearEquiv.baseChange S T _ _ φ
  have ht₁ := constantCancelHom_tetrahedron f₁ g gf₁ hcomp₁ hf₁ hg hgf₁ P
  have ht₂ := constantCancelHom_tetrahedron f₂ g gf₂ hcomp₂ hf₂ hg hgf₂ P
  have hpb : pullbackMap f₁ f₂ g hcomp₁ hcomp₂ X X φ =
      d₁.symm.trans (φD.trans d₂) := by
    subst gf₁
    subst gf₂
    rfl
  simp only [baseChangeMap]
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [hpb]
  have hE₁ : d₁.symm.trans (a₁D.trans c) = b₁ := by
    apply LinearEquiv.ext
    intro y
    exact LinearMap.congr_fun ht₁ y
  have hE₁s := congrArg LinearEquiv.symm hE₁
  have hinv := DFunLike.congr_fun hE₁s x
  have htail : a₁D.symm (c.symm x) = d₁.symm (b₁.symm x) := by
    apply d₁.injective
    rw [d₁.apply_symm_apply]
    exact hinv
  change c (a₂D (φD (a₁D.symm (c.symm x)))) =
    b₂ (d₂ (φD (d₁.symm (b₁.symm x))))
  rw [htail]
  have hhead := LinearMap.congr_fun ht₂
    (d₂ (φD (d₁.symm (b₁.symm x))))
  simp only [LinearMap.comp_apply] at hhead
  change c (a₂D (d₂.symm (d₂ (φD (d₁.symm (b₁.symm x)))))) =
    b₂ (d₂ (φD (d₁.symm (b₁.symm x)))) at hhead
  rw [d₂.symm_apply_apply] at hhead
  exact hhead

private lemma substituteRingHom_preserves_constants
    {A ι κ : Type*} [CommRing A] [Fintype ι] [Fintype κ]
    (f : ι → κ) :
    (substituteRingHom (Γ := (⊤ : AddSubgroup ℝ)) (A := A) f).comp
        algebraMapNovikov = algebraMapNovikov := by
  apply RingHom.ext
  intro a
  exact substitute_algebraMap (Γ := (⊤ : AddSubgroup ℝ)) f a

private lemma realC_π₁_preserves_constants
    {A : Type*} [CommRing A] :
    (realC A).π₁.comp algebraMapNovikov = algebraMapNovikov := by
  change (substituteRingHom (fun _ : Unit => (0 : Fin 2))).comp
    algebraMapNovikov = algebraMapNovikov
  exact substituteRingHom_preserves_constants _

private lemma realC_π₂_preserves_constants
    {A : Type*} [CommRing A] :
    (realC A).π₂.comp algebraMapNovikov = algebraMapNovikov := by
  change (substituteRingHom (fun _ : Unit => (1 : Fin 2))).comp
    algebraMapNovikov = algebraMapNovikov
  exact substituteRingHom_preserves_constants _

private theorem realConstantModuleEquiv_pullbackπ₁
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A) :
    let R := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
    let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
    let Y := R ⊗[A] P.M
    let yAdd : AddCommGroup Y := inferInstance
    let yMod : Module R Y := inferInstance
    let yModC : Module (realC A).R₁ Y := yMod
    letI : AddCommGroup Y := yAdd
    letI : Module R Y := yMod
    letI : Module (realC A).R₁ Y := yModC
    let Z := π₁s (realC A) Y
    let zAdd : AddCommGroup Z := inferInstance
    let zMod : Module (realC A).R₂ Z := by
      letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
      exact inferInstance
    letI : AddCommGroup Z := zAdd
    letI : Module (realC A).R₂ Z := zMod
    letI : Module (realC A).R₂ (π₁s (realC A) Y) := zMod
    let zModR : Module (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
        (π₁s (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A)
          (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) := zMod
    letI : Module (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
      (π₁s (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) := zModR
    let b := realConstantModuleEquiv P
    let a := realConstantPullbackπ₁Equiv P
    let e := normalizedCancelHom (realC A).π₁
      realC_π₁_preserves_constants P
    a.toLinearMap ∘ₗ
        (K.transportπ₁Equiv b).symm.toLinearMap = e.toLinearMap := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  let Y := R ⊗[A] P.M
  let yAdd : AddCommGroup Y := inferInstance
  let yMod : Module R Y := inferInstance
  letI : AddCommGroup Y := yAdd
  letI : Module R Y := yMod
  let yModC : Module (realC A).R₁ Y := yMod
  letI : Module (realC A).R₁ Y := yModC
  let Z := π₁s (realC A) Y
  let zAdd : AddCommGroup Z := inferInstance
  let zMod : Module (realC A).R₂ Z := by
    letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
    exact inferInstance
  letI : AddCommGroup Z := zAdd
  letI : Module (realC A).R₂ Z := zMod
  let zModR : Module (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
      (π₁s (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) := zMod
  letI : Module (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
    (π₁s (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) := zModR
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
          simp only [TensorProduct.tmul_add, map_add, hy, hz]
      | tmul s p =>
          simp only [LinearEquiv.comp_coe, LinearEquiv.coe_coe,
            LinearEquiv.trans_apply]
          let b := realConstantModuleEquiv P
          have hb : b.symm (s ⊗ₜ[A] p) = realConstantElem P s p := by
            apply b.injective
            rw [b.apply_symm_apply]
            exact (realConstantModuleEquiv_tmul P s p).symm
          let faceAlg : Algebra (realC A).R₁ (realC A).R₂ :=
            (realC A).π₁.toAlgebra
          letI : Algebra (realC A).R₁ (realC A).R₂ := faceAlg
          letI : SMul (realC A).R₁ (realC A).R₂ := faceAlg.toSMul
          letI : Module (realC A).R₁ (realC A).R₂ := faceAlg.toModule
          let faceModR : Module (realC A).R₁
              (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := faceAlg.toModule
          letI : Module (realC A).R₁
            (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := faceModR
          have hbc := LinearEquiv.baseChange_symm_tmul
            (realC A).R₁ (realC A).R₂ K.M Y
            (e := b) r (s ⊗ₜ[A] p)
          have hbc' := hbc.trans (congrArg
            (fun y : K.M => r ⊗ₜ[(realC A).R₁] y) hb)
          let a := realConstantPullbackπ₁Equiv P
          let c := normalizedCancelHom (realC A).π₁
            realC_π₁_preserves_constants P
          change a ((LinearEquiv.baseChange (realC A).R₁ (realC A).R₂
            K.M Y b).symm
              (r ⊗ₜ[(realC A).R₁] (s ⊗ₜ[A] p))) =
            c (r ⊗ₜ[(realC A).R₁] (s ⊗ₜ[A] p))
          rw [hbc']
          let z : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A :=
            (realC A).π₁ s * r
          change z ⊗ₜ[A] p = z ⊗ₜ[A] p
          rfl

private theorem realConstantModuleEquiv_pullbackπ₂
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A) :
    let R := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
    let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
    let Y := R ⊗[A] P.M
    let yAdd : AddCommGroup Y := inferInstance
    let yMod : Module R Y := inferInstance
    let yModC : Module (realC A).R₁ Y := yMod
    letI : AddCommGroup Y := yAdd
    letI : Module R Y := yMod
    letI : Module (realC A).R₁ Y := yModC
    let Z := π₂s (realC A) Y
    let zAdd : AddCommGroup Z := inferInstance
    let zMod : Module (realC A).R₂ Z := by
      letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
      exact inferInstance
    letI : AddCommGroup Z := zAdd
    letI : Module (realC A).R₂ Z := zMod
    letI : Module (realC A).R₂ (π₂s (realC A) Y) := zMod
    let zModR : Module (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
        (π₂s (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A)
          (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) := zMod
    letI : Module (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
      (π₂s (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) := zModR
    let b := realConstantModuleEquiv P
    let a := realConstantPullbackπ₂Equiv P
    let e := normalizedCancelHom (realC A).π₂
      realC_π₂_preserves_constants P
    a.toLinearMap ∘ₗ
        (K.transportπ₂Equiv b).symm.toLinearMap = e.toLinearMap := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  let Y := R ⊗[A] P.M
  let yAdd : AddCommGroup Y := inferInstance
  let yMod : Module R Y := inferInstance
  letI : AddCommGroup Y := yAdd
  letI : Module R Y := yMod
  let yModC : Module (realC A).R₁ Y := yMod
  letI : Module (realC A).R₁ Y := yModC
  let Z := π₂s (realC A) Y
  let zAdd : AddCommGroup Z := inferInstance
  let zMod : Module (realC A).R₂ Z := by
    letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
    exact inferInstance
  letI : AddCommGroup Z := zAdd
  letI : Module (realC A).R₂ Z := zMod
  let zModR : Module (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
      (π₂s (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) := zMod
  letI : Module (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
    (π₂s (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) := zModR
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
          simp only [TensorProduct.tmul_add, map_add, hy, hz]
      | tmul s p =>
          simp only [LinearEquiv.comp_coe, LinearEquiv.coe_coe,
            LinearEquiv.trans_apply]
          let b := realConstantModuleEquiv P
          have hb : b.symm (s ⊗ₜ[A] p) = realConstantElem P s p := by
            apply b.injective
            rw [b.apply_symm_apply]
            exact (realConstantModuleEquiv_tmul P s p).symm
          let faceAlg : Algebra (realC A).R₁ (realC A).R₂ :=
            (realC A).π₂.toAlgebra
          letI : Algebra (realC A).R₁ (realC A).R₂ := faceAlg
          letI : SMul (realC A).R₁ (realC A).R₂ := faceAlg.toSMul
          letI : Module (realC A).R₁ (realC A).R₂ := faceAlg.toModule
          let faceModR : Module (realC A).R₁
              (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := faceAlg.toModule
          letI : Module (realC A).R₁
            (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := faceModR
          have hbc := LinearEquiv.baseChange_symm_tmul
            (realC A).R₁ (realC A).R₂ K.M Y
            (e := b) r (s ⊗ₜ[A] p)
          have hbc' := hbc.trans (congrArg
            (fun y : K.M => r ⊗ₜ[(realC A).R₁] y) hb)
          let a := realConstantPullbackπ₂Equiv P
          let c := normalizedCancelHom (realC A).π₂
            realC_π₂_preserves_constants P
          change a ((LinearEquiv.baseChange (realC A).R₁ (realC A).R₂
            K.M Y b).symm
              (r ⊗ₜ[(realC A).R₁] (s ⊗ₜ[A] p))) =
            c (r ⊗ₜ[(realC A).R₁] (s ⊗ₜ[A] p))
          rw [hbc']
          let z : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A :=
            (realC A).π₂ s * r
          change z ⊗ₜ[A] p = z ⊗ₜ[A] p
          rfl

/-- Normalized pullback along the first face is conjugate to pullback on the
constant descent module through `realConstantModuleEquiv`. -/
theorem π₁End_eq_conj
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (ξ : (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M) ≃ₗ[NovikovSeries
      (⊤ : AddSubgroup ℝ) Unit A]
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) :
    let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
    let b := realConstantModuleEquiv P
    let ξK := b.trans (ξ.trans b.symm)
    π₁End P ξ.toLinearMap =
      (realConstantPullbackπ₁Equiv P).toLinearMap ∘ₗ
        (K.transportπ₁Equiv ξK).toLinearMap ∘ₗ
          (realConstantPullbackπ₁Equiv P).symm.toLinearMap := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  let Y := R ⊗[A] P.M
  let yAdd : AddCommGroup Y := inferInstance
  let yMod : Module R Y := inferInstance
  letI : AddCommGroup Y := yAdd
  letI : Module R Y := yMod
  let yModC : Module (realC A).R₁ Y := yMod
  letI : Module (realC A).R₁ Y := yModC
  let Z := π₁s (realC A) Y
  let zAdd : AddCommGroup Z := inferInstance
  let zMod : Module (realC A).R₂ Z := by
    letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
    exact inferInstance
  letI : AddCommGroup Z := zAdd
  letI : Module (realC A).R₂ Z := zMod
  let zModR : Module (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
      (π₁s (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) := zMod
  letI : Module (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
    (π₁s (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) := zModR
  let faceAlg : Algebra (realC A).R₁ (realC A).R₂ :=
    (realC A).π₁.toAlgebra
  letI : Algebra (realC A).R₁ (realC A).R₂ := faceAlg
  letI : SMul (realC A).R₁ (realC A).R₂ := faceAlg.toSMul
  letI : Module (realC A).R₁ (realC A).R₂ := faceAlg.toModule
  let faceModR : Module (realC A).R₁
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := faceAlg.toModule
  letI : Module (realC A).R₁
    (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := faceModR
  letI : RingHomInvPair
      (RingHom.id (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A).R₂)
      (RingHom.id (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A).R₂) :=
    RingHomInvPair.ids
  let b := realConstantModuleEquiv P
  let a := realConstantPullbackπ₁Equiv P
  let e := normalizedCancelHom (realC A).π₁
    realC_π₁_preserves_constants P
  let B := K.transportπ₁Equiv b
  let X := LinearEquiv.baseChange
    (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A).R₁
    (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A).R₂ Y Y ξ
  let ξK := b.trans (ξ.trans b.symm)
  have hc := realConstantModuleEquiv_pullbackπ₁ P
  have hc_apply (x) : a (B.symm x) = e x :=
    LinearMap.congr_fun hc x
  have hc_inv_apply (x) : B (a.symm x) = e.symm x := by
    apply e.injective
    rw [← hc_apply (B (a.symm x))]
    simp
  have hK_apply (x) :
      (K.transportπ₁Equiv ξK) x = B.symm (X (B x)) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r x =>
        simp [ξK, B, X, DescentDatum.transportπ₁Equiv]
        rfl
  apply LinearMap.ext
  intro x
  change e (X (e.symm x)) =
    a ((K.transportπ₁Equiv ξK) (a.symm x))
  rw [hK_apply, hc_apply, hc_inv_apply]

/-- Normalized pullback along the second face is conjugate to pullback on the
constant descent module through `realConstantModuleEquiv`. -/
theorem π₂End_eq_conj
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (ξ : (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M) ≃ₗ[NovikovSeries
      (⊤ : AddSubgroup ℝ) Unit A]
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) :
    let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
    let b := realConstantModuleEquiv P
    let ξK := b.trans (ξ.trans b.symm)
    π₂End P ξ.toLinearMap =
      (realConstantPullbackπ₂Equiv P).toLinearMap ∘ₗ
        (K.transportπ₂Equiv ξK).toLinearMap ∘ₗ
          (realConstantPullbackπ₂Equiv P).symm.toLinearMap := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  let Y := R ⊗[A] P.M
  let yAdd : AddCommGroup Y := inferInstance
  let yMod : Module R Y := inferInstance
  letI : AddCommGroup Y := yAdd
  letI : Module R Y := yMod
  let yModC : Module (realC A).R₁ Y := yMod
  letI : Module (realC A).R₁ Y := yModC
  let Z := π₂s (realC A) Y
  let zAdd : AddCommGroup Z := inferInstance
  let zMod : Module (realC A).R₂ Z := by
    letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
    exact inferInstance
  letI : AddCommGroup Z := zAdd
  letI : Module (realC A).R₂ Z := zMod
  let zModR : Module (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
      (π₂s (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) := zMod
  letI : Module (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
    (π₂s (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M)) := zModR
  let faceAlg : Algebra (realC A).R₁ (realC A).R₂ :=
    (realC A).π₂.toAlgebra
  letI : Algebra (realC A).R₁ (realC A).R₂ := faceAlg
  letI : SMul (realC A).R₁ (realC A).R₂ := faceAlg.toSMul
  letI : Module (realC A).R₁ (realC A).R₂ := faceAlg.toModule
  let faceModR : Module (realC A).R₁
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := faceAlg.toModule
  letI : Module (realC A).R₁
    (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) := faceModR
  letI : RingHomInvPair
      (RingHom.id (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A).R₂)
      (RingHom.id (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A).R₂) :=
    RingHomInvPair.ids
  let b := realConstantModuleEquiv P
  let a := realConstantPullbackπ₂Equiv P
  let e := normalizedCancelHom (realC A).π₂
    realC_π₂_preserves_constants P
  let B := K.transportπ₂Equiv b
  let X := LinearEquiv.baseChange
    (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A).R₁
    (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A).R₂ Y Y ξ
  let ξK := b.trans (ξ.trans b.symm)
  have hc := realConstantModuleEquiv_pullbackπ₂ P
  have hc_apply (x) : a (B.symm x) = e x :=
    LinearMap.congr_fun hc x
  have hc_inv_apply (x) : B (a.symm x) = e.symm x := by
    apply e.injective
    rw [← hc_apply (B (a.symm x))]
    simp
  have hK_apply (x) :
      (K.transportπ₂Equiv ξK) x = B.symm (X (B x)) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r x =>
        simp [ξK, B, X, DescentDatum.transportπ₂Equiv]
        rfl
  apply LinearMap.ext
  intro x
  change e (X (e.symm x)) =
    a ((K.transportπ₂Equiv ξK) (a.symm x))
  rw [hK_apply, hc_apply, hc_inv_apply]

private lemma realC_π₁₂_preserves_constants
    {A : Type*} [CommRing A] :
    (realC A).π₁₂.comp algebraMapNovikov = algebraMapNovikov := by
  change (substituteRingHom Fin.castSucc).comp algebraMapNovikov =
    algebraMapNovikov
  exact substituteRingHom_preserves_constants _

private lemma realC_π₁₃_preserves_constants
    {A : Type*} [CommRing A] :
    (realC A).π₁₃.comp algebraMapNovikov = algebraMapNovikov := by
  change (substituteRingHom (Fin.succAbove 1)).comp algebraMapNovikov =
    algebraMapNovikov
  exact substituteRingHom_preserves_constants _

private lemma realC_π₂₃_preserves_constants
    {A : Type*} [CommRing A] :
    (realC A).π₂₃.comp algebraMapNovikov = algebraMapNovikov := by
  change (substituteRingHom Fin.succ).comp algebraMapNovikov =
    algebraMapNovikov
  exact substituteRingHom_preserves_constants _

private lemma realC_ρ₁_preserves_constants
    {A : Type*} [CommRing A] :
    (realC A).ρ₁.comp algebraMapNovikov = algebraMapNovikov := by
  rw [(realC A).ρ₁_eq_π₁₂_π₁, RingHom.comp_assoc,
    realC_π₁_preserves_constants, realC_π₁₂_preserves_constants]

private lemma realC_ρ₂_preserves_constants
    {A : Type*} [CommRing A] :
    (realC A).ρ₂.comp algebraMapNovikov = algebraMapNovikov := by
  rw [(realC A).ρ₂_eq_π₁₂_π₂, RingHom.comp_assoc,
    realC_π₂_preserves_constants, realC_π₁₂_preserves_constants]

private lemma realC_ρ₃_preserves_constants
    {A : Type*} [CommRing A] :
    (realC A).ρ₃.comp algebraMapNovikov = algebraMapNovikov := by
  rw [show (realC A).ρ₃ = (realC A).π₂₃.comp (realC A).π₂ from rfl,
    RingHom.comp_assoc, realC_π₂_preserves_constants,
    realC_π₂₃_preserves_constants]

private theorem normalizedPhi_pullback_12
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (φ : π₁s (realC A)
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M ≃ₗ[(realC A).R₂]
      π₂s (realC A)
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M) :
    let C := realC A
    let b₁ := constantCancelHom C.ρ₁
      realC_ρ₁_preserves_constants P
    let b₂ := constantCancelHom C.ρ₂
      realC_ρ₂_preserves_constants P
    π₁₂End P (normalizedPhi P φ) =
      b₂.toLinearMap ∘ₗ (pullbackMap_12 C _ φ).toLinearMap ∘ₗ
        b₁.symm.toLinearMap := by
  let C := realC A
  have hn := normalized_pullback C.π₁ C.π₂ C.π₁₂ C.ρ₁ C.ρ₂
    C.ρ₁_eq_π₁₂_π₁.symm C.ρ₂_eq_π₁₂_π₂.symm
    realC_π₁_preserves_constants realC_π₂_preserves_constants
    realC_π₁₂_preserves_constants realC_ρ₁_preserves_constants
    realC_ρ₂_preserves_constants P φ
  simpa only [π₁₂End, normalizedEndBaseChange, normalizedPhi,
    realConstantPullbackπ₁Equiv, realConstantPullbackπ₂Equiv,
    constantCancelHom, normalizedCancelHom,
    pullbackMap_12, RingHom.comp_apply, AlgHom.toRingHom_eq_coe] using hn

private theorem normalizedPhi_pullback_13
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (φ : π₁s (realC A)
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M ≃ₗ[(realC A).R₂]
      π₂s (realC A)
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M) :
    let C := realC A
    let b₁ := constantCancelHom C.ρ₁
      realC_ρ₁_preserves_constants P
    let b₃ := constantCancelHom C.ρ₃
      realC_ρ₃_preserves_constants P
    π₁₃End P (normalizedPhi P φ) =
      b₃.toLinearMap ∘ₗ (pullbackMap_13 C _ φ).toLinearMap ∘ₗ
        b₁.symm.toLinearMap := by
  let C := realC A
  have hn := normalized_pullback C.π₁ C.π₂ C.π₁₃ C.ρ₁ C.ρ₃
    C.ρ₁_eq_π₁₃_π₁.symm C.ρ₃_eq_π₁₃_π₂.symm
    realC_π₁_preserves_constants realC_π₂_preserves_constants
    realC_π₁₃_preserves_constants realC_ρ₁_preserves_constants
    realC_ρ₃_preserves_constants P φ
  simpa only [π₁₃End, normalizedEndBaseChange, normalizedPhi,
    realConstantPullbackπ₁Equiv, realConstantPullbackπ₂Equiv,
    constantCancelHom, normalizedCancelHom,
    pullbackMap_13, RingHom.comp_apply, AlgHom.toRingHom_eq_coe] using hn

private theorem normalizedPhi_pullback_23
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (φ : π₁s (realC A)
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M ≃ₗ[(realC A).R₂]
      π₂s (realC A)
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M) :
    let C := realC A
    let b₂ := constantCancelHom C.ρ₂
      realC_ρ₂_preserves_constants P
    let b₃ := constantCancelHom C.ρ₃
      realC_ρ₃_preserves_constants P
    π₂₃End P (normalizedPhi P φ) =
      b₃.toLinearMap ∘ₗ (pullbackMap_23 C _ φ).toLinearMap ∘ₗ
        b₂.symm.toLinearMap := by
  let C := realC A
  have hn := normalized_pullback C.π₁ C.π₂ C.π₂₃ C.ρ₂ C.ρ₃
    rfl rfl realC_π₁_preserves_constants
    realC_π₂_preserves_constants realC_π₂₃_preserves_constants
    realC_ρ₂_preserves_constants realC_ρ₃_preserves_constants P φ
  simpa only [π₂₃End, normalizedEndBaseChange, normalizedPhi,
    realConstantPullbackπ₁Equiv, realConstantPullbackπ₂Equiv,
    constantCancelHom, normalizedCancelHom,
    pullbackMap_23, RingHom.comp_apply, AlgHom.toRingHom_eq_coe] using hn

private theorem conjugated_cocycle
    {R X₁ X₂ X₃ V : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁]
    [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup X₃] [Module R X₃]
    [AddCommGroup V] [Module R V]
    (b₁ : X₁ ≃ₗ[R] V) (b₂ : X₂ ≃ₗ[R] V) (b₃ : X₃ ≃ₗ[R] V)
    (f₁₂ : X₁ ≃ₗ[R] X₂) (f₂₃ : X₂ ≃ₗ[R] X₃)
    (f₁₃ : X₁ ≃ₗ[R] X₃)
    (h : f₂₃.toLinearMap ∘ f₁₂.toLinearMap = f₁₃.toLinearMap) :
    (b₃.toLinearMap ∘ₗ f₂₃.toLinearMap ∘ₗ b₂.symm.toLinearMap) ∘ₗ
        (b₂.toLinearMap ∘ₗ f₁₂.toLinearMap ∘ₗ b₁.symm.toLinearMap) =
      b₃.toLinearMap ∘ₗ f₁₃.toLinearMap ∘ₗ b₁.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change b₃ (f₂₃ (b₂.symm (b₂ (f₁₂ (b₁.symm x))))) =
    b₃ (f₁₃ (b₁.symm x))
  rw [b₂.symm_apply_apply]
  exact congrArg b₃ (congrFun h (b₁.symm x))

/-- The normalized endomorphism attached to a descent isomorphism satisfies
the multiplicative Čech cocycle identity. -/
theorem normalizedPhi_cocycle
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (φ : π₁s (realC A)
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M ≃ₗ[(realC A).R₂]
      π₂s (realC A)
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M)
    (hφ :
      (pullbackMap_23 (realC A) _ φ).toLinearMap ∘
          (pullbackMap_12 (realC A) _ φ).toLinearMap =
        (pullbackMap_13 (realC A) _ φ).toLinearMap) :
    π₂₃End P (normalizedPhi P φ) ∘ₗ
        π₁₂End P (normalizedPhi P φ) =
      π₁₃End P (normalizedPhi P φ) := by
  rw [normalizedPhi_pullback_23,
    normalizedPhi_pullback_12, normalizedPhi_pullback_13]
  let C := realC A
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  let R₃ := NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) A
  letI : Module R₃ (ρ₁s C K.M) :=
    (inferInstance : Module C.R₃ (ρ₁s C K.M))
  letI : Module R₃ (ρ₂s C K.M) :=
    (inferInstance : Module C.R₃ (ρ₂s C K.M))
  letI : Module R₃ (ρ₃s C K.M) :=
    (inferInstance : Module C.R₃ (ρ₃s C K.M))
  exact conjugated_cocycle _ _ _ _ _ _ hφ

end Novikov.Descent
