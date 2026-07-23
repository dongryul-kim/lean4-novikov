import Novikov.Descent.Normalization
import Novikov.Descent.SquareZero

/-!
# Square-zero deformation of Novikov descent data

This file isolates the normalization-heavy deformation argument from the
reusable additive and coefficientwise square-zero machinery. In particular,
the concrete coefficient comparison is checked once here rather than whenever
`SquareZero.lean` changes.
-/

namespace Novikov.Descent

open Novikov Novikov.Miscellany TensorProduct

universe u

open CategoryTheory Abstract

/-! ## The constant normalized descent isomorphism -/

private noncomputable def realConstantπ₁Elem
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (r : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) (p : P.M) :
    π₁s (realC A)
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A
  letI : Module E.R₀ P.M := P.instModule
  let e₀₁Alg : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₀ E.R₁ := e₀₁Alg
  let e₁₂Alg : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
  letI : Algebra E.R₁ E.R₂ := e₁₂Alg
  letI : Module E.R₁ (realC A).R₂ := e₁₂Alg.toModule
  exact (show E.R₂ from r) ⊗ₜ[E.R₁]
    ((1 : E.R₁) ⊗ₜ[E.R₀] p)

private noncomputable def realConstantπ₂Elem
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (r : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) (p : P.M) :
    π₂s (realC A)
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M := by
  let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A
  letI : Module E.R₀ P.M := P.instModule
  let e₀₁Alg : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₀ E.R₁ := e₀₁Alg
  let e₁₂Alg : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
  letI : Algebra E.R₁ E.R₂ := e₁₂Alg
  letI : Module E.R₁ (realC A).R₂ := e₁₂Alg.toModule
  exact (show E.R₂ from r) ⊗ₜ[E.R₁]
    ((1 : E.R₁) ⊗ₜ[E.R₀] p)

private lemma realConstantPullbackπ₁Equiv_symm_tmul
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (r : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) (p : P.M) :
    (realConstantPullbackπ₁Equiv P).symm (r ⊗ₜ[A] p) =
      realConstantπ₁Elem P r p := by
  rw [realConstantPullbackπ₁Equiv, realConstantπ₁Elem]
  let R₁ := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
  let R₂ := NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A
  let aR₁ : Algebra A R₁ :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A).π₀.toAlgebra
  let aR₂ : Algebra A R₂ := inferInstance
  letI : Algebra A R₁ := aR₁
  letI : SMul A R₁ := aR₁.toSMul
  letI : Module A R₁ := aR₁.toModule
  letI : Algebra A R₂ := aR₂
  letI : SMul A R₂ := aR₂.toSMul
  letI : Module A R₂ := aR₂.toModule
  let r₁R₂Alg : Algebra R₁ R₂ := (realC A).π₁.toAlgebra
  letI : Algebra R₁ R₂ := r₁R₂Alg
  letI : SMul R₁ R₂ := r₁R₂Alg.toSMul
  letI : Module R₁ R₂ := r₁R₂Alg.toModule
  letI : IsScalarTower A R₁ R₂ :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      change algebraMapNovikov a = substitute (fun _ : Unit => (0 : Fin 2))
        (algebraMapNovikov a)
      exact (substitute_algebraMap _ a).symm)
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul
    A R₁ R₂ r p

private lemma realConstantPullbackπ₂Equiv_tmul
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (r : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A) (p : P.M) :
    realConstantPullbackπ₂Equiv P (realConstantπ₂Elem P r p) =
      r ⊗ₜ[A] p := by
  rw [realConstantPullbackπ₂Equiv, realConstantπ₂Elem]
  let R₁ := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
  let R₂ := NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A
  let aR₁ : Algebra A R₁ :=
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A).π₀.toAlgebra
  let aR₂ : Algebra A R₂ := inferInstance
  letI : Algebra A R₁ := aR₁
  letI : SMul A R₁ := aR₁.toSMul
  letI : Module A R₁ := aR₁.toModule
  letI : Algebra A R₂ := aR₂
  letI : SMul A R₂ := aR₂.toSMul
  letI : Module A R₂ := aR₂.toModule
  let r₁R₂Alg : Algebra R₁ R₂ := (realC A).π₂.toAlgebra
  letI : Algebra R₁ R₂ := r₁R₂Alg
  letI : SMul R₁ R₂ := r₁R₂Alg.toSMul
  letI : Module R₁ R₂ := r₁R₂Alg.toModule
  letI : IsScalarTower A R₁ R₂ :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      change algebraMapNovikov a = substitute (fun _ : Unit => (1 : Fin 2))
        (algebraMapNovikov a)
      exact (substitute_algebraMap _ a).symm)
  simpa only [one_smul] using
    (TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul
      A R₁ R₂ r p (1 : R₁))

-- Keep these definitions opaque while matching the pure-tensor wrappers.
attribute [local irreducible]
  realConstantPullbackπ₁Equiv realConstantPullbackπ₂Equiv

/-- The constant descent isomorphism normalizes to the identity. -/
lemma normalizedPhi_constant
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A) :
    normalizedPhi P
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).φ = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp [normalizedPhi]
  | add x y hx hy => simp only [map_add, LinearMap.id_apply, hx, hy]
  | tmul r p =>
      change realConstantPullbackπ₂Equiv P
          (((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).φ
            ((realConstantPullbackπ₁Equiv P).symm (r ⊗ₜ[A] p))) =
        r ⊗ₜ[A] p
      rw [realConstantPullbackπ₁Equiv_symm_tmul]
      have hφ :
          ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).φ
              (realConstantπ₁Elem P r p) =
            realConstantπ₂Elem P r p := by
        let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A
        letI : Module E.R₀ P.M := P.instModule
        letI : Module.Finite E.R₀ P.M := P.instFinite
        letI : Module.Projective E.R₀ P.M := P.instProjective
        rw [show ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).φ =
          (constantDescentDatum E P.M).φ from rfl]
        rw [realConstantπ₁Elem, realConstantπ₂Elem]
        have h := constantDescentDatum_φ_tmul E P.M
          (show E.R₂ from r) (1 : E.R₁) p
        simpa only [map_one, one_mul] using h
      rw [hφ, realConstantPullbackπ₂Equiv_tmul]

/-! ## The square-zero deformation argument -/

private theorem exists_lifted_constant_reduction
    (A B : Type u) [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (hM : ∃ Q : FiniteProjectiveModule.{u, u} B,
      Nonempty
        ((vectToNovikovDescent.{0, u, u}
            (⊤ : AddSubgroup ℝ) B).obj Q ≅
          M.baseChange (realCCoeffHom q))) :
    ∃ P : FiniteProjectiveModule.{u, u} A,
      Nonempty
        (M.baseChange (realCCoeffHom q) ≅
          ((vectToNovikovDescent.{0, u, u}
            (⊤ : AddSubgroup ℝ) A).obj P).baseChange
              (realCCoeffHom q)) := by
  rcases hM with ⟨Q, ⟨eBar⟩⟩
  rcases FiniteProjectiveModule.exists_lift_of_surjective_of_ker_sq
      q hq hq_sq Q with
    ⟨P, ⟨eQ⟩⟩
  refine ⟨P, ⟨?_⟩⟩
  exact eBar.symm ≪≫
    (vectToNovikovDescent (⊤ : AddSubgroup ℝ) B).mapIso eQ.symm ≪≫
      (vectToNovikovDescent_baseChangeIso q P).symm

private theorem exists_underlying_linearEquiv_lift
    (A B : Type u) [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (P : FiniteProjectiveModule.{u, u} A)
    (eRed :
      M.baseChange (realCCoeffHom q) ≅
        ((vectToNovikovDescent.{0, u, u}
          (⊤ : AddSubgroup ℝ) A).obj P).baseChange
            (realCCoeffHom q)) :
    let C := (vectToNovikovDescent.{0, u, u}
      (⊤ : AddSubgroup ℝ) A).obj P
    let F := realCCoeffHom q
    ∃ θ : M.M ≃ₗ[(realC A).R₁] C.M,
      baseChangeLinearEquiv F.f₁ θ = Abstract.DescentDatum.isoLinearEquiv eRed ∧
        Nonempty (M ≅ M.transport θ) := by
  let C := (vectToNovikovDescent.{0, u, u}
    (⊤ : AddSubgroup ℝ) A).obj P
  let F := realCCoeffHom q
  have hF_surj : Function.Surjective F.f₁ := by
    rw [show F.f₁ = mapRingHom q from realCCoeffHom_f₁ q]
    exact mapRingHom_surjective q hq
  have hF_sq : RingHom.ker F.f₁ ^ 2 = ⊥ := by
    rw [show F.f₁ = mapRingHom q from realCCoeffHom_f₁ q]
    exact mapRingHom_ker_sq q hq_sq
  obtain ⟨θ, hθ⟩ := exists_linearEquiv_lift_of_surjective_of_ker_sq
    F.f₁ hF_surj hF_sq (Abstract.DescentDatum.isoLinearEquiv eRed)
  exact ⟨θ, hθ, ⟨M.transportIso θ⟩⟩

private theorem normalizedPhi_coefficient_eq_constant
    {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B)
    (P : FiniteProjectiveModule.{u, u} A)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (θ : M.M ≃ₗ[(realC A).R₁]
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M)
    (eRed : M.baseChange (realCCoeffHom q) ≅
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).baseChange
        (realCCoeffHom q))
    (hθ : baseChangeLinearEquiv
        (A := (realC A).R₁) (B := (realC B).R₁)
        (realCCoeffHom q).f₁ θ = Abstract.DescentDatum.isoLinearEquiv eRed) :
    q₂End q P (normalizedPhi P (M.transport θ).φ) =
      q₂End q P (normalizedPhi P
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).φ) := by
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  let F := realCCoeffHom q
  have hφ := Abstract.DescentDatum.baseChangeMap_transport_φ_eq
    F M K θ eRed hθ
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A
  let S := NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) B
  let qR := mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) q
  letI : Algebra R S := qR.toAlgebra
  letI : Algebra (realC A).R₂ S := qR.toAlgebra
  letI : Module R (Abstract.π₁s (realC A) K.M) :=
    (inferInstance : Module (realC A).R₂ (Abstract.π₁s (realC A) K.M))
  letI : Module R (Abstract.π₂s (realC A) K.M) :=
    (inferInstance : Module (realC A).R₂ (Abstract.π₂s (realC A) K.M))
  have hφ' : LinearMap.baseChange S (M.transport θ).φ.toLinearMap =
      LinearMap.baseChange S K.φ.toLinearMap := by
    exact hφ
  have hn : LinearMap.baseChange S
        (normalizedPhi P (M.transport θ).φ) =
      LinearMap.baseChange S (normalizedPhi P K.φ) := by
    simp only [normalizedPhi]
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp,
      LinearMap.baseChange_comp, LinearMap.baseChange_comp]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    congr 1
    exact LinearMap.congr_fun hφ' _
  rw [q₂End, coefficientEndBaseChange]
  exact congrArg (coefficientModuleBaseChangeEquiv q P).conjRingEquiv hn

private theorem normalizedPhi_coefficient_eq_id
    {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B)
    (P : FiniteProjectiveModule.{u, u} A)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (θ : M.M ≃ₗ[(realC A).R₁]
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M)
    (eRed : M.baseChange (realCCoeffHom q) ≅
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).baseChange
        (realCCoeffHom q))
    (hθ : baseChangeLinearEquiv
        (A := (realC A).R₁) (B := (realC B).R₁)
        (realCCoeffHom q).f₁ θ = Abstract.DescentDatum.isoLinearEquiv eRed) :
    q₂End q P (normalizedPhi P (M.transport θ).φ) = LinearMap.id := by
  rw [normalizedPhi_coefficient_eq_constant q P M θ eRed hθ]
  rw [normalizedPhi_constant]
  exact map_one (q₂End q P)

private theorem normalizedPhi_sub_id_coefficient_eq_zero
    {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B)
    (P : FiniteProjectiveModule.{u, u} A)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (θ : M.M ≃ₗ[(realC A).R₁]
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M)
    (eRed : M.baseChange (realCCoeffHom q) ≅
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).baseChange
        (realCCoeffHom q))
    (hθ : baseChangeLinearEquiv
        (A := (realC A).R₁) (B := (realC B).R₁)
        (realCCoeffHom q).f₁ θ = Abstract.DescentDatum.isoLinearEquiv eRed) :
    q₂End q P (normalizedPhi P (M.transport θ).φ - LinearMap.id) = 0 := by
  rw [map_sub, normalizedPhi_coefficient_eq_id q P M θ eRed hθ]
  rw [show q₂End q P LinearMap.id = LinearMap.id from map_one (q₂End q P)]
  exact sub_self LinearMap.id

private theorem comp_eq_zero_of_conj_baseChange_eq_zero
    {A B : Type u} {M N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N]
    (q : A →+* B) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (e : letI : Algebra A B := q.toAlgebra; (B ⊗[A] M) ≃ₗ[B] N)
    (u v : Module.End A M)
    (hu :
      (letI : Algebra A B := q.toAlgebra
       e.conjRingEquiv (LinearMap.baseChange B u)) = 0)
    (hv :
      (letI : Algebra A B := q.toAlgebra
       e.conjRingEquiv (LinearMap.baseChange B v)) = 0) :
    u ∘ₗ v = 0 := by
  letI : Algebra A B := q.toAlgebra
  have hu' : LinearMap.baseChange B u = 0 := by
    apply e.conjRingEquiv.injective
    rw [map_zero]
    exact hu
  have hv' : LinearMap.baseChange B v = 0 := by
    apply e.conjRingEquiv.injective
    rw [map_zero]
    exact hv
  exact comp_eq_zero_of_baseChangeMap_eq_zero q hq hq_sq u v hu' hv'

private theorem fin3_comp_eq_zero_of_coefficientEndBaseChange_eq_zero
    {C D : Type u} [CommRing C] [CommRing D]
    (q : C →+* D) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (P : FiniteProjectiveModule C)
    (u v : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) C)
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) C ⊗[C] P.M))
    (hu : q₃End q P u = 0) (hv : q₃End q P v = 0) :
    u ∘ₗ v = 0 := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) C
  let S := NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) D
  let qR := mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 3) q
  letI : Algebra R S := qR.toAlgebra
  let e := coefficientModuleBaseChangeEquiv (ι := Fin 3) q P
  have hqR_surj : Function.Surjective qR :=
    mapRingHom_surjective q hq
  have hqR_sq : RingHom.ker qR ^ 2 = ⊥ :=
    mapRingHom_ker_sq q hq_sq
  change e.conjRingEquiv (LinearMap.baseChange S u) = 0 at hu
  change e.conjRingEquiv (LinearMap.baseChange S v) = 0 at hv
  exact comp_eq_zero_of_conj_baseChange_eq_zero
    qR hqR_surj hqR_sq e u v hu hv

private theorem face_coefficient_eq_zero
    {C D : Type*} [CommRing C] [CommRing D]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (f : Fin 2 → Fin 3)
    (δ : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C ⊗[C] P.M))
    (hδq : q₂End q P δ = 0) :
    q₃End q P (normalizedEndBaseChange (substituteAlgHom f) P δ) = 0 := by
  change coefficientEndBaseChange (ι := Fin 3) q P
    (normalizedEndBaseChange (substituteAlgHom f) P δ) = 0
  rw [normalizedEndBaseChange_coefficient_naturality]
  change normalizedEndBaseChange (substituteAlgHom f)
    (P.baseChange q) (q₂End q P δ) = 0
  rw [hδq, map_zero]

private theorem sub_id_is_add_cocycle
    {C D : Type u} [CommRing C] [CommRing D]
    (q : C →+* D) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (P : FiniteProjectiveModule C)
    (ψ : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C ⊗[C] P.M))
    (hψ : π₂₃End P ψ ∘ₗ π₁₂End P ψ = π₁₃End P ψ)
    (hδq : q₂End q P (ψ - LinearMap.id) = 0) :
    let δ := ψ - LinearMap.id
    π₁₃End P δ = π₂₃End P δ + π₁₂End P δ := by
  let δ := ψ - LinearMap.id
  have h12q : q₃End q P (π₁₂End P δ) = 0 :=
    face_coefficient_eq_zero q P Fin.castSucc δ hδq
  have h23q : q₃End q P (π₂₃End P δ) = 0 :=
    face_coefficient_eq_zero q P Fin.succ δ hδq
  have hcomp : π₂₃End P δ ∘ₗ π₁₂End P δ = 0 :=
    fin3_comp_eq_zero_of_coefficientEndBaseChange_eq_zero
      q hq hq_sq P (π₂₃End P δ) (π₁₂End P δ) h23q h12q
  have hψδ : ψ = LinearMap.id + δ := by
    dsimp only [δ]
    abel
  rw [hψδ, map_add, map_add, map_add] at hψ
  have h12id : π₁₂End P LinearMap.id = LinearMap.id :=
    map_one (π₁₂End P)
  have h13id : π₁₃End P LinearMap.id = LinearMap.id :=
    map_one (π₁₃End P)
  have h23id : π₂₃End P LinearMap.id = LinearMap.id :=
    map_one (π₂₃End P)
  rw [h12id, h13id, h23id] at hψ
  rw [LinearMap.add_comp] at hψ
  rw [LinearMap.comp_add, LinearMap.comp_add] at hψ
  simp only [LinearMap.id_comp, LinearMap.comp_id] at hψ
  rw [hcomp, add_zero] at hψ
  change π₁₃End P δ = π₂₃End P δ + π₁₂End P δ
  calc
    π₁₃End P δ = (LinearMap.id + π₁₃End P δ) - LinearMap.id := by abel
    _ = (LinearMap.id + π₁₂End P δ + π₂₃End P δ) - LinearMap.id :=
      congrArg (fun z => z - LinearMap.id) hψ.symm
    _ = π₂₃End P δ + π₁₂End P δ := by abel

private theorem normalizedPhi_sub_id_is_add_cocycle
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (P : FiniteProjectiveModule.{u, u} A)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (θ : M.M ≃ₗ[(realC A).R₁]
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M)
    (eRed : M.baseChange (realCCoeffHom q) ≅
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).baseChange
        (realCCoeffHom q))
    (hθ : baseChangeLinearEquiv
        (A := (realC A).R₁) (B := (realC B).R₁)
        (realCCoeffHom q).f₁ θ = Abstract.DescentDatum.isoLinearEquiv eRed) :
    let ψ := normalizedPhi P (M.transport θ).φ
    let δ := ψ - LinearMap.id
    π₁₃End P δ = π₂₃End P δ + π₁₂End P δ := by
  let ψ := normalizedPhi P (M.transport θ).φ
  have hψ : π₂₃End P ψ ∘ₗ π₁₂End P ψ = π₁₃End P ψ :=
    normalizedPhi_cocycle P (M.transport θ).φ (M.transport θ).cocycle
  have hδq : q₂End q P (ψ - LinearMap.id) = 0 :=
    normalizedPhi_sub_id_coefficient_eq_zero q P M θ eRed hθ
  exact sub_id_is_add_cocycle q hq hq_sq P ψ hψ hδq

private theorem exists_normalizedPhi_correcting_end
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (P : FiniteProjectiveModule.{u, u} A)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (θ : M.M ≃ₗ[(realC A).R₁]
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M)
    (eRed : M.baseChange (realCCoeffHom q) ≅
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).baseChange
        (realCCoeffHom q))
    (hθ : baseChangeLinearEquiv
        (A := (realC A).R₁) (B := (realC B).R₁)
        (realCCoeffHom q).f₁ θ = Abstract.DescentDatum.isoLinearEquiv eRed) :
    ∃ η : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M),
      normalizedPhi P (M.transport θ).φ - LinearMap.id =
          π₁End P η - π₂End P η ∧
        q₁End q P η = 0 := by
  let ψ := normalizedPhi P (M.transport θ).φ
  let δ := ψ - LinearMap.id
  have hδ : π₁₃End P δ = π₂₃End P δ + π₁₂End P δ :=
    normalizedPhi_sub_id_is_add_cocycle q hq hq_sq P M θ eRed hθ
  have hδq : q₂End q P δ = 0 :=
    normalizedPhi_sub_id_coefficient_eq_zero q P M θ eRed hθ
  exact exists_end_eq_sub_of_is_add_cocycle_of_map_eq_zero q P δ hδ hδq

private theorem comp_eq_zero_of_coefficientEndBaseChange_eq_zero
    {C D : Type u} {ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (P : FiniteProjectiveModule C)
    (u v : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) ι C)
      (NovikovSeries (⊤ : AddSubgroup ℝ) ι C ⊗[C] P.M))
    (hu : coefficientEndBaseChange (ι := ι) q P u = 0)
    (hv : coefficientEndBaseChange (ι := ι) q P v = 0) :
    u ∘ₗ v = 0 := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι C
  let S := NovikovSeries (⊤ : AddSubgroup ℝ) ι D
  let qR := mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) q
  letI : Algebra R S := qR.toAlgebra
  let e := coefficientModuleBaseChangeEquiv (ι := ι) q P
  have hqR_surj : Function.Surjective qR :=
    mapRingHom_surjective q hq
  have hqR_sq : RingHom.ker qR ^ 2 = ⊥ :=
    mapRingHom_ker_sq q hq_sq
  change e.conjRingEquiv (LinearMap.baseChange S u) = 0 at hu
  change e.conjRingEquiv (LinearMap.baseChange S v) = 0 at hv
  have hu' : LinearMap.baseChange S u = 0 := by
    apply e.conjRingEquiv.injective
    rw [map_zero]
    exact hu
  have hv' : LinearMap.baseChange S v = 0 := by
    apply e.conjRingEquiv.injective
    rw [map_zero]
    exact hv
  exact comp_eq_zero_of_baseChangeMap_eq_zero
    qR hqR_surj hqR_sq u v hu' hv'

private theorem normalizedEndBaseChange_coefficient_eq_zero
    {C D ι κ : Type*} [CommRing C] [CommRing D]
    [Fintype ι] [Fintype κ]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (f : ι → κ)
    (δ : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) ι C)
      (NovikovSeries (⊤ : AddSubgroup ℝ) ι C ⊗[C] P.M))
    (hδq : coefficientEndBaseChange (ι := ι) q P δ = 0) :
    coefficientEndBaseChange (ι := κ) q P
      (normalizedEndBaseChange (substituteAlgHom f) P δ) = 0 := by
  rw [normalizedEndBaseChange_coefficient_naturality]
  rw [hδq, map_zero]

private theorem correcting_end_sq_zero
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (P : FiniteProjectiveModule A)
    (η : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M))
    (hηq : q₁End q P η = 0) :
    η ∘ₗ η = 0 := by
  change coefficientEndBaseChange (ι := Unit) q P η = 0 at hηq
  exact comp_eq_zero_of_coefficientEndBaseChange_eq_zero
    q hq hq_sq P η η hηq hηq

private theorem correcting_faces_comp_eq_zero
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (P : FiniteProjectiveModule A)
    (η : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M))
    (hηq : q₁End q P η = 0) :
    π₂End P η ∘ₗ π₁End P η = 0 := by
  change coefficientEndBaseChange (ι := Unit) q P η = 0 at hηq
  have h1 : coefficientEndBaseChange (ι := Fin 2) q P
      (normalizedEndBaseChange
        (substituteAlgHom (fun _ : Unit => (0 : Fin 2))) P η) = 0 :=
    normalizedEndBaseChange_coefficient_eq_zero
      q P (fun _ : Unit => (0 : Fin 2)) η hηq
  have h2 : coefficientEndBaseChange (ι := Fin 2) q P
      (normalizedEndBaseChange
        (substituteAlgHom (fun _ : Unit => (1 : Fin 2))) P η) = 0 :=
    normalizedEndBaseChange_coefficient_eq_zero
      q P (fun _ : Unit => (1 : Fin 2)) η hηq
  change normalizedEndBaseChange
      (substituteAlgHom (fun _ : Unit => (1 : Fin 2))) P η ∘ₗ
    normalizedEndBaseChange
      (substituteAlgHom (fun _ : Unit => (0 : Fin 2))) P η = 0
  exact comp_eq_zero_of_coefficientEndBaseChange_eq_zero
    q hq hq_sq P _ _ h2 h1

private noncomputable def correctingLinearEquiv
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (η : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M))
    (hη : η ∘ₗ η = 0) :
    (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M) ≃ₗ[
      NovikovSeries (⊤ : AddSubgroup ℝ) Unit A]
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M) := by
  apply LinearEquiv.ofLinear (LinearMap.id + η) (LinearMap.id - η)
  · rw [LinearMap.add_comp, LinearMap.comp_sub, LinearMap.comp_sub]
    simp only [LinearMap.id_comp, LinearMap.comp_id, hη]
    abel
  · rw [LinearMap.sub_comp, LinearMap.comp_add, LinearMap.comp_add]
    simp only [LinearMap.id_comp, LinearMap.comp_id, hη]
    abel

private theorem correctingLinearEquiv_toLinearMap
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (η : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M))
    (hη : η ∘ₗ η = 0) :
    (correctingLinearEquiv P η hη).toLinearMap = LinearMap.id + η := rfl

private theorem correctingLinearEquiv_symm_toLinearMap
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A)
    (η : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M))
    (hη : η ∘ₗ η = 0) :
    (correctingLinearEquiv P η hη).symm.toLinearMap = LinearMap.id - η := rfl

private theorem normalized_gauge_identity
    {A : Type u} [CommRing A]
    (P : FiniteProjectiveModule A)
    (ψ : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A ⊗[A] P.M))
    (η : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M))
    (hδ : ψ - LinearMap.id = π₁End P η - π₂End P η)
    (hcomp : π₂End P η ∘ₗ π₁End P η = 0) :
    ψ = π₂End P (LinearMap.id - η) ∘ₗ
      π₁End P (LinearMap.id + η) := by
  rw [map_sub, map_add]
  rw [show π₁End P LinearMap.id = LinearMap.id from map_one (π₁End P)]
  rw [show π₂End P LinearMap.id = LinearMap.id from map_one (π₂End P)]
  rw [LinearMap.sub_comp]
  rw [LinearMap.comp_add, LinearMap.comp_add]
  simp only [LinearMap.id_comp, LinearMap.comp_id]
  rw [hcomp, add_zero]
  calc
    ψ = LinearMap.id + (ψ - LinearMap.id) := by abel
    _ = LinearMap.id + (π₁End P η - π₂End P η) := by rw [hδ]
    _ = LinearMap.id + π₁End P η - π₂End P η := by abel

private theorem normalized_gauge_morphism_identity
    {A : Type u} [CommRing A]
    (P : FiniteProjectiveModule A)
    (ψ : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A)
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) A ⊗[A] P.M))
    (ξ : (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M) ≃ₗ[NovikovSeries
      (⊤ : AddSubgroup ℝ) Unit A]
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M))
    (hψ : ψ = π₂End P ξ.symm.toLinearMap ∘ₗ
      π₁End P ξ.toLinearMap) :
    π₁End P ξ.toLinearMap =
      π₂End P ξ.toLinearMap ∘ₗ ψ := by
  have hcancel :
      π₂End P ξ.toLinearMap ∘ₗ π₂End P ξ.symm.toLinearMap =
        LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, Module.End.mul_eq_comp,
      ξ.comp_symm]
    exact map_one (π₂End P)
  rw [hψ, ← LinearMap.comp_assoc, hcancel, LinearMap.id_comp]

private noncomputable def correctingDescentHom
    {A : Type u} [CommRing A]
    (P : FiniteProjectiveModule.{u, u} A)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (θ : M.M ≃ₗ[(realC A).R₁]
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M)
    (ξ : (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M) ≃ₗ[NovikovSeries
      (⊤ : AddSubgroup ℝ) Unit A]
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M))
    (hψ : normalizedPhi P (M.transport θ).φ =
      π₂End P ξ.symm.toLinearMap ∘ₗ π₁End P ξ.toLinearMap) :
    M.transport θ ⟶
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  let kAdd : AddCommGroup K.M := K.instAddCommGroup
  let kMod : Module R K.M := K.instModule
  letI : AddCommGroup K.M := kAdd
  letI : Module R K.M := kMod
  let b := realConstantModuleEquiv P
  let ξK := b.trans (ξ.trans b.symm)
  let a1 := realConstantPullbackπ₁Equiv P
  let a2 := realConstantPullbackπ₂Equiv P
  let p1 := K.transportπ₁Equiv ξK
  let p2 := K.transportπ₂Equiv ξK
  let ψ := normalizedPhi P (M.transport θ).φ
  have hnorm : π₁End P ξ.toLinearMap =
      π₂End P ξ.toLinearMap ∘ₗ ψ :=
    normalized_gauge_morphism_identity P ψ ξ hψ
  have h1 := π₁End_eq_conj P ξ
  change π₁End P ξ.toLinearMap =
    a1.toLinearMap ∘ₗ p1.toLinearMap ∘ₗ a1.symm.toLinearMap at h1
  have h2 := π₂End_eq_conj P ξ
  change π₂End P ξ.toLinearMap =
    a2.toLinearMap ∘ₗ p2.toLinearMap ∘ₗ a2.symm.toLinearMap at h2
  have hK := normalizedPhi_constant P
  change a2.toLinearMap ∘ₗ K.φ.toLinearMap ∘ₗ a1.symm.toLinearMap =
    LinearMap.id at hK
  refine
    { toLinearMap := ξK.toLinearMap
      commute_φ := ?_ }
  change K.φ.toLinearMap ∘ₗ p1.toLinearMap =
    p2.toLinearMap ∘ₗ (M.transport θ).φ.toLinearMap
  apply LinearMap.ext
  intro x
  apply a2.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hKx : a2 (K.φ (p1 x)) = a1 (p1 x) := by
    have hx := LinearMap.congr_fun hK (a1 (p1 x))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.id_apply] at hx
    calc
      a2 (K.φ (p1 x)) =
          a2 (K.φ (a1.symm (a1 (p1 x)))) := by
        rw [a1.symm_apply_apply]
      _ = a1 (p1 x) := hx
  have h1x : π₁End P ξ.toLinearMap (a1 x) = a1 (p1 x) := by
    have hx := LinearMap.congr_fun h1 (a1 x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
    calc
      π₁End P ξ.toLinearMap (a1 x) =
          a1 (p1 (a1.symm (a1 x))) := hx
      _ = a1 (p1 x) := by rw [a1.symm_apply_apply]
  have hψx : ψ (a1 x) = a2 ((M.transport θ).φ x) := by
    change a2 ((M.transport θ).φ (a1.symm (a1 x))) =
      a2 ((M.transport θ).φ x)
    rw [a1.symm_apply_apply]
  have h2x : π₂End P ξ.toLinearMap
      (a2 ((M.transport θ).φ x)) =
        a2 (p2 ((M.transport θ).φ x)) := by
    have hx := LinearMap.congr_fun h2 (a2 ((M.transport θ).φ x))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
    calc
      π₂End P ξ.toLinearMap (a2 ((M.transport θ).φ x)) =
          a2 (p2 (a2.symm (a2 ((M.transport θ).φ x)))) := hx
      _ = a2 (p2 ((M.transport θ).φ x)) := by
        rw [a2.symm_apply_apply]
  calc
    a2 (K.φ (p1 x)) = a1 (p1 x) := hKx
    _ = π₁End P ξ.toLinearMap (a1 x) := h1x.symm
    _ = π₂End P ξ.toLinearMap (ψ (a1 x)) := by
      exact LinearMap.congr_fun hnorm (a1 x)
    _ = π₂End P ξ.toLinearMap (a2 ((M.transport θ).φ x)) := by
      rw [hψx]
    _ = a2 (p2 ((M.transport θ).φ x)) := h2x

private noncomputable def correctingDescentIso
    {A : Type u} [CommRing A]
    (P : FiniteProjectiveModule.{u, u} A)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (θ : M.M ≃ₗ[(realC A).R₁]
      ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P).M)
    (ξ : (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M) ≃ₗ[NovikovSeries
      (⊤ : AddSubgroup ℝ) Unit A]
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit A ⊗[A] P.M))
    (hψ : normalizedPhi P (M.transport θ).φ =
      π₂End P ξ.symm.toLinearMap ∘ₗ π₁End P ξ.toLinearMap) :
    M.transport θ ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) Unit A
  let K := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
  let kAdd : AddCommGroup K.M := K.instAddCommGroup
  let kMod : Module R K.M := K.instModule
  letI : AddCommGroup K.M := kAdd
  letI : Module R K.M := kMod
  let b := realConstantModuleEquiv P
  let ξK := b.trans (ξ.trans b.symm)
  let f := correctingDescentHom P M θ ξ hψ
  exact Abstract.DescentDatum.isoOfLinearEquiv f ξK rfl

attribute [local irreducible]
  correctingLinearEquiv
  correctingDescentIso

/-- Real Novikov descent data that become constant after a surjective
square-zero coefficient map are already constant. -/
theorem novikovDescent_squareZero_of_surjective
    (A B : Type u) [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (hM : ∃ Q : FiniteProjectiveModule.{u, u} B,
      Nonempty
        ((vectToNovikovDescent.{0, u, u}
            (⊤ : AddSubgroup ℝ) B).obj Q ≅
          M.baseChange (realCCoeffHom q))) :
    ∃ P : FiniteProjectiveModule.{u, u} A,
      Nonempty
        (((vectToNovikovDescent.{0, u, u}
            (⊤ : AddSubgroup ℝ) A).obj P) ≅ M) := by
  obtain ⟨P, ⟨eRed⟩⟩ :=
    exists_lifted_constant_reduction A B q hq hq_sq M hM
  obtain ⟨θ, hθ, ⟨θIso⟩⟩ :=
    exists_underlying_linearEquiv_lift A B q hq hq_sq M P eRed
  obtain ⟨η, hδ, hηq⟩ :=
    exists_normalizedPhi_correcting_end
      q hq hq_sq P M θ eRed hθ
  have hη : η ∘ₗ η = 0 :=
    correcting_end_sq_zero q hq hq_sq P η hηq
  let ξ := correctingLinearEquiv P η hη
  have hcomp : π₂End P η ∘ₗ π₁End P η = 0 :=
    correcting_faces_comp_eq_zero q hq hq_sq P η hηq
  have hψ0 := normalized_gauge_identity P
    (normalizedPhi P (M.transport θ).φ) η hδ hcomp
  have hψ : normalizedPhi P (M.transport θ).φ =
      π₂End P ξ.symm.toLinearMap ∘ₗ π₁End P ξ.toLinearMap := by
    simpa only [ξ, correctingLinearEquiv_toLinearMap,
      correctingLinearEquiv_symm_toLinearMap] using hψ0
  let ξIso := correctingDescentIso P M θ ξ hψ
  exact ⟨P, ⟨(θIso ≪≫ ξIso).symm⟩⟩

/-- Real Novikov descent data that become constant modulo a square-zero ideal
are already constant. -/
theorem novikovDescent_squareZero
    (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I ^ 2 = ⊥)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (hM : ∃ Q : FiniteProjectiveModule.{u, u} (A ⧸ I),
      Nonempty
        ((vectToNovikovDescent.{0, u, u}
            (⊤ : AddSubgroup ℝ) (A ⧸ I)).obj Q ≅
          M.baseChange
            (realCCoeffHom (Ideal.Quotient.mk I)))) :
    ∃ P : FiniteProjectiveModule.{u, u} A,
      Nonempty
        (((vectToNovikovDescent.{0, u, u}
            (⊤ : AddSubgroup ℝ) A).obj P) ≅ M) := by
  let q := Ideal.Quotient.mk I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hq_sq : RingHom.ker q ^ 2 = ⊥ := by
    simpa only [q, Ideal.mk_ker] using hI
  exact novikovDescent_squareZero_of_surjective A (A ⧸ I)
    q hq hq_sq M hM

end Novikov.Descent
