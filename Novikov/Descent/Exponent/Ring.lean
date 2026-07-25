import Novikov.Descent.Basic
import Novikov.Descent.Abstract.ConstantBaseChange
import Novikov.Series.Exponent

/-!
# Inclusion of Novikov exponent rings

This file packages extension by zero from exponents in an additive submonoid
`Γ ⊆ ℝ` to arbitrary real exponents as a homomorphism of the Novikov
cosimplicial rings.  It also defines the resulting base-change functor on
descent data.
-/

namespace Novikov.Descent

open CategoryTheory Novikov TensorProduct
open Novikov.Descent.Abstract Novikov.Miscellany

variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ]
variable (Γ : S)

/-- Extension by zero commutes with substitution along an injective variable
map. -/
lemma extendExponents_substitute_of_injective {ι ι' M : Type*}
    [Fintype ι] [Fintype ι'] [AddCommGroup M]
    (φ : ι → ι') (hφ : Function.Injective φ)
    (f : NovikovSeries Γ ι M) :
    extendExponents Γ (substitute φ f) =
      substitute φ (extendExponents Γ f) := by
  classical
  ext d
  by_cases hmem : ∀ j, (d j : ℝ) ∈ Γ
  · let dΓ : ι' → Γ := fun j => ⟨(d j : ℝ), hmem j⟩
    have hd : includeExponent Γ dΓ = d := by
      funext j
      rfl
    rw [← hd, extendExponents_apply_include]
    rw [substitute_apply_of_injective hφ, substitute_apply_of_injective hφ]
    have hcond :
        (∀ j, (∀ i, φ i ≠ j) → dΓ j = 0) ↔
          ∀ j, (∀ i, φ i ≠ j) → includeExponent Γ dΓ j = 0 := by
      constructor
      · intro h j hj
        change realExponentInclusion Γ (dΓ j) = 0
        rw [h j hj, map_zero]
      · intro h j hj
        exact Subtype.ext
          (congrArg (fun z : (⊤ : AddSubgroup ℝ) => (z : ℝ)) (h j hj))
    by_cases hzero : ∀ j, (∀ i, φ i ≠ j) → dΓ j = 0
    · rw [if_pos hzero, if_pos (hcond.mp hzero)]
      have harg : (fun i => includeExponent Γ dΓ (φ i)) =
          includeExponent Γ (fun i => dΓ (φ i)) := rfl
      rw [harg, extendExponents_apply_include]
    · rw [if_neg hzero, if_neg (fun h => hzero (hcond.mpr h))]
  · rw [extendExponents_apply_of_not_mem Γ _ d hmem]
    rw [substitute_apply_of_injective hφ]
    by_cases hzero : ∀ j, (∀ i, φ i ≠ j) → d j = 0
    · rw [if_pos hzero]
      symm
      apply extendExponents_apply_of_not_mem Γ
      intro hpull
      apply hmem
      intro j
      by_cases hj : ∃ i, φ i = j
      · obtain ⟨i, rfl⟩ := hj
        exact hpull i
      · have hj' : ∀ i, φ i ≠ j := by
          intro i hij
          exact hj ⟨i, hij⟩
        rw [hzero j hj']
        exact zero_mem Γ
    · rw [if_neg hzero]

/-- The inclusion of `Γ`-exponent Novikov rings into real-exponent Novikov
rings as a homomorphism of cosimplicial rings. -/
noncomputable def exponentInclusionCHom (A : Type*) [CommRing A] :
    CosimplicialRingHom (novikovCosimplicialRing Γ A)
      (novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A) where
  f₁ := extendExponentsRingHom Γ
  f₂ := extendExponentsRingHom Γ
  f₃ := extendExponentsRingHom Γ
  comm_π₁ := by
    ext f
    exact extendExponents_substitute_of_injective Γ _
      (fun x y _ => by cases x; cases y; rfl) f
  comm_π₂ := by
    ext f
    exact extendExponents_substitute_of_injective Γ _
      (fun x y _ => by cases x; cases y; rfl) f
  comm_π₁₂ := by
    ext f
    exact extendExponents_substitute_of_injective Γ _
      (Fin.castSucc_injective 2) f
  comm_π₁₃ := by
    ext f
    exact extendExponents_substitute_of_injective Γ _
      Fin.succAbove_right_injective f
  comm_π₂₃ := by
    ext f
    exact extendExponents_substitute_of_injective Γ _
      (fun _ _ h => Fin.succ_injective _ h) f

@[simp]
lemma exponentInclusionCHom_f₁_apply (A : Type*) [CommRing A]
    (f : (novikovCosimplicialRing Γ A).R₁) :
    (exponentInclusionCHom Γ A).f₁ f = extendExponents Γ f := rfl

@[simp]
lemma exponentInclusionCHom_f₂_apply (A : Type*) [CommRing A]
    (f : (novikovCosimplicialRing Γ A).R₂) :
    (exponentInclusionCHom Γ A).f₂ f = extendExponents Γ f := rfl

@[simp]
lemma exponentInclusionCHom_f₃_apply (A : Type*) [CommRing A]
    (f : (novikovCosimplicialRing Γ A).R₃) :
    (exponentInclusionCHom Γ A).f₃ f = extendExponents Γ f := rfl

lemma exponentInclusionCHom_f₁_injective (A : Type*) [CommRing A] :
    Function.Injective (exponentInclusionCHom Γ A).f₁ :=
  extendExponentsRingHom_injective Γ

lemma exponentInclusionCHom_f₂_injective (A : Type*) [CommRing A] :
    Function.Injective (exponentInclusionCHom Γ A).f₂ :=
  extendExponentsRingHom_injective Γ

lemma exponentInclusionCHom_f₃_injective (A : Type*) [CommRing A] :
    Function.Injective (exponentInclusionCHom Γ A).f₃ :=
  extendExponentsRingHom_injective Γ

/-- The exponent inclusion as a homomorphism of extended cosimplicial rings;
its level-zero map is the identity on coefficients. -/
noncomputable def exponentInclusionExtendedCHom (A : Type*) [CommRing A] :
    ExtendedCosimplicialRingHom (novikovExtendedCosimplicialRing Γ A)
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A) where
  toCosimplicialRingHom := exponentInclusionCHom Γ A
  f₀ := RingHom.id A
  comm_π₀ := by
    ext a
    exact extendExponents_algebraMapNovikov Γ a

/-- Base change of Novikov descent data from exponents in `Γ` to arbitrary real
exponents. -/
noncomputable def exponentBaseChangeFunctor (A : Type*) [CommRing A] :
    NovikovDescentDatum Γ A ⥤
      NovikovDescentDatum (⊤ : AddSubgroup ℝ) A :=
  baseChangeFunctor (exponentInclusionCHom Γ A)

private noncomputable def finiteProjectiveModuleBaseChangeIdIso
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A) :
    P.baseChange (RingHom.id A) ≅ P := by
  let e : (P.baseChange (RingHom.id A)).M ≃ₗ[A] P.M := by
    change (A ⊗[A] P.M) ≃ₗ[A] P.M
    exact TensorProduct.lid A P.M
  exact
    { hom := e.toLinearMap
      inv := e.symm.toLinearMap
      hom_inv_id := by
        apply LinearMap.ext
        intro x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply LinearMap.ext
        intro x
        exact e.apply_symm_apply x }

@[simp]
private lemma finiteProjectiveModuleBaseChangeIdIso_hom_tmul
    {A : Type*} [CommRing A] (P : FiniteProjectiveModule A) (p : P.M) :
    (finiteProjectiveModuleBaseChangeIdIso P).hom.toFun
      ((1 : A) ⊗ₜ[A] p) = p := by
  change (TensorProduct.lid A P.M) (1 ⊗ₜ[A] p) = p
  simp

/-- Base-changing a constant `Γ`-exponent descent datum to real exponents
recovers the corresponding constant real-exponent descent datum. -/
noncomputable def exponentConstantBaseChangeIso
    (A : Type*) [CommRing A] (P : FiniteProjectiveModule A) :
    ((vectToNovikovDescent Γ A).obj P).baseChange
        (exponentInclusionCHom Γ A) ≅
      (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P := by
  let F := exponentInclusionExtendedCHom Γ A
  exact (constantDescentDatum_baseChangeIso F P).trans
    ((constantDescentDatumFunctor
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A)).mapIso
        (finiteProjectiveModuleBaseChangeIdIso P))

@[simp]
lemma exponentConstantBaseChangeIso_hom_tmul
    (A : Type*) [CommRing A] (P : FiniteProjectiveModule A)
    (s : NovikovSeries (⊤ : AddSubgroup ℝ) Unit A)
    (t : NovikovSeries Γ Unit A) (p : P.M) :
    (exponentConstantBaseChangeIso Γ A P).hom.toLinearMap
        (by
          let E := novikovExtendedCosimplicialRing Γ A
          let D := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A
          let F := exponentInclusionExtendedCHom Γ A
          letI : Module E.R₀ P.M := by
            change Module A P.M
            infer_instance
          letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
          letI : Algebra E.R₁ D.R₁ := F.f₁.toAlgebra
          change D.R₁ ⊗[E.R₁] (E.R₁ ⊗[E.R₀] P.M)
          exact s ⊗ₜ[E.R₁] (t ⊗ₜ[E.R₀] p)) =
      (by
        let D := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A
        letI : Module D.R₀ P.M := by
          change Module A P.M
          infer_instance
        letI : Algebra D.R₀ D.R₁ := D.π₀.toAlgebra
        change D.R₁ ⊗[D.R₀] P.M
        exact (extendExponents Γ t * s) ⊗ₜ[D.R₀] p) := by
  dsimp only [exponentConstantBaseChangeIso]
  simp only [Iso.trans_hom]
  let D := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A
  letI : Algebra D.R₀ D.R₁ := D.π₀.toAlgebra
  letI : Algebra A D.R₁ := by
    change Algebra D.R₀ D.R₁
    infer_instance
  change (LinearMap.baseChange D.R₁
      (finiteProjectiveModuleBaseChangeIdIso P).hom)
    ((constantDescentDatumBaseChangeEquiv
      (exponentInclusionExtendedCHom Γ A) P) _) = _
  dsimp only [id_eq]
  have hbase := constantDescentDatumBaseChangeEquiv_tmul
    (exponentInclusionExtendedCHom Γ A) P s t p
  erw [hbase]
  erw [LinearMap.baseChange_tmul]
  congr 1
  exact finiteProjectiveModuleBaseChangeIdIso_hom_tmul P p

end Novikov.Descent
