import Novikov.Descent.Exponent.Dual

/-!
# Novikov descent for arbitrary exponent monoids

The real-exponent descent theorem and exponent-restriction duality imply that
constant Novikov descent is an equivalence for every additive submonoid of
`ℝ`.
-/

open CategoryTheory Novikov.Miscellany Novikov.Descent.Abstract

namespace Novikov.Descent

noncomputable section

universe u v

variable {S : Type v} [SetLike S ℝ] [AddSubmonoidClass S ℝ]

/-- Constant Novikov descent for an arbitrary exponent monoid is essentially
surjective. -/
theorem vectToNovikovDescent_essSurj
    (Γ : S) (A : Type u) [CommRing A] :
    (vectToNovikovDescent.{v, u, u} Γ A).EssSurj := by
  let FReal := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) A
  haveI : FReal.IsEquivalence := vectToNovikovDescent_isEquivalence_real A
  constructor
  intro M
  let MReal := M.baseChange (exponentInclusionCHom Γ A)
  let P : FiniteProjectiveModule.{u, u} A := FReal.objPreimage MReal
  let e : MReal ≅ FReal.obj P := (FReal.objObjPreimageIso MReal).symm
  exact ⟨P, ⟨(restrictRealTrivializationIso Γ M P e).symm⟩⟩

/-- Constant Novikov descent is an equivalence for every additive exponent
submonoid of `ℝ` and every commutative coefficient ring. -/
theorem vectToNovikovDescent_isEquivalence
    (Γ : S) (A : Type u) [CommRing A] :
    (vectToNovikovDescent.{v, u, u} Γ A).IsEquivalence := by
  let F := vectToNovikovDescent.{v, u, u} Γ A
  have hFF : F.FullyFaithful := vectToNovikovDescent_fullyFaithful Γ A
  letI : F.Faithful := hFF.faithful
  letI : F.Full := hFF.full
  letI : F.EssSurj := vectToNovikovDescent_essSurj Γ A
  change F.IsEquivalence
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The bundled equivalence between finite-projective modules and Novikov
descent data for an arbitrary additive exponent submonoid of `ℝ`. -/
noncomputable def vectToNovikovDescent_equivalence
    (Γ : S) (A : Type u) [CommRing A] :
    FiniteProjectiveModule.{u, u} A ≌
      NovikovDescentDatum.{v, u, u} Γ A := by
  let F := vectToNovikovDescent.{v, u, u} Γ A
  haveI : F.IsEquivalence := vectToNovikovDescent_isEquivalence Γ A
  exact F.asEquivalence

end

end Novikov.Descent
