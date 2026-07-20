import Novikov.Descent.CoefficientBaseChange
import Novikov.Descent.ProdAlgClosed
import Novikov.Isocrystal.Injective
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Real Novikov descent over reduced rings

A reduced ring embeds in the product of algebraic closures of the fraction
fields of its prime quotients. After extending coefficients along this map,
product-field descent makes every descent datum constant. Isocrystal
base-change compatibility and injectivity then descend constancy to the
original ring.
-/

noncomputable section

universe u

open CategoryTheory Novikov Novikov.Descent.Abstract Novikov.Miscellany

namespace Novikov.Descent

/-- An algebraic closure of the fraction field of the residue domain at a
prime ideal. -/
abbrev algClosedResidueField (A : Type u) [CommRing A]
    (p : PrimeSpectrum A) : Type u :=
  AlgebraicClosure p.asIdeal.ResidueField

/-- The canonical map from a ring to the product of its algebraically closed
residue fields. -/
noncomputable def reducedEmbedding (A : Type u) [CommRing A] :
    A →+* (∀ p : PrimeSpectrum A, algClosedResidueField A p) :=
  Pi.ringHom fun p =>
    (algebraMap p.asIdeal.ResidueField (algClosedResidueField A p)).comp
      (algebraMap A p.asIdeal.ResidueField)

/-- The canonical product map `reducedEmbedding` is injective for a reduced
ring. -/
lemma reducedEmbedding_injective (A : Type u) [CommRing A] [IsReduced A] :
    Function.Injective (reducedEmbedding A) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_bot]
    apply (nilradical_eq_zero A) ▸ (show x ∈ nilradical A from ?_)
    rw [PrimeSpectrum.nilradical_eq_iInf]
    rw [Ideal.mem_iInf]
    intro p
    rw [← Ideal.algebraMap_residueField_eq_zero]
    apply (algebraMap p.asIdeal.ResidueField
      (algClosedResidueField A p)).injective
    rw [map_zero]
    exact congrFun hx p
  · exact bot_le

/-- Over a reduced ring, the isocrystal attached to any real Novikov descent
datum is constant. -/
theorem descentToIsocrystal_obj_is_const_of_reduced
    {Λ : ℝ} [Fact (Λ > 1)]
    (A : Type u) [CommRing A] [IsReduced A]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A) :
    ∃ P : FiniteProjectiveModule.{u, u} A,
      Nonempty
        ((descentToIsocrystal.{u, u} (Λ := Λ) A).obj M ≅
          (NovikovIsocrystal.vectToNovIsoc.{u, u}
            (Λ := Λ) (A := A)).obj P) := by
  let K : PrimeSpectrum A → Type u := fun p => algClosedResidueField A p
  let B : Type u := ∀ p : PrimeSpectrum A, K p
  let f : A →+* B := reducedEmbedding A
  let F_B := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) B
  let M_B := M.baseChange (realCCoeffHom f)
  haveI : F_B.IsEquivalence :=
    vectToNovikovDescent_isEquivalence_prod_algClosed K
  let P_B : FiniteProjectiveModule.{u, u} B := F_B.objPreimage M_B
  let ε_B : F_B.obj P_B ≅ M_B := F_B.objObjPreimageIso M_B
  let D_A := descentToIsocrystal.{u, u} (Λ := Λ) A
  let D_B := descentToIsocrystal.{u, u} (Λ := Λ) B
  let α_B := descentToIsocrystal_comp_vectToNovikovDescent_iso.{u, u}
    (Λ := Λ) (A := B)
  let β := descentToIsocrystal_baseChangeIso (Λ := Λ) f M
  let iso_over_B : Novikov.baseChange f (D_A.obj M) ≅
      (NovikovIsocrystal.vectToNovIsoc.{u, u}
        (Λ := Λ) (A := B)).obj P_B :=
    β ≪≫ D_B.mapIso ε_B.symm ≪≫ α_B.app P_B
  exact Novikov.nov_isoc_injective (Λ := Λ) f
    (reducedEmbedding_injective A) (D_A.obj M) P_B iso_over_B

/-- Constant real Novikov descent over a reduced ring is an equivalence. -/
theorem vectToNovikovDescent_isEquivalence_reduced
    (A : Type u) [CommRing A] [IsReduced A] :
    (vectToNovikovDescent.{0, u, u}
      (⊤ : AddSubgroup ℝ) A).IsEquivalence := by
  letI : Fact ((2 : ℝ) > 1) := ⟨by norm_num⟩
  let F := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) A
  have hFF : F.FullyFaithful :=
    vectToNovikovDescent_fullyFaithful (⊤ : AddSubgroup ℝ) A
  letI : F.Faithful := hFF.faithful
  letI : F.Full := hFF.full
  letI : F.EssSurj := by
    constructor
    intro M
    obtain ⟨P, ⟨e⟩⟩ :=
      descentToIsocrystal_obj_is_const_of_reduced (Λ := (2 : ℝ)) A M
    refine ⟨P, ⟨?_⟩⟩
    let α := descentToIsocrystal_comp_vectToNovikovDescent_iso.{u, u}
      (Λ := (2 : ℝ)) (A := A)
    exact (descentToIsocrystal_fullyFaithful.{u, u}
      (Λ := (2 : ℝ)) (A := A)).preimageIso ((α.app P).trans e.symm)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The bundled equivalence for constant real Novikov descent over a reduced
ring. -/
noncomputable def vectToNovikovDescent_equivalence_reduced
    (A : Type u) [CommRing A] [IsReduced A] :
    FiniteProjectiveModule.{u, u} A ≌
      NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A := by
  let F := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) A
  haveI : F.IsEquivalence :=
    vectToNovikovDescent_isEquivalence_reduced A
  exact F.asEquivalence

end Novikov.Descent
