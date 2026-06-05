import Novikov.Descent.Product.Inverse

/-!
# Product of algebraically closed fields

This file packages the product-field descent construction into the final
categorical equivalence: if `A = ∀ i, K i` is a product of algebraically closed
fields, then constant real Novikov descent over `A` is an equivalence.
-/

open CategoryTheory Novikov.Miscellany Novikov.Descent.Abstract

namespace Novikov.Descent

noncomputable section

universe u

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)] [∀ i, IsAlgClosed (K i)]

/-- For a product of algebraically closed fields, constant real Novikov descent
is an equivalence. -/
theorem vectToNovikovDescent_isEquivalence_prod_algClosed :
    (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).IsEquivalence := by
  let F := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)
  have hFF : F.FullyFaithful := vectToNovikovDescent_fullyFaithful (⊤ : AddSubgroup ℝ) (∀ i, K i)
  letI : F.Faithful := hFF.faithful
  letI : F.Full := hFF.full
  letI : F.EssSurj := by
    constructor
    intro M
    refine ⟨productConstModule K M, ⟨?_⟩⟩
    exact (toConstantIso K M).symm
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The bundled equivalence for constant real Novikov descent over a product of
algebraically closed fields. -/
noncomputable def vectToNovikovDescent_equivalence_prod_algClosed :
    FiniteProjectiveModule.{u, u} (∀ i, K i) ≌
      NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i) := by
  let F := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)
  haveI : F.IsEquivalence := vectToNovikovDescent_isEquivalence_prod_algClosed K
  exact F.asEquivalence

end

end Novikov.Descent
