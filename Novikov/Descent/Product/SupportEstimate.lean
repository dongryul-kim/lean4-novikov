import Novikov.Descent.Product.FiberCoordinateTransitions
import Mathlib.Tactic.Linarith

/-!
# Fiber-coordinate support estimates for product-field descent

This file applies the fiber-coordinate transition identities to bound the
supports of the trivialized coordinates and prove that their family lies in the
coefficientwise range.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract
open scoped BigOperators

namespace Novikov.Descent

noncomputable section

universe u v

variable {S : Type*} [SetLike S ℝ] {Γ : S}

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)] [∀ i, IsAlgClosed (K i)]

/-- Fiberwise support of a transition coefficient, as a subset of `ℝ × ℝ`. -/
private def generatorTransitionCoeffFiberSupportReal
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j k : Fin (productFiberRankBoundN K M)) : Set (ℝ × ℝ) :=
  {p | ∃ d : Fin 2 → (⊤ : AddSubgroup ℝ),
    (coeffwiseEvalRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
      (generatorTransitionCoeff K M j k)).val d ≠ 0 ∧
    p = ((d 0 : ℝ), (d 1 : ℝ))}

omit [∀ i, IsAlgClosed (K i)] in
private lemma generatorTransitionCoeffFiberSupportReal_exists_weight_lower_bound
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    ∃ C : ℝ, ∀ (i : I) (j k : Fin (productFiberRankBoundN K M)) (p : ℝ × ℝ),
      p ∈ generatorTransitionCoeffFiberSupportReal K M i j k → C ≤ 2 * p.1 + p.2 := by
  rcases generatorTransitionCoeff_exists_weight_lower_bound K M with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro i j k p hp
  rcases hp with ⟨d, hd_eval, rfl⟩
  have hd_orig : (generatorTransitionCoeff K M j k).val d ≠ 0 := by
    intro hzero
    apply hd_eval
    have hcoeff_i : ((generatorTransitionCoeff K M j k).val d) i = 0 := congrFun hzero i
    simpa [coeffwiseEvalRingHom] using hcoeff_i
  have hCd := hC j k d hd_orig
  rw [Fin.sum_univ_two] at hCd
  norm_num [twoOneWeight] at hCd
  simpa using hCd

/-- Fiberwise support of an inverse transition coefficient, as a subset of `ℝ × ℝ`. -/
private def generatorInverseTransitionCoeffFiberSupportReal
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j k : Fin (productFiberRankBoundN K M)) : Set (ℝ × ℝ) :=
  {p | ∃ d : Fin 2 → (⊤ : AddSubgroup ℝ),
    (coeffwiseEvalRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
      (generatorInverseTransitionCoeff K M j k)).val d ≠ 0 ∧
    p = ((d 0 : ℝ), (d 1 : ℝ))}

omit [∀ i, IsAlgClosed (K i)] in
private lemma generatorInverseTransitionCoeffFiberSupportReal_subset_global
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j k : Fin (productFiberRankBoundN K M)) :
    generatorInverseTransitionCoeffFiberSupportReal K M i j k ⊆
      twoVarSupportRealUnion (fun k' : Fin (productFiberRankBoundN K M) =>
        generatorInverseTransitionCoeff K M j k') := by
  intro p hp
  rcases hp with ⟨d, hd_eval, rfl⟩
  refine ⟨k, d, ?_, rfl⟩
  intro hzero
  apply hd_eval
  have hcoeff_i : ((generatorInverseTransitionCoeff K M j k).val d) i = 0 := congrFun hzero i
  simpa [coeffwiseEvalRingHom] using hcoeff_i

/-- Fiberwise support of a generator coordinate. -/
private def generatorCoordSupportReal
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j c : Fin (productFiberRankBoundN K M)) : Set ℝ :=
  oneVarSupportReal (trivializedCoordFamily K M (productFiberGenerator K M j) c i)

/-- Product-specific lower-bound consequence of the transition-support relation
coming from descent compatibility.  The relation itself is proved later from the
coordinate form of the descent diagram. -/
private lemma generatorCoordSupportReal_exists_lower_bound_of_transition_relation
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hrel : ∀ (i : I) (j c : Fin (productFiberRankBoundN K M)) (x : ℝ),
      x ∈ generatorCoordSupportReal K M i j c →
        ∃ k p y,
          p ∈ generatorTransitionCoeffFiberSupportReal K M i j k ∧
          y ∈ generatorCoordSupportReal K M i k c ∧
          p.1 = x ∧ p.2 + y = 0) :
    ∃ C : ℝ, ∀ (i : I) (j c : Fin (productFiberRankBoundN K M)) (x : ℝ),
      x ∈ generatorCoordSupportReal K M i j c → C ≤ x := by
  rcases generatorTransitionCoeffFiberSupportReal_exists_weight_lower_bound K M with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  let J := Fin (productFiberRankBoundN K M) × Fin (productFiberRankBoundN K M)
  let g : ∀ i : I, J → NovikovSeries (⊤ : AddSubgroup ℝ) Unit (K i) := fun i jc =>
    trivializedCoordFamily K M (productFiberGenerator K M jc.1) jc.2 i
  let T : I → J → J → Set (ℝ × ℝ) := fun i jc kc =>
    {p | p ∈ generatorTransitionCoeffFiberSupportReal K M i jc.1 kc.1 ∧ kc.2 = jc.2}
  have hT : ∀ i (jc kc : J) p, p ∈ T i jc kc → C ≤ 2 * p.1 + p.2 := by
    intro i jc kc p hp
    exact hC i jc.1 kc.1 p hp.1
  have hrel' : ∀ i (jc : J) x, x ∈ oneVarSupportReal (g i jc) →
      ∃ kc p y, p ∈ T i jc kc ∧ y ∈ oneVarSupportReal (g i kc) ∧ p.1 = x ∧ p.2 + y = 0 := by
    intro i jc x hx
    rcases hrel i jc.1 jc.2 x hx with ⟨k, p, y, hp, hy, hp1, hp2⟩
    refine ⟨(k, jc.2), p, y, ?_, hy, hp1, hp2⟩
    exact ⟨hp, rfl⟩
  have hbound := lower_bound_of_series_transition_relation (Γ := (⊤ : AddSubgroup ℝ))
    g T C hT hrel'
  intro i j c x hx
  exact hbound i (j, c) x hx

/-- The inverse transition-support relation plus the generator lower bound gives
finite-below support for each generator coordinate. -/
private lemma generatorCoordSupportReal_finite_le_of_inverse_transition_relation
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hbound : ∃ D : ℝ, ∀ (i : I) (j c : Fin (productFiberRankBoundN K M)) (x : ℝ),
      x ∈ generatorCoordSupportReal K M i j c → D ≤ x)
    (hinv : ∀ (i : I) (j c : Fin (productFiberRankBoundN K M)) (y : ℝ),
      y ∈ generatorCoordSupportReal K M i j c →
        ∃ k p x,
          p ∈ generatorInverseTransitionCoeffFiberSupportReal K M i j k ∧
          x ∈ generatorCoordSupportReal K M i k c ∧
          p.1 + x = 0 ∧ p.2 = y) :
    ∀ (j c : Fin (productFiberRankBoundN K M)) (C : ℝ),
      {d ∈ coeffwiseSupportUnion K (trivializedCoordFamily K M (productFiberGenerator K M j) c) |
        (d () : ℝ) ≤ C}.Finite := by
  rcases hbound with ⟨D, hD⟩
  intro j c C
  let a : Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₂ := fun k =>
    generatorInverseTransitionCoeff K M j k
  let Y : Set ℝ := {y | ∃ p x,
        p ∈ twoVarSupportRealUnion a ∧ D ≤ x ∧ y = p.2 ∧ p.1 + x + p.2 ≤ C}
  have hY : Y.Finite := twoVarSupportRealUnion_y_finite_of_lower_bound' a D C
  refine Set.Finite.subset (unitExponentReal_preimage_finite (Γ := (⊤ : AddSubgroup ℝ)) Y hY) ?_
  intro d hd
  rcases hd with ⟨hdSupp, hdle⟩
  rcases hdSupp with ⟨i, hdi⟩
  have hy_mem : (d () : ℝ) ∈ generatorCoordSupportReal K M i j c := by
    exact ⟨d, hdi, rfl⟩
  rcases hinv i j c (d () : ℝ) hy_mem with ⟨k, p, x, hp, hx, hpx, hpy⟩
  change (d () : ℝ) ∈ Y
  refine ⟨p, x, ?_, hD i k c x hx, ?_, ?_⟩
  · exact generatorInverseTransitionCoeffFiberSupportReal_subset_global K M i j k hp
  · exact hpy.symm
  · linarith

/-- The assertion that all finite-free coordinates of all trivialized elements
come from product-coefficient Novikov series. -/
def TrivializedCoordinatesInCoeffwiseRange
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) : Prop :=
  ∀ (m : M.M) (c : Fin (productFiberRankBoundN K M)),
    InCoeffwiseRange K (trivializedCoordFamily K M m c)

/-- The assertion that the chosen generators have coefficientwise-range
trivialized coordinates. -/
private def GeneratorTrivializedCoordinatesInCoeffwiseRange
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) : Prop :=
  ∀ (j : Fin (productFiberRankBoundN K M)) (c : Fin (productFiberRankBoundN K M)),
    InCoeffwiseRange K (trivializedCoordFamily K M (productFiberGenerator K M j) c)

/-- The forward and inverse transition-support relations imply that the chosen
generators have coefficientwise-range trivialized coordinates. -/
private lemma generatorTrivializedCoordinatesInCoeffwiseRange_of_transition_relations
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hforward : ∀ (i : I) (j c : Fin (productFiberRankBoundN K M)) (x : ℝ),
      x ∈ generatorCoordSupportReal K M i j c →
        ∃ k p y,
          p ∈ generatorTransitionCoeffFiberSupportReal K M i j k ∧
          y ∈ generatorCoordSupportReal K M i k c ∧
          p.1 = x ∧ p.2 + y = 0)
    (hinv : ∀ (i : I) (j c : Fin (productFiberRankBoundN K M)) (y : ℝ),
      y ∈ generatorCoordSupportReal K M i j c →
        ∃ k p x,
          p ∈ generatorInverseTransitionCoeffFiberSupportReal K M i j k ∧
          x ∈ generatorCoordSupportReal K M i k c ∧
          p.1 + x = 0 ∧ p.2 = y) :
    GeneratorTrivializedCoordinatesInCoeffwiseRange K M := by
  have hbound := generatorCoordSupportReal_exists_lower_bound_of_transition_relation K M hforward
  have hfinite := generatorCoordSupportReal_finite_le_of_inverse_transition_relation K M hbound hinv
  intro j c
  exact inCoeffwiseRange_unit_of_finite_le K (hfinite j c)

/-- The coordinate equalities imply that the chosen generators have
coefficientwise-range trivialized coordinates. -/
private lemma generatorTrivializedCoordinatesInCoeffwiseRange_of_coordinate_equalities
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hfwd : GeneratorForwardCoordinateEquality K M)
    (hinv : GeneratorInverseCoordinateEquality K M) :
    GeneratorTrivializedCoordinatesInCoeffwiseRange K M := by
  refine generatorTrivializedCoordinatesInCoeffwiseRange_of_transition_relations K M ?_ ?_
  · intro i j c x hx
    let g : Fin (productFiberRankBoundN K M) → (realC (K i)).R₁ := fun j =>
      trivializedCoordFamily K M (productFiberGenerator K M j) c i
    let a : Fin (productFiberRankBoundN K M) → Fin (productFiberRankBoundN K M) →
        (realC (K i)).R₂ := fun j k =>
      (show (realC (K i)).R₂ from coeffwiseEvalRingHom
        (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i (generatorTransitionCoeff K M j k))
    have hcoord : ∀ j, (realC (K i)).π₁ (g j) = ∑ k, a j k * (realC (K i)).π₂ (g k) := by
      intro j
      exact hfwd i j c
    rcases forward_relation_of_coord_eq g a hcoord j x hx with ⟨k, p, y, hp, hy, hp1, hp2⟩
    exact ⟨k, p, y, hp, hy, hp1, hp2⟩
  · intro i j c y hy
    let g : Fin (productFiberRankBoundN K M) → (realC (K i)).R₁ := fun j =>
      trivializedCoordFamily K M (productFiberGenerator K M j) c i
    let b : Fin (productFiberRankBoundN K M) → Fin (productFiberRankBoundN K M) →
        (realC (K i)).R₂ := fun j k =>
      (show (realC (K i)).R₂ from coeffwiseEvalRingHom
        (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
          (generatorInverseTransitionCoeff K M j k))
    have hcoord : ∀ j, (realC (K i)).π₂ (g j) = ∑ k, b j k * (realC (K i)).π₁ (g k) := by
      intro j
      exact hinv i j c
    rcases inverse_relation_of_coord_eq g b hcoord j y hy with ⟨k, p, x, hp, hx, hp1, hp2⟩
    exact ⟨k, p, x, hp, hx, hp1, hp2⟩

omit [∀ i, IsAlgClosed (K i)] in
/-- Base-changing the chosen presentation equality to `prodRealC K`. -/
private lemma one_tmul_productFiberPresentation_eq_sum_generators
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (v : Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₁) :
    letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ :=
      (coeffwiseRealCHom K).f₁.toAlgebra
    ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁]
        productFiberPresentation K M v : (M.baseChange (coeffwiseRealCHom K)).M) =
      ∑ j : Fin (productFiberRankBoundN K M),
        (coeffwiseRealCHom K).f₁ (v j) •
          ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁]
            productFiberGenerator K M j) := by
  letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ :=
    (coeffwiseRealCHom K).f₁.toAlgebra
  rw [productFiberPresentation_eq_sum_generators]
  rw [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [TensorProduct.tmul_smul]
  change ((v j) • (1 : (prodRealC K).R₁)) ⊗ₜ[(realC (∀ i, K i)).R₁]
      productFiberGenerator K M j =
    (coeffwiseRealCHom K).f₁ (v j) •
      ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁]
        productFiberGenerator K M j)
  rw [TensorProduct.smul_tmul']
  rfl

/-- Coordinates of a presented element are finite sums of scalar multiples of the
coordinates of the chosen generators. -/
private lemma trivializedCoordFamily_presentation
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (v : Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₁)
    (c : Fin (productFiberRankBoundN K M)) :
    trivializedCoordFamily K M (productFiberPresentation K M v) c =
      fun i => ∑ j : Fin (productFiberRankBoundN K M),
        (show (realC (K i)).R₁ from coeffwiseEvalRingHom K i (v j)) •
          (show (realC (K i)).R₁ from trivializedCoordFamily K M
            (productFiberGenerator K M j) c i) := by
  letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ :=
    (coeffwiseRealCHom K).f₁.toAlgebra
  let L := prodTrivializationCoord K M
  let term : Fin (productFiberRankBoundN K M) → (M.baseChange (coeffwiseRealCHom K)).M :=
    fun j => (coeffwiseRealCHom K).f₁ (v j) •
      ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁]
        productFiberGenerator K M j)
  funext i
  change L ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁]
      productFiberPresentation K M v) c i = _
  rw [one_tmul_productFiberPresentation_eq_sum_generators]
  change L (∑ j, term j) c i = _
  rw [show L (∑ j, term j) = ∑ j, L (term j) by
    exact map_sum L term Finset.univ]
  rw [show (∑ j, L (term j)) c i = ∑ j, L (term j) c i by
    calc
      (∑ j, L (term j)) c i = (∑ j, L (term j) c) i := by
        exact congrArg (fun z : (prodRealC K).R₁ => z i)
          (Finset.sum_apply c Finset.univ _)
      _ = ∑ j, L (term j) c i := Finset.sum_apply i Finset.univ _]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [term]
  have h := congrArg
    (fun z : Fin (productFiberRankBoundN K M) → (prodRealC K).R₁ => z c i)
    (map_smul L ((coeffwiseRealCHom K).f₁ (v j))
      ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁]
        productFiberGenerator K M j))
  exact h

/-- If the chosen generators have coefficientwise-range trivialized coordinates,
then every element does. -/
private lemma trivializedCoordinatesInCoeffwiseRange_of_generators
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (hgen : GeneratorTrivializedCoordinatesInCoeffwiseRange K M) :
    TrivializedCoordinatesInCoeffwiseRange K M := by
  intro m c
  obtain ⟨v, hv⟩ := productFiberPresentation_surjective K M m
  rw [← hv]
  rw [trivializedCoordFamily_presentation]
  exact inCoeffwiseRange_finset_sum K Finset.univ
    (fun j i => (show (realC (K i)).R₁ from coeffwiseEvalRingHom K i (v j)) •
      (show (realC (K i)).R₁ from trivializedCoordFamily K M
        (productFiberGenerator K M j) c i))
    (fun j => inCoeffwiseRange_smul_left K (v j) (hgen j c))

/-- Every trivialized coordinate of every element of `M` is in the coefficientwise
range. -/
lemma trivializedCoordinatesInCoeffwiseRange
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    TrivializedCoordinatesInCoeffwiseRange K M :=
  trivializedCoordinatesInCoeffwiseRange_of_generators K M
    (generatorTrivializedCoordinatesInCoeffwiseRange_of_coordinate_equalities K M
      (generatorForwardCoordinateEquality K M)
      (generatorInverseCoordinateEquality K M))

end

end Novikov.Descent
