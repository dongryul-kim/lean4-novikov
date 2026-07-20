import Novikov.Descent.Product.Trivialization
import Novikov.Descent.Product.SupportCombinatorics

/-!
# Generator presentations and transition formulas for product descent

This file constructs the chosen product generators, their pullback
presentations and transition coefficients, and the corresponding single-fiber
generator formulas.  It is independent of the expensive pointwise compatibility
between a fiber trivialization and its descent datum.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract
open scoped BigOperators

namespace Novikov.Descent

noncomputable section

universe u v

variable {S : Type*} [SetLike S ℝ] {Γ : S}

private lemma pi_single_one_eq_indicator {R ι : Type*} [Semiring R] [DecidableEq ι]
    (i : ι) :
    Pi.single (M := fun _ : ι => R) i (1 : R) = fun j => if i = j then 1 else 0 := by
  funext j
  simp [Pi.single_apply, eq_comm]

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)] [∀ i, IsAlgClosed (K i)]

omit [∀ i, IsAlgClosed (K i)] in
/-- Multiplication by a product-coefficient Novikov series, written as scalar
multiplication in each fiber, preserves the coefficientwise range. -/
lemma inCoeffwiseRange_smul_left
    (a : NovikovSeries (⊤ : AddSubgroup ℝ) Unit (∀ i, K i))
    {x : ∀ i, NovikovSeries (⊤ : AddSubgroup ℝ) Unit (K i)}
    (hx : InCoeffwiseRange K x) :
    InCoeffwiseRange K (fun i => (show (realC (K i)).R₁ from coeffwiseEvalRingHom K i a) •
      (show (realC (K i)).R₁ from x i)) := by
  simpa [smul_eq_mul] using inCoeffwiseRange_mul_left K a hx

/-- The chosen generators of the underlying product Novikov module. -/
noncomputable def productFiberGenerator
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j : Fin (productFiberRankBoundN K M)) : M.M :=
  productFiberPresentation K M (Pi.single j 1)

omit [∀ i, IsAlgClosed (K i)] in
lemma productFiberPresentation_eq_sum_generators
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (v : Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₁) :
    productFiberPresentation K M v =
      ∑ j : Fin (productFiberRankBoundN K M), v j • productFiberGenerator K M j := by
  simpa only [productFiberGenerator, pi_single_one_eq_indicator] using
    LinearMap.pi_apply_eq_sum_univ (productFiberPresentation K M) v

/-- The base change of the chosen product presentation along `π₂`. -/
noncomputable def productPullback₂Presentation
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    (Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₂) →ₗ[
      (realC (∀ i, K i)).R₂] π₂s (realC (∀ i, K i)) M.M := by
  letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
    (realC (∀ i, K i)).π₂.toAlgebra
  let e := TensorProduct.piScalarRight (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂
    (realC (∀ i, K i)).R₂ (Fin (productFiberRankBoundN K M))
  exact (LinearMap.baseChange (realC (∀ i, K i)).R₂ (productFiberPresentation K M)).comp
    e.symm.toLinearMap

omit [∀ i, IsAlgClosed (K i)] in
private lemma productPullback₂Presentation_surjective
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    Function.Surjective (productPullback₂Presentation K M) := by
  letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
    (realC (∀ i, K i)).π₂.toAlgebra
  dsimp [productPullback₂Presentation]
  exact (LinearMap.baseChange_surjective (realC (∀ i, K i)).R₂
      (productFiberPresentation_surjective K M)).comp
    (LinearEquiv.surjective _)

omit [∀ i, IsAlgClosed (K i)] in
/-- The `π₂`-pullback presentation is the finite sum over the chosen generators. -/
lemma productPullback₂Presentation_eq_sum_generators
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (w : Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₂) :
    productPullback₂Presentation K M w =
      ∑ k : Fin (productFiberRankBoundN K M),
        w k • ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
          (realC (∀ i, K i)).π₂.toAlgebra;
          (1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁]
            productFiberGenerator K M k)) := by
  have h : productPullback₂Presentation K M w =
      ∑ k : Fin (productFiberRankBoundN K M),
        w k • productPullback₂Presentation K M (Pi.single k 1) := by
    simpa only [pi_single_one_eq_indicator] using
      LinearMap.pi_apply_eq_sum_univ (productPullback₂Presentation K M) w
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
    (realC (∀ i, K i)).π₂.toAlgebra
  dsimp [productPullback₂Presentation]
  rw [TensorProduct.piScalarRight_symm_single]
  rw [LinearMap.baseChange_tmul]
  rfl

/-- The base change of the chosen product presentation along `π₁`. -/
noncomputable def productPullback₁Presentation
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    (Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₂) →ₗ[
      (realC (∀ i, K i)).R₂] π₁s (realC (∀ i, K i)) M.M := by
  letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
    (realC (∀ i, K i)).π₁.toAlgebra
  let e := TensorProduct.piScalarRight (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂
    (realC (∀ i, K i)).R₂ (Fin (productFiberRankBoundN K M))
  exact (LinearMap.baseChange (realC (∀ i, K i)).R₂ (productFiberPresentation K M)).comp
    e.symm.toLinearMap

omit [∀ i, IsAlgClosed (K i)] in
lemma productPullback₁Presentation_surjective
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    Function.Surjective (productPullback₁Presentation K M) := by
  letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
    (realC (∀ i, K i)).π₁.toAlgebra
  dsimp [productPullback₁Presentation]
  exact (LinearMap.baseChange_surjective (realC (∀ i, K i)).R₂
      (productFiberPresentation_surjective K M)).comp
    (LinearEquiv.surjective _)

omit [∀ i, IsAlgClosed (K i)] in
/-- The `π₁`-pullback presentation is the finite sum over the chosen generators. -/
lemma productPullback₁Presentation_eq_sum_generators
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (w : Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₂) :
    productPullback₁Presentation K M w =
      ∑ k : Fin (productFiberRankBoundN K M),
        w k • ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
          (realC (∀ i, K i)).π₁.toAlgebra;
          (1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁]
            productFiberGenerator K M k)) := by
  have h : productPullback₁Presentation K M w =
      ∑ k : Fin (productFiberRankBoundN K M),
        w k • productPullback₁Presentation K M (Pi.single k 1) := by
    simpa only [pi_single_one_eq_indicator] using
      LinearMap.pi_apply_eq_sum_univ (productPullback₁Presentation K M) w
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
    (realC (∀ i, K i)).π₁.toAlgebra
  dsimp [productPullback₁Presentation]
  rw [TensorProduct.piScalarRight_symm_single]
  rw [LinearMap.baseChange_tmul]
  rfl

/-- Chosen coefficients expressing the descent translate of a generator in the
`π₂`-pullback of the chosen presentation. -/
noncomputable def generatorTransitionVector
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j : Fin (productFiberRankBoundN K M)) :
    Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₂ := by
  let x : π₂s (realC (∀ i, K i)) M.M :=
    M.φ ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
      (realC (∀ i, K i)).π₁.toAlgebra;
      (1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁]
        productFiberGenerator K M j))
  exact Classical.choose (productPullback₂Presentation_surjective K M x)

omit [∀ i, IsAlgClosed (K i)] in
lemma productPullback₂Presentation_generatorTransitionVector
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j : Fin (productFiberRankBoundN K M)) :
    productPullback₂Presentation K M (generatorTransitionVector K M j) =
      M.φ ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
        (realC (∀ i, K i)).π₁.toAlgebra;
        (1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁]
          productFiberGenerator K M j)) :=
  Classical.choose_spec (productPullback₂Presentation_surjective K M _)

/-- Individual transition coefficient `a_{jk}` in the proof. -/
noncomputable def generatorTransitionCoeff
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j k : Fin (productFiberRankBoundN K M)) : (realC (∀ i, K i)).R₂ :=
  generatorTransitionVector K M j k

/-- Chosen coefficients expressing the inverse descent translate of a generator in the
`π₁`-pullback of the chosen presentation. -/
private noncomputable def generatorInverseTransitionVector
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j : Fin (productFiberRankBoundN K M)) :
    Fin (productFiberRankBoundN K M) → (realC (∀ i, K i)).R₂ := by
  let x : π₁s (realC (∀ i, K i)) M.M :=
    M.φ.symm ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
      (realC (∀ i, K i)).π₂.toAlgebra;
      (1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁]
        productFiberGenerator K M j))
  exact Classical.choose (productPullback₁Presentation_surjective K M x)

omit [∀ i, IsAlgClosed (K i)] in
private lemma productPullback₁Presentation_generatorInverseTransitionVector
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j : Fin (productFiberRankBoundN K M)) :
    productPullback₁Presentation K M (generatorInverseTransitionVector K M j) =
      M.φ.symm ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
        (realC (∀ i, K i)).π₂.toAlgebra;
        (1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁]
          productFiberGenerator K M j)) :=
  Classical.choose_spec (productPullback₁Presentation_surjective K M _)

/-- Individual inverse transition coefficient. -/
noncomputable def generatorInverseTransitionCoeff
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (j k : Fin (productFiberRankBoundN K M)) : (realC (∀ i, K i)).R₂ :=
  generatorInverseTransitionVector K M j k

omit [∀ i, IsAlgClosed (K i)] in
/-- Compatibility of the `π₂` base-change comparison with a scalar multiple of a
chosen generator tensor.  This is the local algebraic normalization used to
transport the global transition coefficients to a fiber. -/
private lemma fiberPullbackBaseChangeπ₂_symm_smul_one_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (c : (realC (∀ i, K i)).R₂) (m : M.M) :
    ((fiberRealCHom K i).pullbackBaseChangeπ₂ M.M).symm
      ((letI : Algebra (realC (∀ i, K i)).R₂ (realC (K i)).R₂ :=
          (fiberRealCHom K i).f₂.toAlgebra
        letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₁.toAlgebra
        letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
          (realC (∀ i, K i)).π₂.toAlgebra
        (c • ((1 : (realC (K i)).R₁) • (1 : (realC (K i)).R₂))) ⊗ₜ[
          (realC (∀ i, K i)).R₂]
          ((1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁] m))) =
      (show (realC (K i)).R₂ from (fiberRealCHom K i).f₂ c) •
        ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
          letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
            (fiberRealCHom K i).f₁.toAlgebra
          (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁]
            ((1 : (realC (K i)).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m))) := by
  letI : Algebra (realC (∀ i, K i)).R₂ (realC (K i)).R₂ :=
    (fiberRealCHom K i).f₂.toAlgebra
  letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
    (realC (∀ i, K i)).π₂.toAlgebra
  rw [CosimplicialRingHom.pullbackBaseChangeπ₂_symm_tmul]
  letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
  rw [TensorProduct.smul_tmul']
  congr 1
  simp only [smul_eq_mul, mul_one]
  rw [Algebra.smul_def]
  rw [show (letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ :=
      (realC (K i)).π₁.toAlgebra
      ((1 : (realC (K i)).R₁) • (1 : (realC (K i)).R₂))) =
        (1 : (realC (K i)).R₂) by
    change (realC (K i)).π₁ (1 : (realC (K i)).R₁) * (1 : (realC (K i)).R₂) = 1
    rw [map_one, one_mul]]
  rw [mul_one]
  rfl

omit [∀ i, IsAlgClosed (K i)] in
/-- Pure-tensor formula for the inverse of the base-changed descent isomorphism. -/
private lemma fiber_baseChangePhi_symm_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (r : (realC (K i)).R₂) (s : (realC (K i)).R₁) (m : M.M) :
    (fiberDescentDatum K M i).φ.symm
      ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
        letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
          (fiberRealCHom K i).f₁.toAlgebra
        r ⊗ₜ[(realC (K i)).R₁]
          (s ⊗ₜ[(realC (∀ i, K i)).R₁] m))) =
      ((fiberRealCHom K i).pullbackBaseChangeπ₁ M.M).symm
        ((letI : Algebra (realC (∀ i, K i)).R₂ (realC (K i)).R₂ :=
            (fiberRealCHom K i).f₂.toAlgebra
          letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
          (s • r) ⊗ₜ[(realC (∀ i, K i)).R₂]
            (M.φ.symm ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
              (realC (∀ i, K i)).π₂.toAlgebra;
              (1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁] m))))) := by
  change ((fiberRealCHom K i).baseChangePhi M).symm
      ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
        letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
          (fiberRealCHom K i).f₁.toAlgebra
        r ⊗ₜ[(realC (K i)).R₁]
          (s ⊗ₜ[(realC (∀ i, K i)).R₁] m))) = _
  exact (fiberRealCHom K i).baseChangePhi_symm_tmul M r s m

omit [∀ i, IsAlgClosed (K i)] in
/-- Compatibility of the `π₁` base-change comparison with a scalar multiple of a
chosen generator tensor. -/
private lemma fiberPullbackBaseChangeπ₁_symm_smul_one_tmul
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (c : (realC (∀ i, K i)).R₂) (m : M.M) :
    ((fiberRealCHom K i).pullbackBaseChangeπ₁ M.M).symm
      ((letI : Algebra (realC (∀ i, K i)).R₂ (realC (K i)).R₂ :=
          (fiberRealCHom K i).f₂.toAlgebra
        letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
        letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
          (realC (∀ i, K i)).π₁.toAlgebra
        (c • ((1 : (realC (K i)).R₁) • (1 : (realC (K i)).R₂))) ⊗ₜ[
          (realC (∀ i, K i)).R₂]
          ((1 : (realC (∀ i, K i)).R₂) ⊗ₜ[(realC (∀ i, K i)).R₁] m))) =
      (show (realC (K i)).R₂ from (fiberRealCHom K i).f₂ c) •
        ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₁.toAlgebra
          letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
            (fiberRealCHom K i).f₁.toAlgebra
          (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁]
            ((1 : (realC (K i)).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m))) := by
  letI : Algebra (realC (∀ i, K i)).R₂ (realC (K i)).R₂ :=
    (fiberRealCHom K i).f₂.toAlgebra
  letI : Algebra (realC (∀ i, K i)).R₁ (realC (∀ i, K i)).R₂ :=
    (realC (∀ i, K i)).π₁.toAlgebra
  rw [CosimplicialRingHom.pullbackBaseChangeπ₁_symm_tmul]
  letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₁.toAlgebra
  rw [TensorProduct.smul_tmul']
  congr 1
  simp only [smul_eq_mul, mul_one]
  rw [Algebra.smul_def]
  rw [show (letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ :=
      (realC (K i)).π₂.toAlgebra
      ((1 : (realC (K i)).R₁) • (1 : (realC (K i)).R₂))) =
        (1 : (realC (K i)).R₂) by
    change (realC (K i)).π₂ (1 : (realC (K i)).R₁) * (1 : (realC (K i)).R₂) = 1
    rw [map_one, one_mul]]
  rw [mul_one]
  rfl

omit [∀ i, IsAlgClosed (K i)] in
/-- The finite set of transition coefficients has a common lower bound for the
positive weight `(x,y) ↦ 2*x + y`. -/
lemma generatorTransitionCoeff_exists_weight_lower_bound
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    ∃ C : ℝ,
      ∀ (j k : Fin (productFiberRankBoundN K M)) (d : Fin 2 → (⊤ : AddSubgroup ℝ)),
        (generatorTransitionCoeff K M j k).val d ≠ 0 →
          C ≤ ∑ r : Fin 2, twoOneWeight r * (d r : ℝ) := by
  let α := Fin (productFiberRankBoundN K M) × Fin (productFiberRankBoundN K M)
  let W : (Fin 2 → (⊤ : AddSubgroup ℝ)) → ℝ := fun d =>
    ∑ r : Fin 2, twoOneWeight r * (d r : ℝ)
  let P : α → (Fin 2 → (⊤ : AddSubgroup ℝ)) → Prop := fun jk d =>
    (generatorTransitionCoeff K M jk.1 jk.2).val d ≠ 0
  have h_each : ∀ a : α, ∃ C : ℝ, ∀ d, P a d → C ≤ W d := by
    intro a
    exact hasNovikovFiniteness.exists_weighted_lower_bound
      (generatorTransitionCoeff K M a.1 a.2).prop twoOneWeight twoOneWeight_pos
  rcases exists_common_lower_bound_fintype W P h_each with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro j k d hd
  exact hC (j, k) d hd

/-- Coordinates of `m` after base change to the product of fibers and product
fiber trivialization. -/
noncomputable def trivializedCoordFamily
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) (c : Fin (productFiberRankBoundN K M)) :
    ∀ i, (realC (K i)).R₁ := by
  letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ :=
    (coeffwiseRealCHom K).f₁.toAlgebra
  exact prodTrivializationCoord K M
    ((1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m) c

@[simp]
lemma trivializedCoordFamily_apply
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (m : M.M) (c : Fin (productFiberRankBoundN K M)) (i : I) :
    trivializedCoordFamily K M m c i =
      prodTrivializationCoord K M
        ((letI : Algebra (realC (∀ i, K i)).R₁ (prodRealC K).R₁ :=
            (coeffwiseRealCHom K).f₁.toAlgebra;
          (1 : (prodRealC K).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁] m)) c i := by
  rfl

/-- The image of a chosen product generator in a single fiber of the descent
object. -/
private noncomputable def fiberGenerator
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j : Fin (productFiberRankBoundN K M)) : (fiberDescentDatum K M i).M :=
  (letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
      (fiberRealCHom K i).f₁.toAlgebra
   (1 : (realC (K i)).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁]
    productFiberGenerator K M j)

/-- The trivialized constant-fiber image of a chosen generator in a single
factor. -/
noncomputable def fiberGeneratorConstTriv
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j : Fin (productFiberRankBoundN K M)) :
    (fiberConstDescentDatum K M i).M :=
  fiberTrivializationLinearEquiv K M i
    ((letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
        (fiberRealCHom K i).f₁.toAlgebra
      (1 : (realC (K i)).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁]
        productFiberGenerator K M j))

/-- Component formula for the trivialized coordinate family on a chosen
generator. -/
lemma trivializedCoordFamily_generator_apply
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j c : Fin (productFiberRankBoundN K M)) :
    trivializedCoordFamily K M (productFiberGenerator K M j) c i =
      (letI : Algebra (K i) (realC (K i)).R₁ :=
        (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) (K i)).π₀.toAlgebra
       FiniteProjectiveModule.fiberBaseChangeCoord K (fiberConstModule K M)
        (productFiberRankBoundN K M) i (realC (K i)).R₁
          (fiberGeneratorConstTriv K M i j) c) := by
  rw [trivializedCoordFamily_apply]
  rw [prodTrivializationCoord_apply]
  rw [prodBaseChangeFiberEquiv_tmul]
  rfl

/-- The `π₁`-pullback of a chosen fiber generator. -/
noncomputable def fiberGeneratorPullback₁
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j : Fin (productFiberRankBoundN K M)) :
    π₁s (realC (K i)) (fiberDescentDatum K M i).M :=
  (letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₁.toAlgebra
   (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁] fiberGenerator K M i j)

/-- The `π₂`-pullback of a chosen fiber generator. -/
noncomputable def fiberGeneratorPullback₂
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j : Fin (productFiberRankBoundN K M)) :
    π₂s (realC (K i)) (fiberDescentDatum K M i).M :=
  (letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
   (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁] fiberGenerator K M i j)

/-- The `π₁`-pullback of a chosen trivialized constant-fiber generator. -/
noncomputable def fiberConstGeneratorPullback₁
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j : Fin (productFiberRankBoundN K M)) :
    π₁s (realC (K i)) (fiberConstDescentDatum K M i).M :=
  (letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₁.toAlgebra
   (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁] fiberGeneratorConstTriv K M i j)

/-- The `π₂`-pullback of a chosen trivialized constant-fiber generator. -/
noncomputable def fiberConstGeneratorPullback₂
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j : Fin (productFiberRankBoundN K M)) :
    π₂s (realC (K i)) (fiberConstDescentDatum K M i).M :=
  (letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
   (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁] fiberGeneratorConstTriv K M i j)

omit [∀ i, IsAlgClosed (K i)] in
/-- The fiber descent isomorphism on the abbreviated generator pullbacks. -/
lemma fiber_phi_generator_eq_sum_fiberGenerator
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j : Fin (productFiberRankBoundN K M)) :
    (fiberDescentDatum K M i).φ (fiberGeneratorPullback₁ K M i j) =
      ∑ k : Fin (productFiberRankBoundN K M),
        (show (realC (K i)).R₂ from coeffwiseEvalRingHom
          (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
          (generatorTransitionCoeff K M j k)) • fiberGeneratorPullback₂ K M i k := by
  dsimp only [fiberGeneratorPullback₁, fiberGeneratorPullback₂, fiberGenerator]
  change (fiberRealCHom K i).baseChangePhi M
      ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₁.toAlgebra
        letI : Algebra (realC (∀ i, K i)).R₁ (realC (K i)).R₁ :=
          (fiberRealCHom K i).f₁.toAlgebra
        (1 : (realC (K i)).R₂) ⊗ₜ[(realC (K i)).R₁]
          ((1 : (realC (K i)).R₁) ⊗ₜ[(realC (∀ i, K i)).R₁]
            productFiberGenerator K M j))) = _
  rw [CosimplicialRingHom.baseChangePhi_tmul]
  rw [← productPullback₂Presentation_generatorTransitionVector]
  rw [productPullback₂Presentation_eq_sum_generators]
  letI : Algebra (realC (∀ i, K i)).R₂ (realC (K i)).R₂ :=
    (fiberRealCHom K i).f₂.toAlgebra
  rw [TensorProduct.tmul_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [TensorProduct.tmul_smul]
  change _ = (show (realC (K i)).R₂ from (fiberRealCHom K i).f₂
      (generatorTransitionCoeff K M j k)) • _
  exact fiberPullbackBaseChangeπ₂_symm_smul_one_tmul K M i
    (generatorTransitionCoeff K M j k) (productFiberGenerator K M k)

omit [∀ i, IsAlgClosed (K i)] in
/-- The inverse fiber descent isomorphism on the abbreviated generator
pullbacks. -/
lemma fiber_phi_symm_generator_eq_sum_fiberGenerator
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j : Fin (productFiberRankBoundN K M)) :
    (fiberDescentDatum K M i).φ.symm (fiberGeneratorPullback₂ K M i j) =
      ∑ k : Fin (productFiberRankBoundN K M),
        (show (realC (K i)).R₂ from coeffwiseEvalRingHom
          (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i
          (generatorInverseTransitionCoeff K M j k)) • fiberGeneratorPullback₁ K M i k := by
  dsimp only [fiberGeneratorPullback₁, fiberGeneratorPullback₂, fiberGenerator]
  rw [fiber_baseChangePhi_symm_tmul]
  rw [← productPullback₁Presentation_generatorInverseTransitionVector]
  rw [productPullback₁Presentation_eq_sum_generators]
  letI : Algebra (realC (∀ i, K i)).R₂ (realC (K i)).R₂ :=
    (fiberRealCHom K i).f₂.toAlgebra
  rw [TensorProduct.tmul_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [TensorProduct.tmul_smul]
  change _ = (show (realC (K i)).R₂ from (fiberRealCHom K i).f₂
      (generatorInverseTransitionCoeff K M j k)) • _
  exact fiberPullbackBaseChangeπ₁_symm_smul_one_tmul K M i
    (generatorInverseTransitionCoeff K M j k) (productFiberGenerator K M k)

/-- Base-changing the fiber trivialization along `π₁` sends a generator pullback
to the corresponding constant-generator pullback. -/
lemma fiberGeneratorConstTriv_pullback₁
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j : Fin (productFiberRankBoundN K M)) :
    (letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₁.toAlgebra
     LinearMap.baseChange (realC (K i)).R₂ (fiberTrivializationLinearEquiv K M i).toLinearMap
      (fiberGeneratorPullback₁ K M i j)) = fiberConstGeneratorPullback₁ K M i j := by
  dsimp [fiberGeneratorPullback₁, fiberConstGeneratorPullback₁, fiberGenerator,
    fiberGeneratorConstTriv]

/-- Base-changing the fiber trivialization along `π₂` sends a generator pullback
to the corresponding constant-generator pullback. -/
lemma fiberGeneratorConstTriv_pullback₂
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (j : Fin (productFiberRankBoundN K M)) :
    (letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ := (realC (K i)).π₂.toAlgebra
     LinearMap.baseChange (realC (K i)).R₂ (fiberTrivializationLinearEquiv K M i).toLinearMap
      (fiberGeneratorPullback₂ K M i j)) = fiberConstGeneratorPullback₂ K M i j := by
  dsimp [fiberGeneratorPullback₂, fiberConstGeneratorPullback₂, fiberGenerator,
    fiberGeneratorConstTriv]

end

end Novikov.Descent
