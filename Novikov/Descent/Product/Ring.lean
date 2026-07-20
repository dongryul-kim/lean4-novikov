import Novikov.Descent.CoefficientMap

/-!
# Product cosimplicial rings for products of coefficient rings

This file defines the levelwise product of the real Novikov cosimplicial rings
attached to a family of coefficient rings, together with the coefficientwise
map from the real Novikov cosimplicial ring over the product ring and the
projection maps back to the factors.
-/

open Novikov.Descent.Abstract

namespace Novikov.Descent

universe u v w

/-- Componentwise ring homomorphism between dependent products of semirings. -/
private def componentwiseRingHom {I : Type u} {A : I → Type v} {B : I → Type w}
    [∀ i, Semiring (A i)] [∀ i, Semiring (B i)] (f : ∀ i, A i →+* B i) :
    ((i : I) → A i) →+* ((i : I) → B i) :=
  Pi.ringHom fun i => (f i).comp (Pi.evalRingHom A i)

@[simp]
private lemma componentwiseRingHom_apply {I : Type u} {A : I → Type v} {B : I → Type w}
    [∀ i, Semiring (A i)] [∀ i, Semiring (B i)] (f : ∀ i, A i →+* B i)
    (x : (i : I) → A i) (i : I) :
    componentwiseRingHom f x i = f i (x i) := rfl

/-- Product, level by level, of the real Novikov cosimplicial rings attached to a
family of coefficient rings. -/
noncomputable def prodRealC {I : Type u} (K : I → Type v) [∀ i, CommRing (K i)] :
    CosimplicialRing where
  R₁ := ∀ i, (realC (K i)).R₁
  R₂ := ∀ i, (realC (K i)).R₂
  R₃ := ∀ i, (realC (K i)).R₃
  π₁ := componentwiseRingHom fun i => (realC (K i)).π₁
  π₂ := componentwiseRingHom fun i => (realC (K i)).π₂
  π₁₂ := componentwiseRingHom fun i => (realC (K i)).π₁₂
  π₁₃ := componentwiseRingHom fun i => (realC (K i)).π₁₃
  π₂₃ := componentwiseRingHom fun i => (realC (K i)).π₂₃
  π₁₃_π₁_eq_π₁₂_π₁ := by
    ext x i
    exact RingHom.congr_fun (realC (K i)).π₁₃_π₁_eq_π₁₂_π₁ (x i)
  π₁₂_π₂_eq_π₂₃_π₁ := by
    ext x i
    exact RingHom.congr_fun (realC (K i)).π₁₂_π₂_eq_π₂₃_π₁ (x i)
  π₁₃_π₂_eq_π₂₃_π₂ := by
    ext x i
    exact RingHom.congr_fun (realC (K i)).π₁₃_π₂_eq_π₂₃_π₂ (x i)

@[simp]
lemma prodRealC_π₁_apply {I : Type u} (K : I → Type v) [∀ i, CommRing (K i)]
    (x : (prodRealC K).R₁) (i : I) :
    ((prodRealC K).π₁ x) i = (realC (K i)).π₁ (x i) := rfl

@[simp]
lemma prodRealC_π₂_apply {I : Type u} (K : I → Type v) [∀ i, CommRing (K i)]
    (x : (prodRealC K).R₁) (i : I) :
    ((prodRealC K).π₂ x) i = (realC (K i)).π₂ (x i) := rfl

@[simp]
lemma prodRealC_π₁₂_apply {I : Type u} (K : I → Type v) [∀ i, CommRing (K i)]
    (x : (prodRealC K).R₂) (i : I) :
    ((prodRealC K).π₁₂ x) i = (realC (K i)).π₁₂ (x i) := rfl

@[simp]
lemma prodRealC_π₁₃_apply {I : Type u} (K : I → Type v) [∀ i, CommRing (K i)]
    (x : (prodRealC K).R₂) (i : I) :
    ((prodRealC K).π₁₃ x) i = (realC (K i)).π₁₃ (x i) := rfl

@[simp]
lemma prodRealC_π₂₃_apply {I : Type u} (K : I → Type v) [∀ i, CommRing (K i)]
    (x : (prodRealC K).R₂) (i : I) :
    ((prodRealC K).π₂₃ x) i = (realC (K i)).π₂₃ (x i) := rfl

/-- Coefficientwise embedding from Novikov series over a product ring to the
product of Novikov series over the factors, as a cosimplicial-ring homomorphism. -/
noncomputable def coeffwiseRealCHom {I : Type u} (K : I → Type v)
    [∀ i, CommRing (K i)] :
    CosimplicialRingHom (realC (∀ i, K i)) (prodRealC K) where
  f₁ := coeffwisePiRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K
  f₂ := coeffwisePiRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K
  f₃ := coeffwisePiRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 3) K
  comm_π₁ := by
    ext x
    funext i
    exact (realCCoeffHom (Pi.evalRingHom K i)).map_π₁_apply x
  comm_π₂ := by
    ext x
    funext i
    exact (realCCoeffHom (Pi.evalRingHom K i)).map_π₂_apply x
  comm_π₁₂ := by
    ext x
    funext i
    exact (realCCoeffHom (Pi.evalRingHom K i)).map_π₁₂_apply x
  comm_π₁₃ := by
    ext x
    funext i
    exact (realCCoeffHom (Pi.evalRingHom K i)).map_π₁₃_apply x
  comm_π₂₃ := by
    ext x
    funext i
    exact (realCCoeffHom (Pi.evalRingHom K i)).map_π₂₃_apply x

/-- Evaluation at one factor of the product cosimplicial ring. -/
noncomputable def evalProdRealCHom {I : Type u} (K : I → Type v)
    [∀ i, CommRing (K i)] (i : I) :
    CosimplicialRingHom (prodRealC K) (realC (K i)) where
  f₁ := Pi.evalRingHom (fun j => (realC (K j)).R₁) i
  f₂ := Pi.evalRingHom (fun j => (realC (K j)).R₂) i
  f₃ := Pi.evalRingHom (fun j => (realC (K j)).R₃) i
  comm_π₁ := by ext x; rfl
  comm_π₂ := by ext x; rfl
  comm_π₁₂ := by ext x; rfl
  comm_π₁₃ := by ext x; rfl
  comm_π₂₃ := by ext x; rfl

/-- Evaluating the coefficientwise product map at one factor recovers the
generic real Novikov coefficient map induced by evaluation. -/
lemma eval_comp_coeffwiseRealCHom {I : Type u} (K : I → Type v)
    [∀ i, CommRing (K i)] (i : I) :
    (evalProdRealCHom K i).comp (coeffwiseRealCHom K) =
      realCCoeffHom (Pi.evalRingHom K i) := by
  apply CosimplicialRingHom.ext
  · rfl
  · rfl
  · rfl

@[simp]
lemma coeffwiseRealCHom_f₁_apply {I : Type u} (K : I → Type v)
    [∀ i, CommRing (K i)] (x : (realC (∀ i, K i)).R₁) (i : I) :
    (coeffwiseRealCHom K).f₁ x i =
      coeffwiseEvalRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K i x := rfl

@[simp]
lemma coeffwiseRealCHom_f₂_apply {I : Type u} (K : I → Type v)
    [∀ i, CommRing (K i)] (x : (realC (∀ i, K i)).R₂) (i : I) :
    (coeffwiseRealCHom K).f₂ x i =
      coeffwiseEvalRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i x := rfl

@[simp]
lemma coeffwiseRealCHom_f₃_apply {I : Type u} (K : I → Type v)
    [∀ i, CommRing (K i)] (x : (realC (∀ i, K i)).R₃) (i : I) :
    (coeffwiseRealCHom K).f₃ x i =
      coeffwiseEvalRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 3) K i x := rfl

@[simp]
lemma evalProdRealCHom_f₁_apply {I : Type u} (K : I → Type v)
    [∀ i, CommRing (K i)] (i : I) (x : (prodRealC K).R₁) :
    (evalProdRealCHom K i).f₁ x = x i := rfl

@[simp]
lemma evalProdRealCHom_f₂_apply {I : Type u} (K : I → Type v)
    [∀ i, CommRing (K i)] (i : I) (x : (prodRealC K).R₂) :
    (evalProdRealCHom K i).f₂ x = x i := rfl

@[simp]
lemma evalProdRealCHom_f₃_apply {I : Type u} (K : I → Type v)
    [∀ i, CommRing (K i)] (i : I) (x : (prodRealC K).R₃) :
    (evalProdRealCHom K i).f₃ x = x i := rfl

@[simp]
lemma eval_comp_coeffwiseRealCHom_f₁ {I : Type u} (K : I → Type v)
    [∀ i, CommRing (K i)] (i : I) :
    ((evalProdRealCHom K i).comp (coeffwiseRealCHom K)).f₁ =
      coeffwiseEvalRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K i := by
  rfl

@[simp]
lemma eval_comp_coeffwiseRealCHom_f₂ {I : Type u} (K : I → Type v)
    [∀ i, CommRing (K i)] (i : I) :
    ((evalProdRealCHom K i).comp (coeffwiseRealCHom K)).f₂ =
      coeffwiseEvalRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) K i := by
  rfl

@[simp]
lemma eval_comp_coeffwiseRealCHom_f₃ {I : Type u} (K : I → Type v)
    [∀ i, CommRing (K i)] (i : I) :
    ((evalProdRealCHom K i).comp (coeffwiseRealCHom K)).f₃ =
      coeffwiseEvalRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 3) K i := by
  rfl

end Novikov.Descent
