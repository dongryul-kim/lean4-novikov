import Novikov.Descent.RecoverDDFromIsoc
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Full faithfulness of the descent-to-isocrystal functor

This file proves Proposition 4.2 of `paper.tex`: for every commutative ring `A`,
the functor `descentToIsocrystal A` from real Novikov descent data to Novikov
isocrystals is fully faithful.

The argument mirrors the paper: an isocrystal morphism is an `R₁`-linear map
commuting with the descended Frobenii, and the recovery diagram
`recoverDDFromIsoc_equalizerLemma` is used to upgrade this to the descent-morphism
condition (`commute_φ`).
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract

namespace Novikov.Descent

/-- Generic extensionality for `S`-linear maps out of a base change `S ⊗[R] M`:
two such maps agree as soon as they agree on the generators `1 ⊗ m`. -/
lemma baseChange_linearMap_ext
    {R S P M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module S P]
    {L₁ L₂ : S ⊗[R] M →ₗ[S] P}
    (h : ∀ m : M, L₁ ((1 : S) ⊗ₜ[R] m) = L₂ ((1 : S) ⊗ₜ[R] m)) :
    L₁ = L₂ := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      have hs : s ⊗ₜ[R] m = s • ((1 : S) ⊗ₜ[R] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, h]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

section RecoverMapLemmas

variable (A : Type*) [CommRing A]

/-- `recoverTopMap` is additive. -/
lemma recoverTopMap_add (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) (m n : M.M) :
    recoverTopMap A M (m + n) = recoverTopMap A M m + recoverTopMap A M n := by
  rw [recoverTopMap_apply, recoverTopMap_apply, recoverTopMap_apply, map_add, map_add]

/-- `oneTmulπ₁` carries the `R₁`-action to the `R₂`-action through `π₁`. -/
lemma oneTmulπ₁_smul (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M]
    (r : (realC A).R₁) (m : M) :
    oneTmulπ₁ A M (r • m) = (realC A).π₁ r • oneTmulπ₁ A M m := by
  letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
  rw [oneTmulπ₁_apply, oneTmulπ₁_apply]
  change (1 : (realC A).R₂) ⊗ₜ[(realC A).R₁] (r • m) =
    (realC A).π₁ r • ((1 : (realC A).R₂) ⊗ₜ[(realC A).R₁] m)
  rw [TensorProduct.tmul_smul, ← algebraMap_smul (realC A).R₂ r
    ((1 : (realC A).R₂) ⊗ₜ[(realC A).R₁] m)]
  rfl

/-- `recoverTopMap` carries the `R₁`-action on `M` to the `R₂`-action through
`π₁`. -/
lemma recoverTopMap_smul_π₁ (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (r : (realC A).R₁) (m : M.M) :
    recoverTopMap A M (r • m) = (realC A).π₁ r • recoverTopMap A M m := by
  rw [recoverTopMap_apply, recoverTopMap_apply, oneTmulπ₁_smul, map_smul]

/-- `recoverTopMap` is injective. -/
lemma recoverTopMap_injective (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) :
    Function.Injective (recoverTopMap A M) := by
  intro m n h
  rw [recoverTopMap_apply, recoverTopMap_apply] at h
  exact oneTmulπ₁_injective A M.M (M.φ.injective h)

/-- Two `R₂`-linear maps out of `π₂^* M` agree as soon as they agree on the
generating family `recoverTopMap A M m`. -/
lemma linearMap_ext_of_eq_on_recoverTopMap
    (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    {P : Type*} [AddCommGroup P] [Module (realC A).R₂ P]
    {L₁ L₂ : π₂s (realC A) M.M →ₗ[(realC A).R₂] P}
    (h : ∀ m : M.M, L₁ (recoverTopMap A M m) = L₂ (recoverTopMap A M m)) :
    L₁ = L₂ := by
  have key : L₁ ∘ₗ M.φ.toLinearMap = L₂ ∘ₗ M.φ.toLinearMap := by
    letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
    apply baseChange_linearMap_ext
    intro m
    change L₁ (M.φ (oneTmulπ₁ A M.M m)) = L₂ (M.φ (oneTmulπ₁ A M.M m))
    rw [← recoverTopMap_apply]
    exact h m
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ := M.φ.surjective y
  exact LinearMap.congr_fun key w

end RecoverMapLemmas

section Naturality

variable (A : Type*) [CommRing A]

/-- `baseChangeMap π₂` sends `oneTmulπ₂` to `oneTmulπ₂` of the image. -/
lemma baseChangeMap_π₂_oneTmulπ₂_linear {M N : Type*} [AddCommGroup M]
    [Module (realC A).R₁ M] [AddCommGroup N] [Module (realC A).R₁ N]
    (f : M →ₗ[(realC A).R₁] N) (m : M) :
    baseChangeMap (realC A).π₂ f (oneTmulπ₂ (A := A) M m) =
      oneTmulπ₂ (A := A) N (f m) := by
  rw [oneTmulπ₂_apply, baseChangeMap_tmul, oneTmulπ₂_apply]

/-- Naturality of `π₁₃star` with respect to a base-changed linear map. -/
lemma baseChangeMap_ρ₃_π₁₃star {M N : Type*} [AddCommGroup M]
    [Module (realC A).R₁ M] [AddCommGroup N] [Module (realC A).R₁ N]
    (f : M →ₗ[(realC A).R₁] N) (x : π₂s (realC A) M) :
    baseChangeMap (realC A).ρ₃ f (π₁₃star A M x) =
      π₁₃star A N (baseChangeMap (realC A).π₂ f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      simp only [π₁₃star, LinearMap.rTensor_tmul, baseChangeMap_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- `π₁₃star` sends the generator `oneTmulπ₂ m` to the pure tensor `1 ⊗ m` in
`ρ₃^* M`. -/
lemma π₁₃star_oneTmulπ₂ {M : Type*} [AddCommGroup M] [Module (realC A).R₁ M] (m : M) :
    letI : Algebra (realC A).R₁ (realC A).R₃ := (realC A).ρ₃.toAlgebra
    π₁₃star A M (oneTmulπ₂ (A := A) M m) = (1 : (realC A).R₃) ⊗ₜ[(realC A).R₁] m := by
  rw [π₁₃star_eq_natExt, oneTmulπ₂_apply, natExt_tmul, map_one]

end Naturality

section RecoverBottomMapGeneric

variable {C : CosimplicialRing}

/-- The natural extension along `π₁₂` carries the `R₂`-action to the `R₃`-action
through `π₁₂`. -/
lemma natExt_smul_π₁₂_generic (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (r : C.R₂) (x : π₂s C M) :
    natExt C.π₂ C.π₁₂ C.ρ₂_eq_π₁₂_π₂.symm M (r • x) =
      C.π₁₂ r • natExt C.π₂ C.π₁₂ C.ρ₂_eq_π₁₂_π₂.symm M x := by
  letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
  letI : Algebra C.R₁ C.R₃ := C.ρ₂.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      have hl : r • (s ⊗ₜ[C.R₁] m) = (r * s) ⊗ₜ[C.R₁] m := by
        rw [TensorProduct.smul_tmul', smul_eq_mul]
      have hr : C.π₁₂ r • (C.π₁₂ s ⊗ₜ[C.R₁] m) = (C.π₁₂ r * C.π₁₂ s) ⊗ₜ[C.R₁] m := by
        rw [TensorProduct.smul_tmul', smul_eq_mul]
      rw [hl, natExt_tmul, natExt_tmul, hr, map_mul]
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]

/-- Naturality of the scalar extension `natExt π₂ π₂₃` under base change. -/
lemma baseChangeMap_ρ₃_natExt_π₂₃_generic
    {M N : Type*} [AddCommGroup M] [Module C.R₁ M] [AddCommGroup N] [Module C.R₁ N]
    (f : M →ₗ[C.R₁] N) (y : π₂s C M) :
    baseChangeMap C.ρ₃ f (natExt C.π₂ C.π₂₃ C.ρ₃_eq_π₂₃_π₂.symm M y) =
      natExt C.π₂ C.π₂₃ C.ρ₃_eq_π₂₃_π₂.symm N (baseChangeMap C.π₂ f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => rw [natExt_tmul, baseChangeMap_tmul, baseChangeMap_tmul, natExt_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- `pullbackMap_23` intertwines the `π₂₃`-extensions of a `π₁`-generator and the
corresponding `π₂`-element through `φ`.  Stated over an abstract `C` so that a
concrete `realC` instantiation is a pure substitution (no kernel reduction of the
heavy `pullbackMap` body). -/
lemma recoverBottomMapGeneric_natExt_oneTmul (M : DescentDatum C) (w : π₁s C M.M) :
    pullbackMap_23 C M.M M.φ (natExt C.π₁ C.π₂₃ C.ρ₂_eq_π₂₃_π₁.symm M.M w) =
      natExt C.π₂ C.π₂₃ C.ρ₃_eq_π₂₃_π₂.symm M.M (M.φ w) :=
  pullbackMap_natExt C.π₁ C.π₂ C.π₂₃ C.ρ₂_eq_π₂₃_π₁.symm C.ρ₃_eq_π₂₃_π₂.symm M.M M.φ w

/-- The two `π₁₂`/`π₂₃`-extensions of `1 ⊗ m` agree (both equal `1 ⊗ m` in
`ρ₂^* M`). -/
lemma natExt_π₁₂_oneTmul_eq (M : Type*) [AddCommGroup M] [Module C.R₁ M] (m : M) :
    natExt C.π₂ C.π₁₂ C.ρ₂_eq_π₁₂_π₂.symm M
        (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra; TensorProduct.mk C.R₁ C.R₂ M 1 m) =
      natExt C.π₁ C.π₂₃ C.ρ₂_eq_π₂₃_π₁.symm M
        (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; TensorProduct.mk C.R₁ C.R₂ M 1 m) := by
  simp only [TensorProduct.mk_apply]
  rw [natExt_tmul, natExt_tmul, map_one, map_one]

/-- Generic bottom-row generator formula: the bottom-row inclusion of `1 ⊗ m` is
the `π₂₃`-extension of the top-row inclusion `φ (1 ⊗ m)`. -/
lemma recoverBottomMapGeneric_oneTmul (M : DescentDatum C) (m : M.M) :
    recoverBottomMapGeneric C M
        (letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra; TensorProduct.mk C.R₁ C.R₂ M.M 1 m) =
      natExt C.π₂ C.π₂₃ C.ρ₃_eq_π₂₃_π₂.symm M.M
        (M.φ (letI : Algebra C.R₁ C.R₂ := C.π₁.toAlgebra; TensorProduct.mk C.R₁ C.R₂ M.M 1 m)) := by
  unfold recoverBottomMapGeneric
  rw [natExt_π₁₂_oneTmul_eq, recoverBottomMapGeneric_natExt_oneTmul]

/-- `recoverBottomMapGeneric` sends `0` to `0`. -/
lemma recoverBottomMapGeneric_zero (M : DescentDatum C) :
    recoverBottomMapGeneric C M 0 = 0 := by
  unfold recoverBottomMapGeneric
  rw [map_zero, map_zero]

/-- `recoverBottomMapGeneric` is additive. -/
lemma recoverBottomMapGeneric_add (M : DescentDatum C) (x y : π₂s C M.M) :
    recoverBottomMapGeneric C M (x + y) =
      recoverBottomMapGeneric C M x + recoverBottomMapGeneric C M y := by
  unfold recoverBottomMapGeneric
  rw [map_add, map_add]

/-- `recoverBottomMapGeneric` is injective, given injectivity of the underlying
natural extension along `π₁₂`. -/
lemma recoverBottomMapGeneric_injective (M : DescentDatum C)
    (hinj : Function.Injective (natExt C.π₂ C.π₁₂ C.ρ₂_eq_π₁₂_π₂.symm M.M)) :
    Function.Injective (recoverBottomMapGeneric C M) := by
  intro x y h
  unfold recoverBottomMapGeneric at h
  exact hinj ((pullbackMap_23 C M.M M.φ).injective h)

/-- `recoverBottomMapGeneric` carries the `R₂`-action through `π₁₂`. -/
lemma recoverBottomMapGeneric_smul (M : DescentDatum C) (r : C.R₂) (x : π₂s C M.M) :
    recoverBottomMapGeneric C M (r • x) = C.π₁₂ r • recoverBottomMapGeneric C M x := by
  unfold recoverBottomMapGeneric
  rw [natExt_smul_π₁₂_generic, map_smul]

end RecoverBottomMapGeneric

section RecoverBottomMapLemmas

variable (A : Type*) [CommRing A]

/-- `recoverBottomMap` sends `0` to `0`. -/
lemma recoverBottomMap_zero (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) :
    recoverBottomMap A M 0 = 0 :=
  recoverBottomMapGeneric_zero M

/-- `recoverBottomMap` is additive. -/
lemma recoverBottomMap_add (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (x y : π₂s (realC A) M.M) :
    recoverBottomMap A M (x + y) = recoverBottomMap A M x + recoverBottomMap A M y :=
  recoverBottomMapGeneric_add M x y

/-- `recoverBottomMap` is injective. -/
lemma recoverBottomMap_injective (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) :
    Function.Injective (recoverBottomMap A M) :=
  recoverBottomMapGeneric_injective M (natExt_π₁₂_injective A M.M)

/-- `recoverBottomMap` carries the `R₂`-action through `π₁₂`. -/
lemma recoverBottomMap_smul_π₁₂ (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (r : (realC A).R₂) (x : π₂s (realC A) M.M) :
    recoverBottomMap A M (r • x) = (realC A).π₁₂ r • recoverBottomMap A M x :=
  recoverBottomMapGeneric_smul M r x

/-- The bottom-row inclusion of a `1 ⊗ m` generator is the `π₂₃`-extension of the
top-row inclusion `recoverTopMap A M m`. -/
lemma recoverBottomMap_oneTmulπ₂ (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (m : M.M) :
    recoverBottomMap A M (oneTmulπ₂ (A := A) M.M m) =
      natExt (realC A).π₂ (realC A).π₂₃ (realC A).ρ₃_eq_π₂₃_π₂.symm M.M
        (recoverTopMap A M m) := by
  rw [recoverBottomMap_apply, recoverTopMap_apply]
  exact recoverBottomMapGeneric_oneTmul M m

end RecoverBottomMapLemmas

section FrobeniusCommute

variable {Λ : ℝ} [Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

noncomputable local instance : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
noncomputable local instance : Algebra (realC A).R₁ (realC A).R₃ := (realC A).ρ₃.toAlgebra

/-- `FM2` on a pure tensor `s ⊗ m` scales the scalar by `F2` and applies the
descended Frobenius to `m`. -/
lemma FM2_tmulπ₂ (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (s : (realC A).R₂) (m : M.M) :
    FM2 (Λ := Λ) A M (s ⊗ₜ[(realC A).R₁] m) =
      F2 (Λ := Λ) A s ⊗ₜ[(realC A).R₁] descentFrobeniusToFun (Λ := Λ) A M m := by
  have hsm : (s ⊗ₜ[(realC A).R₁] m : π₂s (realC A) M.M) =
      s • oneTmulπ₂ (A := A) M.M m := by
    rw [oneTmulπ₂_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hsm, map_smulₛₗ, descentFrobeniusToFun_spec, oneTmulπ₂_apply,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- If `f` commutes with the descended Frobenii, then base change along `π₂`
intertwines the `FM2` Frobenii. -/
lemma baseChangeMap_π₂_FM2_of_commute_frobenius
    {M N : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A}
    (f : M.M →ₗ[(realC A).R₁] N.M)
    (hf : ∀ m, descentFrobeniusToFun (Λ := Λ) A N (f m) =
                f (descentFrobeniusToFun (Λ := Λ) A M m))
    (x : π₂s (realC A) M.M) :
    baseChangeMap (realC A).π₂ f (FM2 (Λ := Λ) A M x) =
      FM2 (Λ := Λ) A N (baseChangeMap (realC A).π₂ f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      rw [FM2_tmulπ₂, baseChangeMap_tmul, baseChangeMap_tmul, FM2_tmulπ₂, hf]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- If `f` commutes with the descended Frobenii, then base change along `ρ₃`
intertwines the `FM3` Frobenii.  Reduced (via the `π₁₃star`-generators and `FM3`'s
`F3`-semilinearity) to the right-square chain of the recovery diagram. -/
lemma baseChangeMap_ρ₃_FM3_of_commute_frobenius
    {M N : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A}
    (f : M.M →ₗ[(realC A).R₁] N.M)
    (hf : ∀ m, descentFrobeniusToFun (Λ := Λ) A N (f m) =
                f (descentFrobeniusToFun (Λ := Λ) A M m))
    (y : ρ₃s (realC A) M.M) :
    baseChangeMap (realC A).ρ₃ f (FM3 (Λ := Λ) A M y) =
      FM3 (Λ := Λ) A N (baseChangeMap (realC A).ρ₃ f y) := by
  have chain : ∀ x : π₂s (realC A) M.M,
      baseChangeMap (realC A).ρ₃ f (FM3 (Λ := Λ) A M (π₁₃star A M.M x)) =
        FM3 (Λ := Λ) A N (baseChangeMap (realC A).ρ₃ f (π₁₃star A M.M x)) := by
    intro x
    rw [← face13_FM2, baseChangeMap_ρ₃_π₁₃star,
        baseChangeMap_π₂_FM2_of_commute_frobenius A f hf, face13_FM2,
        ← baseChangeMap_ρ₃_π₁₃star]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      have hg : (s ⊗ₜ[(realC A).R₁] m : ρ₃s (realC A) M.M) =
          s • π₁₃star A M.M (oneTmulπ₂ (A := A) M.M m) := by
        rw [π₁₃star_oneTmulπ₂, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hg, map_smulₛₗ, map_smul, chain, map_smul, map_smulₛₗ]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end FrobeniusCommute

section MainProof

variable {Λ : ℝ} [Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

/-- **Proposition 4.2, the key step.**  An `R₁`-linear map `f` commuting with the
descended Frobenii is automatically a descent-datum morphism: its base changes
along `π₁`/`π₂` commute with the cocycles `φ`. -/
lemma descentToIsocrystal_full_aux
    {M N : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A}
    (f : M.M →ₗ[(realC A).R₁] N.M)
    (hf : ∀ m, descentFrobeniusToFun (Λ := Λ) A N (f m) =
                f (descentFrobeniusToFun (Λ := Λ) A M m)) :
    N.φ.toLinearMap ∘ₗ baseChangeMap (realC A).π₁ f =
      baseChangeMap (realC A).π₂ f ∘ₗ M.φ.toLinearMap := by
  set RM := recoverDDFromIsoc_equalizerLemma (Λ := Λ) A M with hRM
  set RN := recoverDDFromIsoc_equalizerLemma (Λ := Λ) A N with hRN
  -- `B₂ f` sends the top-row inclusion into the top equalizer of `N`.
  have hB2fix : ∀ m, FM2 (Λ := Λ) A N
      (baseChangeMap (realC A).π₂ f (recoverTopMap A M m)) =
      baseChangeMap (realC A).π₂ f (recoverTopMap A M m) := by
    intro m
    rw [← baseChangeMap_π₂_FM2_of_commute_frobenius A f hf, RM.topMem]
  -- Define `g` by the top-equalizer universal property for `N`.
  let g : M.M → N.M := fun m => (RN.topEqualizer _ (hB2fix m)).choose
  have hg_spec : ∀ m, recoverTopMap A N (g m) =
      baseChangeMap (realC A).π₂ f (recoverTopMap A M m) :=
    fun m => (RN.topEqualizer _ (hB2fix m)).choose_spec.1
  -- `g` is `R₁`-linear.
  have g_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂ := by
    intro m₁ m₂
    apply recoverTopMap_injective A N
    simp only [hg_spec, recoverTopMap_add, map_add]
  have g_smul : ∀ (r : (realC A).R₁) m, g (r • m) = r • g m := by
    intro r m
    apply recoverTopMap_injective A N
    simp only [hg_spec, recoverTopMap_smul_π₁, map_smul]
  let gLin : M.M →ₗ[(realC A).R₁] N.M :=
    { toFun := g, map_add' := g_add, map_smul' := fun r m => g_smul r m }
  have hg_specL : ∀ m, recoverTopMap A N (gLin m) =
      baseChangeMap (realC A).π₂ f (recoverTopMap A M m) := hg_spec
  -- `B₃ f` sends the bottom-row inclusion into the bottom equalizer of `N`.
  have hB3fix : ∀ x, FM3 (Λ := Λ) A N
      (baseChangeMap (realC A).ρ₃ f (recoverBottomMap A M x)) =
      baseChangeMap (realC A).ρ₃ f (recoverBottomMap A M x) := by
    intro x
    rw [← baseChangeMap_ρ₃_FM3_of_commute_frobenius A f hf, RM.bottomMem]
  -- Define `h` by the bottom-equalizer universal property for `N`.
  let h : π₂s (realC A) M.M → π₂s (realC A) N.M :=
    fun x => (RN.bottomEqualizer _ (hB3fix x)).choose
  have hh_spec : ∀ x, recoverBottomMap A N (h x) =
      baseChangeMap (realC A).ρ₃ f (recoverBottomMap A M x) :=
    fun x => (RN.bottomEqualizer _ (hB3fix x)).choose_spec.1
  -- Left face of the cube: `h ∘ recoverTopMap M = recoverTopMap N ∘ g`.
  have hleft : ∀ m, h (recoverTopMap A M m) = recoverTopMap A N (g m) := by
    intro m
    apply recoverBottomMap_injective A N
    rw [hh_spec, ← RM.leftSquare, baseChangeMap_ρ₃_π₁₃star, ← hg_spec, RN.leftSquare]
  -- Bottom-face commutativity with `π₂^* g` (the non-circular step, via the
  -- `oneTmulπ₂`-generators and `π₁₂`-semilinearity of `recoverBottomMap`).
  have hEQ : ∀ x, recoverBottomMap A N (baseChangeMap (realC A).π₂ gLin x) =
      baseChangeMap (realC A).ρ₃ f (recoverBottomMap A M x) := by
    have hgen : ∀ m, recoverBottomMap A N
          (baseChangeMap (realC A).π₂ gLin (oneTmulπ₂ (A := A) M.M m)) =
        baseChangeMap (realC A).ρ₃ f
          (recoverBottomMap A M (oneTmulπ₂ (A := A) M.M m)) := by
      intro m
      rw [baseChangeMap_π₂_oneTmulπ₂_linear, recoverBottomMap_oneTmulπ₂,
          recoverBottomMap_oneTmulπ₂, baseChangeMap_ρ₃_natExt_π₂₃_generic, ← hg_specL]
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, recoverBottomMap_zero, recoverBottomMap_zero, map_zero]
    | tmul s m =>
        letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
        have hsm : (s ⊗ₜ[(realC A).R₁] m : π₂s (realC A) M.M) =
            s • oneTmulπ₂ (A := A) M.M m := by
          rw [oneTmulπ₂_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hsm, map_smul, recoverBottomMap_smul_π₁₂, recoverBottomMap_smul_π₁₂,
            map_smul, hgen]
    | add a b ha hb =>
        rw [map_add, recoverBottomMap_add, ha, hb, recoverBottomMap_add, map_add]
  -- Hence `π₂^* g = h`.
  have hclaim2 : ∀ x, baseChangeMap (realC A).π₂ gLin x = h x := by
    intro x
    apply recoverBottomMap_injective A N
    rw [hEQ, hh_spec]
  -- Compare with the left face on the generators `recoverTopMap M m`.
  have hkey : ∀ m, baseChangeMap (realC A).π₂ gLin (recoverTopMap A M m) =
      baseChangeMap (realC A).π₂ f (recoverTopMap A M m) := by
    intro m
    rw [hclaim2, hleft, hg_spec]
  -- So `π₂^* g = π₂^* f`, whence `g = f`.
  have hbc : baseChangeMap (realC A).π₂ gLin = baseChangeMap (realC A).π₂ f :=
    linearMap_ext_of_eq_on_recoverTopMap A M hkey
  have hgf : ∀ m, gLin m = f m := by
    intro m
    apply oneTmulπ₂_injective A N.M
    rw [← baseChangeMap_π₂_oneTmulπ₂_linear, ← baseChangeMap_π₂_oneTmulπ₂_linear, hbc]
  -- Unravel the top face into the descent condition.
  have hfinal : ∀ m, recoverTopMap A N (f m) =
      baseChangeMap (realC A).π₂ f (recoverTopMap A M m) := by
    intro m
    rw [← hgf]
    exact hg_specL m
  exact @baseChange_linearMap_ext (realC A).R₁ (realC A).R₂ (π₂s (realC A) N.M) M.M
    _ _ (realC A).π₁.toAlgebra _ _ _ _
    (N.φ.toLinearMap ∘ₗ baseChangeMap (realC A).π₁ f)
    (baseChangeMap (realC A).π₂ f ∘ₗ M.φ.toLinearMap)
    (by
      intro m
      change N.φ (baseChangeMap (realC A).π₁ f (oneTmulπ₁ A M.M m)) =
        baseChangeMap (realC A).π₂ f (M.φ (oneTmulπ₁ A M.M m))
      have hL : N.φ (baseChangeMap (realC A).π₁ f (oneTmulπ₁ A M.M m)) =
          recoverTopMap A N (f m) := by
        rw [oneTmulπ₁_apply, baseChangeMap_tmul, recoverTopMap_apply, oneTmulπ₁_apply]
      rw [hL, ← recoverTopMap_apply]
      exact hfinal m)

/-- **Proposition 4.2.**  For every commutative ring `A`, the functor
`descentToIsocrystal A` from Novikov descent data to Novikov isocrystals is fully
faithful. -/
noncomputable def descentToIsocrystal_fullyFaithful :
    (descentToIsocrystal (Λ := Λ) A).FullyFaithful := by
  have hFull : (descentToIsocrystal (Λ := Λ) A).Full := by
    constructor
    intro M N F
    let f : M.M →ₗ[(realC A).R₁] N.M := F.toLinearMap
    have hf : ∀ m, descentFrobeniusToFun (Λ := Λ) A N (f m) =
        f (descentFrobeniusToFun (Λ := Λ) A M m) := F.commute_frobenius
    refine ⟨{ toLinearMap := f, commute_φ := descentToIsocrystal_full_aux A f hf }, ?_⟩
    apply NovikovIsocrystal.hom_ext
    rfl
  have hFaithful : (descentToIsocrystal (Λ := Λ) A).Faithful := by
    constructor
    intro M N f g hfg
    apply DescentDatum.hom_ext
    exact congr_arg NovikovIsocrystal.Hom.toLinearMap hfg
  letI := hFull
  letI := hFaithful
  exact Functor.FullyFaithful.ofFullyFaithful (descentToIsocrystal (Λ := Λ) A)

end MainProof

end Novikov.Descent
