import Novikov.Descent.Basic
import Novikov.Isocrystal.Basic
import Novikov.Miscellany.BaseChange
import Novikov.Series.Frobenius
import Mathlib.RingTheory.Flat.Basic
/-!
# From Novikov descent data to Novikov isocrystals

This file constructs the functor from real Novikov descent data to Novikov
isocrystals.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract

namespace Novikov.Descent

/-- The real-exponent Novikov cosimplicial ring used for descent data whose
level-one ring is `RealNovikovSeries A`. -/
noncomputable abbrev realC (A : Type*) [CommRing A] :=
  novikovCosimplicialRing (⊤ : AddSubgroup ℝ) A

section BaseChangeSemilinear

/-- Semilinear companion to base change: given a ring hom `f : R →+* S` and
an `S`-ring automorphism `σ` that fixes the image of `f`, the induced map
`s ⊗ m ↦ σ s ⊗ m` is a `σ`-semilinear automorphism of `S ⊗[R] M`. -/
noncomputable def baseChangeSemilinearSelf
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (σ σinv : S →+* S)
    [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    -- `_hσinv` is kept for interface symmetry; `TensorProduct.congr` derives the
    -- inverse from `RingHomInvPair`, so `σinv` fixing `f` is no longer needed here.
    (hσ : σ.comp f = f) (_hσinv : σinv.comp f = f)
    (M : Type*) [AddCommGroup M] [Module R M] :
    baseChange_along f M ≃ₛₗ[σ] baseChange_along f M := by
  letI : Algebra R S := f.toAlgebra
  -- `σ` fixes the image of `f = algebraMap`, so it is an `R`-algebra automorphism.
  let e : S ≃ₐ[R] S :=
    { toFun := σ
      invFun := σinv
      left_inv := fun s => RingHomInvPair.comp_apply_eq (σ := σ) (x := s)
      right_inv := fun s => RingHomInvPair.comp_apply_eq₂ (σ := σ) (x := s)
      map_mul' := σ.map_mul
      map_add' := σ.map_add
      commutes' := fun r => by change σ (f r) = f r; rw [← RingHom.comp_apply, hσ] }
  -- The `R`-linear bijection of `S ⊗[R] M` twisting the `S`-factor by `σ`;
  -- `TensorProduct.congr` supplies the inverse and the round-trip laws.
  let cR : (S ⊗[R] M) ≃ₗ[R] (S ⊗[R] M) :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)
  exact
    { toFun := cR
      invFun := cR.symm
      map_add' := cR.map_add
      left_inv := cR.left_inv
      right_inv := cR.right_inv
      map_smul' := fun s x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a m =>
            simp only [smul_tmul', smul_eq_mul, cR, TensorProduct.congr_tmul,
              AlgEquiv.toLinearEquiv_apply, LinearEquiv.refl_apply, map_mul]
            rfl
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }

@[simp]
lemma baseChangeSemilinearSelf_tmul
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (σ σinv : S →+* S)
    [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hσ : σ.comp f = f) (hσinv : σinv.comp f = f)
    (M : Type*) [AddCommGroup M] [Module R M]
    (s : S) (m : M) :
    baseChangeSemilinearSelf f σ σinv hσ hσinv M
      (letI : Algebra R S := f.toAlgebra; s ⊗ₜ[R] m) =
      (letI : Algebra R S := f.toAlgebra; σ s ⊗ₜ[R] m) := by
  simp [baseChangeSemilinearSelf]

/-- Naturality of `baseChangeSemilinearSelf` in the module variable. -/
lemma baseChangeSemilinearSelf_baseChangeMap
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (σ σinv : S →+* S)
    [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hσ : σ.comp f = f) (hσinv : σinv.comp f = f)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (x : baseChange_along f M) :
    baseChangeSemilinearSelf f σ σinv hσ hσinv N (baseChangeMap f φ x) =
      baseChangeMap f φ (baseChangeSemilinearSelf f σ σinv hσ hσinv M x) := by
  letI : Algebra R S := f.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp only [baseChangeMap_tmul, baseChangeSemilinearSelf_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `baseChange_assoc` intertwines the semilinear self-maps at the middle ring
`g` and at the composite `g ∘ f`, provided `σ` fixes the image of `g`. -/
lemma baseChangeSemilinearSelf_baseChange_assoc
    {R₁ R₂ R₃ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (f : R₁ →+* R₂) (g : R₂ →+* R₃)
    (σ σinv : R₃ →+* R₃) [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hσg : σ.comp g = g) (hσing : σinv.comp g = g)
    (hσgf : σ.comp (g.comp f) = g.comp f) (hσingf : σinv.comp (g.comp f) = g.comp f)
    (M : Type*) [AddCommGroup M] [Module R₁ M]
    (y : letI : Algebra R₁ R₂ := f.toAlgebra
         letI : Algebra R₂ R₃ := g.toAlgebra
         R₃ ⊗[R₂] (R₂ ⊗[R₁] M)) :
    letI : Algebra R₁ R₂ := f.toAlgebra
    letI : Algebra R₂ R₃ := g.toAlgebra
    letI : Algebra R₁ R₃ := (g.comp f).toAlgebra
    baseChangeSemilinearSelf (g.comp f) σ σinv hσgf hσingf M (baseChange_assoc f g M y) =
      baseChange_assoc f g M
        (baseChangeSemilinearSelf g σ σinv hσg hσing (R₂ ⊗[R₁] M) y) := by
  letI : Algebra R₁ R₂ := f.toAlgebra
  letI : Algebra R₂ R₃ := g.toAlgebra
  letI : Algebra R₁ R₃ := (g.comp f).toAlgebra
  induction y using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero]
  | tmul c z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, LinearEquiv.map_zero]
    | tmul b m =>
      simp only [baseChange_assoc_tmul, baseChangeSemilinearSelf_tmul]
      have hbc : σ (b • c) = b • σ c := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        exact congrFun (congrArg DFunLike.coe hσg) b
      rw [hbc]
    | add z₁ z₂ hz₁ hz₂ =>
      rw [TensorProduct.tmul_add, LinearEquiv.map_add, LinearEquiv.map_add,
        LinearEquiv.map_add, LinearEquiv.map_add, hz₁, hz₂]
  | add y₁ y₂ h₁ h₂ =>
    rw [LinearEquiv.map_add, LinearEquiv.map_add, LinearEquiv.map_add,
      LinearEquiv.map_add, h₁, h₂]

/-- The base change of an `R₂`-linear equivalence along `g` commutes with the
semilinear self-map at `g`. -/
lemma baseChangeSemilinearSelf_baseChange_comm
    {R₂ R₃ : Type*} [CommRing R₂] [CommRing R₃]
    (g : R₂ →+* R₃) (σ σinv : R₃ →+* R₃) [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hσg : σ.comp g = g) (hσing : σinv.comp g = g)
    {N P : Type*} [AddCommGroup N] [Module R₂ N] [AddCommGroup P] [Module R₂ P]
    (φ : N ≃ₗ[R₂] P)
    (y : letI : Algebra R₂ R₃ := g.toAlgebra; R₃ ⊗[R₂] N) :
    letI : Algebra R₂ R₃ := g.toAlgebra
    (LinearEquiv.baseChange R₂ R₃ N P φ)
        (baseChangeSemilinearSelf g σ σinv hσg hσing N y) =
      baseChangeSemilinearSelf g σ σinv hσg hσing P
        (LinearEquiv.baseChange R₂ R₃ N P φ y) := by
  letI : Algebra R₂ R₃ := g.toAlgebra
  induction y using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero]
  | tmul c v =>
    simp only [baseChangeSemilinearSelf_tmul, LinearEquiv.baseChange_tmul]
  | add a b ha hb =>
    rw [LinearEquiv.map_add, LinearEquiv.map_add, LinearEquiv.map_add,
      LinearEquiv.map_add, ha, hb]

/-- Naturality of the semilinear self-maps under the abstract `pullbackMap`,
provided `σ` fixes the image of the face map `g`. -/
lemma pullbackMap_baseChangeSemilinearSelf
    {R₁ R₂ R₃ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (f₁ f₂ : R₁ →+* R₂) (g : R₂ →+* R₃)
    {h₁ h₂ : R₁ →+* R₃} (hh₁ : g.comp f₁ = h₁) (hh₂ : g.comp f₂ = h₂)
    (σ σinv : R₃ →+* R₃) [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hσg : σ.comp g = g) (hσing : σinv.comp g = g)
    (hσ1 : σ.comp h₁ = h₁) (hσin1 : σinv.comp h₁ = h₁)
    (hσ2 : σ.comp h₂ = h₂) (hσin2 : σinv.comp h₂ = h₂)
    (M₁ : Type*) [AddCommGroup M₁] [Module R₁ M₁]
    (M₂ : Type*) [AddCommGroup M₂] [Module R₁ M₂]
    (φ : baseChange_along f₁ M₁ ≃ₗ[R₂] baseChange_along f₂ M₂)
    (x : baseChange_along h₁ M₁) :
    pullbackMap f₁ f₂ g hh₁ hh₂ M₁ M₂ φ
        (baseChangeSemilinearSelf h₁ σ σinv hσ1 hσin1 M₁ x) =
      baseChangeSemilinearSelf h₂ σ σinv hσ2 hσin2 M₂
        (pullbackMap f₁ f₂ g hh₁ hh₂ M₁ M₂ φ x) := by
  subst hh₁; subst hh₂
  letI : Algebra R₂ R₃ := g.toAlgebra
  have hpb : ∀ z, pullbackMap f₁ f₂ g rfl rfl M₁ M₂ φ z =
      baseChange_assoc f₂ g M₂
        ((LinearEquiv.baseChange R₂ R₃ (baseChange_along f₁ M₁) (baseChange_along f₂ M₂) φ)
          ((baseChange_assoc f₁ g M₁).symm z)) := fun z => rfl
  simp only [hpb]
  have hA : (baseChange_assoc f₁ g M₁).symm
        (baseChangeSemilinearSelf (g.comp f₁) σ σinv hσ1 hσin1 M₁ x) =
      baseChangeSemilinearSelf g σ σinv hσg hσing (baseChange_along f₁ M₁)
        ((baseChange_assoc f₁ g M₁).symm x) := by
    have h1 := baseChangeSemilinearSelf_baseChange_assoc f₁ g σ σinv hσg hσing hσ1 hσin1 M₁
      ((baseChange_assoc f₁ g M₁).symm x)
    rw [LinearEquiv.apply_symm_apply] at h1
    exact (LinearEquiv.symm_apply_eq _).mpr h1
  rw [hA, baseChangeSemilinearSelf_baseChange_comm g σ σinv hσg hσing φ,
    ← baseChangeSemilinearSelf_baseChange_assoc f₂ g σ σinv hσg hσing hσ2 hσin2 M₂]

end BaseChangeSemilinear

section FaceFrobenius

variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

noncomputable local instance : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
noncomputable local instance : Algebra (realC A).R₁ (realC A).R₃ := (realC A).ρ₃.toAlgebra

/-- Frobenius on the second variable of `A((t))((u))`: it fixes the first
coordinate and scales the second coordinate by `Λ`. -/
noncomputable def F2 : (realC A).R₂ →+* (realC A).R₂ :=
  coordinateFrobeniusRingHom (Λ := Λ) (R := A) (ι := Fin 2) (1 : Fin 2)

/-- Frobenius on the third variable of `A((t))((u))((v))`: it fixes the first
two coordinates and scales the third coordinate by `Λ`. -/
noncomputable def F3 : (realC A).R₃ →+* (realC A).R₃ :=
  coordinateFrobeniusRingHom (Λ := Λ) (R := A) (ι := Fin 3) (2 : Fin 3)

/-- Inverse to `F2`, scaling the second coordinate by `1 / Λ`. -/
noncomputable def F2Inv : (realC A).R₂ →+* (realC A).R₂ :=
  coordinateFrobeniusRingHomInv (Λ := Λ) (R := A) (ι := Fin 2) (1 : Fin 2)

/-- Inverse to `F3`, scaling the third coordinate by `1 / Λ`. -/
noncomputable def F3Inv : (realC A).R₃ →+* (realC A).R₃ :=
  coordinateFrobeniusRingHomInv (Λ := Λ) (R := A) (ι := Fin 3) (2 : Fin 3)

noncomputable instance : RingHomInvPair (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A) :=
  coordinateFrobeniusRingHom_invPair (Λ := Λ) (R := A) (ι := Fin 2) (1 : Fin 2)

noncomputable instance : RingHomInvPair (F2Inv (Λ := Λ) A) (F2 (Λ := Λ) A) :=
  coordinateFrobeniusRingHom_invPair_symm (Λ := Λ) (R := A) (ι := Fin 2) (1 : Fin 2)

noncomputable instance : RingHomInvPair (F3 (Λ := Λ) A) (F3Inv (Λ := Λ) A) :=
  coordinateFrobeniusRingHom_invPair (Λ := Λ) (R := A) (ι := Fin 3) (2 : Fin 3)

noncomputable instance : RingHomInvPair (F3Inv (Λ := Λ) A) (F3 (Λ := Λ) A) :=
  coordinateFrobeniusRingHom_invPair_symm (Λ := Λ) (R := A) (ι := Fin 3) (2 : Fin 3)

/-- Ring-level equalizer for `π₂ : R₁ → R₂` and the two maps
`π₁₃, π₂₃ : R₂ → R₃`. -/
lemma novikovCosimplicialRing_equalizer_π₂ (x : (realC A).R₂)
    (h : (realC A).π₁₃ x = (realC A).π₂₃ x) :
    ∃ y : (realC A).R₁, x = (realC A).π₂ y := by
  let yFun : (Unit → ↥(⊤ : AddSubgroup ℝ)) → A :=
    fun d => x.val (fun i : Fin 2 => if i = 0 then 0 else d ())
  have hy : isNovikovSeries yFun := by
    intro s hs C
    let s₂ : Fin 2 → ℝ := fun i => if i = 0 then 1 else s ()
    have hs₂ : ∀ i, 0 < s₂ i := by
      intro i
      by_cases hi : i = 0
      · simp [s₂, hi]
      · simp [s₂, hi, hs ()]
    let emb : (Unit → ↥(⊤ : AddSubgroup ℝ)) → (Fin 2 → ↥(⊤ : AddSubgroup ℝ)) :=
      fun d i => if i = 0 then 0 else d ()
    have hemb_inj : Function.Injective emb := by
      intro d₁ d₂ hEmb
      ext u
      fin_cases u
      have h1 := congr_fun hEmb 1
      simpa [emb] using h1
    have hfin := Set.Finite.preimage (fun _ _ _ _ hEmb => hemb_inj hEmb) (x.prop s₂ hs₂ C)
    refine hfin.subset ?_
    intro d hd
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    simp only [Set.mem_setOf_eq] at hd
    refine ⟨hd.1, ?_⟩
    have hsum : ∑ i, s₂ i * (emb d i : ℝ) = ∑ i, s i * (d i : ℝ) := by
      simp [s₂, emb]
    rw [hsum]
    exact hd.2
  let y : (realC A).R₁ := ⟨yFun, hy⟩
  refine ⟨y, ?_⟩
  apply NovikovSeries.ext
  intro d
  have coeff_eq : x.val d = if d 0 = 0 then x.val (fun i : Fin 2 => if i = 0 then 0 else d 1) else 0 := by
    let e : Fin 3 → ↥(⊤ : AddSubgroup ℝ) := fun k => if k = 0 then d 0 else if k = 1 then 0 else d 1
    have heq := congr_fun (congr_arg Subtype.val h) e
    rw [novikovCosimplicialRing_π₁₃_apply, novikovCosimplicialRing_π₂₃_apply] at heq
    have hleft : (fun i : Fin 2 => if i = 0 then d 0 else d 1) = d := by
      ext i
      fin_cases i <;> simp
    simpa [e, hleft] using heq
  rw [novikovCosimplicialRing_π₂_apply]
  exact coeff_eq

/-- The second face map `π₂ : R₁ → R₂` as an `R₁`-linear map, where `R₂`
is an `R₁`-module via `π₂`. -/
noncomputable def π₂Linear :=
  letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
  Algebra.linearMap (realC A).R₁ (realC A).R₂

/-- The face map `π₁₃ : R₂ → R₃` as an `R₁`-linear map, using `π₂` on `R₂`
and `ρ₃` on `R₃`. -/
noncomputable def π₁₃Linear :=
  letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
  letI : Algebra (realC A).R₁ (realC A).R₃ := (realC A).ρ₃.toAlgebra
  -- `π₁₃` is an `R₁`-algebra hom via `ρ₃ = π₁₃ ∘ π₂` (here non-definitional).
  AlgHom.toLinearMap
    ({ (realC A).π₁₃ with
        commutes' := fun r =>
          (congr_fun (congr_arg DFunLike.coe (realC A).ρ₃_eq_π₁₃_π₂) r).symm } :
      (realC A).R₂ →ₐ[(realC A).R₁] (realC A).R₃)

/-- The face map `π₂₃ : R₂ → R₃` as an `R₁`-linear map, using `π₂` on `R₂`
and `ρ₃` on `R₃`. -/
noncomputable def π₂₃Linear :=
  letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
  letI : Algebra (realC A).R₁ (realC A).R₃ := (realC A).ρ₃.toAlgebra
  -- `π₂₃` is an `R₁`-algebra hom: `ρ₃ = π₂₃ ∘ π₂` definitionally, so `commutes'` is `rfl`.
  AlgHom.toLinearMap
    ({ (realC A).π₂₃ with commutes' := fun _ => rfl } :
      (realC A).R₂ →ₐ[(realC A).R₁] (realC A).R₃)

/-- Difference of the two maps `π₁₃` and `π₂₃`. -/
noncomputable def π₁₃Subπ₂₃Linear :=
  π₁₃Linear (A := A) - π₂₃Linear (A := A)

lemma π₂Linear_exact_π₁₃Subπ₂₃Linear :
    Function.Exact (π₂Linear (A := A)) (π₁₃Subπ₂₃Linear (A := A)) := by
  intro x
  constructor
  · intro hx
    have hfaces : (realC A).π₁₃ x = (realC A).π₂₃ x := by
      have hx' := congr_arg Subtype.val hx
      change ((realC A).π₁₃ x).val - ((realC A).π₂₃ x).val = 0 at hx'
      apply NovikovSeries.ext
      intro d
      have hd := congr_fun hx' d
      simpa [Pi.sub_apply, sub_eq_zero] using hd
    rcases novikovCosimplicialRing_equalizer_π₂ (A := A) x hfaces with ⟨y, hy⟩
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    ext d
    have hρπ13 : (realC A).ρ₃ y = (realC A).π₁₃ ((realC A).π₂ y) :=
      congr_fun (congr_arg DFunLike.coe (realC A).ρ₃_eq_π₁₃_π₂) y
    have hfaces : (realC A).π₁₃ ((realC A).π₂ y) = (realC A).π₂₃ ((realC A).π₂ y) := by
      rw [← hρπ13]
      rfl
    have hd := congr_fun (congr_arg Subtype.val hfaces) d
    change ((realC A).π₁₃ ((realC A).π₂ y)).val d -
        ((realC A).π₂₃ ((realC A).π₂ y)).val d = 0
    rw [hd]
    simp

/-- The map `m ↦ 1 ⊗ m` into the pullback along `π₂`; this is Mathlib's
`TensorProduct.mk` at the unit `1`. -/
noncomputable def oneTmulπ₂ (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] :
    M →ₗ[(realC A).R₁] ((realC A).R₂ ⊗[(realC A).R₁] M) :=
  TensorProduct.mk (realC A).R₁ (realC A).R₂ M 1

@[simp]
lemma oneTmulπ₂_apply (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] (m : M) :
    oneTmulπ₂ (A := A) M m =
      (letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
       (1 : (realC A).R₂) ⊗ₜ[(realC A).R₁] m) := rfl

/-- The substitution `A((t,u)) → A((t))` merging both variables retracts `π₂`. -/
noncomputable def π₂Retract : (realC A).R₂ →+* (realC A).R₁ :=
  substituteRingHom (Γ := (⊤ : AddSubgroup ℝ)) (A := A) (fun _ : Fin 2 => ())

@[simp]
lemma π₂Retract_comp_π₂ :
    (π₂Retract (A := A)).comp (realC A).π₂ = RingHom.id (realC A).R₁ := by
  apply RingHom.ext
  intro f
  change substitute (fun _ : Fin 2 => ())
      (substitute (fun _ : Unit => (1 : Fin 2)) f) = f
  rw [← substitute_comp]
  simpa using substitute_id (Γ := (⊤ : AddSubgroup ℝ)) f

/-- The above retraction as an `R₁`-linear map, where `R₂` is an `R₁`-module via `π₂`. -/
noncomputable def π₂RetractLinear : (realC A).R₂ →ₗ[(realC A).R₁] (realC A).R₁ :=
  letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
  -- `π₂Retract` is an `R₁`-algebra hom via `π₂Retract ∘ π₂ = id`.
  AlgHom.toLinearMap
    ({ π₂Retract (A := A) with
        commutes' := fun r =>
          congr_fun (congr_arg DFunLike.coe (π₂Retract_comp_π₂ (A := A))) r } :
      (realC A).R₂ →ₐ[(realC A).R₁] (realC A).R₁)

@[simp]
lemma π₂RetractLinear_apply (x : (realC A).R₂) :
    π₂RetractLinear (A := A) x = π₂Retract (A := A) x := rfl

@[simp]
lemma π₂RetractLinear_rTensor_oneTmulπ₂ (M : Type*) [AddCommGroup M]
    [Module (realC A).R₁ M] (m : M) :
    (TensorProduct.lid (realC A).R₁ M)
      (((π₂RetractLinear (A := A)).rTensor M) ((oneTmulπ₂ (A := A) M) m)) = m := by
  rw [oneTmulπ₂_apply, LinearMap.rTensor_tmul, π₂RetractLinear_apply]
  have hπ : (π₂Retract (A := A)) (1 : (realC A).R₂) = 1 := (π₂Retract (A := A)).map_one
  rw [hπ, TensorProduct.lid_tmul]
  simp

lemma oneTmulπ₂_injective (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] :
    Function.Injective (oneTmulπ₂ (A := A) M) := by
  intro m n h
  have h' := congrArg
    (fun z => (TensorProduct.lid (realC A).R₁ M) (((π₂RetractLinear (A := A)).rTensor M) z)) h
  simpa using h'

/-- Module-level equalizer for `π₂` against `π₁₃` and `π₂₃`, after tensoring
with a flat (in particular projective) module: the equalizer is exactly the range
of `oneTmulπ₂`. This is the API used by the Frobenius descent construction. -/
theorem pi2_module_equalizer_oneTmul
    (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M]
    [Module.Flat (realC A).R₁ M]
    (x : (realC A).R₂ ⊗[(realC A).R₁] M)
    (h : ((π₁₃Linear (A := A)).rTensor M) x = ((π₂₃Linear (A := A)).rTensor M) x) :
    ∃ m : M, x = oneTmulπ₂ (A := A) M m := by
  have hdelta : ((π₁₃Subπ₂₃Linear (A := A)).rTensor M) x = 0 := by
    have hmap : (π₁₃Subπ₂₃Linear (A := A)).rTensor M =
        (π₁₃Linear (A := A)).rTensor M - (π₂₃Linear (A := A)).rTensor M := by
      ext r m
      simp [π₁₃Subπ₂₃Linear]
    rw [hmap]
    exact sub_eq_zero.mpr h
  have hExact := Module.Flat.rTensor_exact M (π₂Linear_exact_π₁₃Subπ₂₃Linear (A := A))
  rcases (hExact x).mp hdelta with ⟨z, hz⟩
  refine ⟨(TensorProduct.lid (realC A).R₁ M) z, ?_⟩
  rw [oneTmulπ₂_apply, ← hz]
  clear hz hdelta
  -- `π₂Linear.rTensor` sends `z` to `1 ⊗ lid z` (it is `algebraMap` on the left factor).
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      change (algebraMap (realC A).R₁ (realC A).R₂ r) ⊗ₜ[(realC A).R₁] m =
        (1 : (realC A).R₂) ⊗ₜ[(realC A).R₁] (r • m)
      rw [TensorProduct.tmul_smul]
      congr 1
      change (algebraMap (realC A).R₁ (realC A).R₂) r =
        (algebraMap (realC A).R₁ (realC A).R₂) r * 1
      rw [mul_one]
  | add x y hx hy =>
      simp only [map_add, hx, hy, TensorProduct.tmul_add]

section CoordinateFrobeniusCompat

variable {Λ : ℝ} [Fact (Λ > 0)]
variable (A : Type*) [CommRing A]

lemma pushExponents_eq_scaleCoordinate_iff_of_not_mem {ι ι' : Type*} [Fintype ι]
    [Fintype ι'] [DecidableEq ι'] {φ : ι → ι'} (j : ι') (hj : ∀ i, φ i ≠ j)
    (g : ι → ↥(⊤ : AddSubgroup ℝ)) (d : ι' → ↥(⊤ : AddSubgroup ℝ)) :
    pushExponents φ g = scaleCoordinate (Λ := Λ) j d ↔ pushExponents φ g = d := by
  constructor
  · intro h
    ext k
    by_cases hk : k = j
    · subst k
      have hpush : pushExponents φ g j = 0 :=
        Novikov.Descent.pushExponents_eq_zero_of_not_mem g j hj
      have hcoord := congr_fun h j
      rw [hpush] at hcoord
      have hreal : (d j : ℝ) / Λ = 0 := by
        simpa [scaleCoordinate] using congrArg Subtype.val hcoord.symm
      have hΛpos' : 0 < Λ := Fact.out
      field_simp [hΛpos'.ne'] at hreal
      have hd0 : (d j : ℝ) = 0 := by simpa using hreal
      rw [hpush]
      exact hd0.symm
    · simpa [scaleCoordinate, hk] using congr_fun h k
  · intro h
    ext k
    by_cases hk : k = j
    · subst k
      have hpush : pushExponents φ g j = 0 :=
        Novikov.Descent.pushExponents_eq_zero_of_not_mem g j hj
      have hdzero : (d j : ℝ) = 0 := by
        rw [← congr_fun h j]
        simp [hpush]
      rw [hpush]
      simp [scaleCoordinate, hdzero]
    · simpa [scaleCoordinate, hk] using congr_fun h k

lemma coordinateFrobenius_comp_substitute_of_not_mem {ι ι' : Type*} [Fintype ι]
    [Fintype ι'] [DecidableEq ι'] {φ : ι → ι'} (j : ι') (hj : ∀ i, φ i ≠ j) :
    (coordinateFrobeniusRingHom (Λ := Λ) (R := A) (ι := ι') j).comp
        (substituteRingHom (Γ := (⊤ : AddSubgroup ℝ)) (A := A) φ) =
      substituteRingHom (Γ := (⊤ : AddSubgroup ℝ)) (A := A) φ := by
  apply RingHom.ext
  intro f
  apply NovikovSeries.ext
  intro d
  change (substitute φ f).val (scaleCoordinate (Λ := Λ) j d) = (substitute φ f).val d
  simp only [substitute, substituteFun]
  apply Finset.sum_congr
  · ext g
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [pushExponents_eq_scaleCoordinate_iff_of_not_mem (Λ := Λ) j hj g d]
  · intro g _
    rfl

lemma coordinateFrobenius_comp_substitute_of_injective {ι ι' : Type*} [Fintype ι]
    [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] {φ : ι → ι'}
    (hφ : Function.Injective φ) (i : ι) :
    (coordinateFrobeniusRingHom (Λ := Λ) (R := A) (ι := ι') (φ i)).comp
        (substituteRingHom (Γ := (⊤ : AddSubgroup ℝ)) (A := A) φ) =
      (substituteRingHom (Γ := (⊤ : AddSubgroup ℝ)) (A := A) φ).comp
        (coordinateFrobeniusRingHom (Λ := Λ) (R := A) (ι := ι) i) := by
  apply RingHom.ext
  intro f
  apply NovikovSeries.ext
  intro d
  change (substitute φ f).val (scaleCoordinate (Λ := Λ) (φ i) d) =
    (substitute φ (coordinateFrobeniusRingHom (Λ := Λ) (R := A) (ι := ι) i f)).val d
  rw [Novikov.Descent.substitute_apply_of_injective (A := A) (φ := φ) (hφ := hφ) f
      (scaleCoordinate (Λ := Λ) (φ i) d),
    Novikov.Descent.substitute_apply_of_injective (A := A) (φ := φ) (hφ := hφ)
      (coordinateFrobeniusRingHom (Λ := Λ) (R := A) (ι := ι) i f) d]
  have hcond :
      (∀ j, (∀ k, φ k ≠ j) → scaleCoordinate (Λ := Λ) (φ i) d j = 0) ↔
        (∀ j, (∀ k, φ k ≠ j) → d j = 0) := by
    constructor
    · intro h j hj
      have hne : j ≠ φ i := fun hji => hj i hji.symm
      simpa [scaleCoordinate, hne] using h j hj
    · intro h j hj
      have hne : j ≠ φ i := fun hji => hj i hji.symm
      simpa [scaleCoordinate, hne] using h j hj
  by_cases hd : ∀ j, (∀ k, φ k ≠ j) → d j = 0
  · have hs : ∀ j, (∀ k, φ k ≠ j) → scaleCoordinate (Λ := Λ) (φ i) d j = 0 :=
      hcond.mpr hd
    rw [if_pos hs, if_pos hd]
    have harg : (fun k => scaleCoordinate (Λ := Λ) (φ i) d (φ k)) =
        scaleCoordinate (Λ := Λ) i (fun k => d (φ k)) := by
      ext k
      by_cases hk : k = i
      · subst k
        simp [scaleCoordinate]
      · have hne : φ k ≠ φ i := fun h => hk (hφ h)
        simp [scaleCoordinate, hk, hne]
    simp [coordinateFrobeniusRingHom_apply, harg]
  · have hs : ¬ ∀ j, (∀ k, φ k ≠ j) → scaleCoordinate (Λ := Λ) (φ i) d j = 0 :=
      fun hs => hd (hcond.mp hs)
    rw [if_neg hs, if_neg hd]

end CoordinateFrobeniusCompat

lemma ρ₁_eq_substitute : (realC A).ρ₁ =
    substituteRingHom (Γ := (⊤ : AddSubgroup ℝ)) (A := A) (fun _ : Unit => (0 : Fin 3)) := by
  apply RingHom.ext
  intro f
  change substituteRingHom Fin.castSucc (substituteRingHom (fun _ : Unit => (0 : Fin 2)) f) =
    substituteRingHom (fun _ : Unit => (0 : Fin 3)) f
  simp only [substituteRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← substitute_comp]
  rfl

lemma ρ₂_eq_substitute : (realC A).ρ₂ =
    substituteRingHom (Γ := (⊤ : AddSubgroup ℝ)) (A := A) (fun _ : Unit => (1 : Fin 3)) := by
  apply RingHom.ext
  intro f
  change substituteRingHom Fin.succ (substituteRingHom (fun _ : Unit => (0 : Fin 2)) f) =
    substituteRingHom (fun _ : Unit => (1 : Fin 3)) f
  simp only [substituteRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← substitute_comp]
  rfl

lemma π₁_eq_substitute : (realC A).π₁ =
    substituteRingHom (Γ := (⊤ : AddSubgroup ℝ)) (A := A) (fun _ : Unit => (0 : Fin 2)) := by
  simp [novikovCosimplicialRing, substituteRingHom]

/-- Compatibility: `F2` commutes with `π₁` because coordinate 1 is not hit
by the substitution `Unit → Fin 2` sending `()` to `0`. -/
lemma F2_comp_π₁_eq : (F2 (Λ := Λ) A).comp (realC A).π₁ = (realC A).π₁ := by
  rw [π₁_eq_substitute A]
  have h := coordinateFrobenius_comp_substitute_of_not_mem (Λ := Λ) (A := A)
    (j := (1 : Fin 2)) (hj := by intro i; fin_cases i; decide)
    (φ := fun _ : Unit => (0 : Fin 2))
  simpa only [F2] using h

lemma F2_comp_π₂_eq :
    (F2 (Λ := Λ) A).comp (realC A).π₂ =
      (realC A).π₂.comp (frobeniusRingHom (Λ := Λ) (A := A)) := by
  have h := coordinateFrobenius_comp_substitute_of_injective (Λ := Λ) (A := A)
    (φ := fun _ : Unit => (1 : Fin 2))
    (hφ := by intro x y _; cases x; cases y; rfl) ()
  simpa only [F2, realC, novikovCosimplicialRing,
    Novikov.coordinateFrobeniusRingHom_unit_eq (Λ := Λ) (A := A)] using h

lemma F3_comp_ρ₁_eq : (F3 (Λ := Λ) A).comp (realC A).ρ₁ = (realC A).ρ₁ := by
  rw [ρ₁_eq_substitute A]
  have h := coordinateFrobenius_comp_substitute_of_not_mem (Λ := Λ) (A := A)
    (j := (2 : Fin 3)) (hj := by intro i; fin_cases i; decide)
    (φ := fun _ : Unit => (0 : Fin 3))
  simpa only [F3] using h

lemma F3_comp_ρ₂_eq : (F3 (Λ := Λ) A).comp (realC A).ρ₂ = (realC A).ρ₂ := by
  rw [ρ₂_eq_substitute A]
  have h := coordinateFrobenius_comp_substitute_of_not_mem (Λ := Λ) (A := A)
    (j := (2 : Fin 3)) (hj := by intro i; fin_cases i; decide)
    (φ := fun _ : Unit => (1 : Fin 3))
  simpa only [F3] using h

lemma F3_comp_π₁₂_eq : (F3 (Λ := Λ) A).comp (realC A).π₁₂ = (realC A).π₁₂ := by
  have h := coordinateFrobenius_comp_substitute_of_not_mem (Λ := Λ) (A := A)
    (j := (2 : Fin 3)) (hj := fun i => by fin_cases i <;> decide)
    (φ := Fin.castSucc)
  simpa only [F3, realC, novikovCosimplicialRing] using h

lemma F3_comp_π₁₃_eq :
    (F3 (Λ := Λ) A).comp (realC A).π₁₃ =
      (realC A).π₁₃.comp (F2 (Λ := Λ) A) := by
  have h := coordinateFrobenius_comp_substitute_of_injective (Λ := Λ) (A := A)
    (φ := Fin.succAbove 1) (hφ := Fin.succAbove_right_injective) (1 : Fin 2)
  simpa only [F2, F3, realC, novikovCosimplicialRing] using h

lemma F3_comp_π₂₃_eq :
    (F3 (Λ := Λ) A).comp (realC A).π₂₃ =
      (realC A).π₂₃.comp (F2 (Λ := Λ) A) := by
  have h := coordinateFrobenius_comp_substitute_of_injective (Λ := Λ) (A := A)
    (φ := Fin.succ) (hφ := fun _ _ h => Fin.succ_injective _ h) (1 : Fin 2)
  simpa only [F2, F3, realC, novikovCosimplicialRing] using h

lemma F3Inv_comp_π₁₂_eq : (F3Inv (Λ := Λ) A).comp (realC A).π₁₂ = (realC A).π₁₂ := by
  have h := coordinateFrobenius_comp_substitute_of_not_mem (Λ := 1 / Λ) (A := A)
    (j := (2 : Fin 3)) (hj := fun i => by fin_cases i <;> decide)
    (φ := Fin.castSucc)
  simpa only [F3Inv, realC, novikovCosimplicialRing, coordinateFrobeniusRingHomInv] using h

lemma F2Inv_comp_π₁_eq : (F2Inv (Λ := Λ) A).comp (realC A).π₁ = (realC A).π₁ := by
  rw [π₁_eq_substitute A]
  have h := coordinateFrobenius_comp_substitute_of_not_mem (Λ := 1 / Λ) (A := A)
    (j := (1 : Fin 2)) (hj := by intro i; fin_cases i; decide)
    (φ := fun _ : Unit => (0 : Fin 2))
  simpa only [F2Inv, coordinateFrobeniusRingHomInv] using h

lemma F3Inv_comp_ρ₁_eq : (F3Inv (Λ := Λ) A).comp (realC A).ρ₁ = (realC A).ρ₁ := by
  rw [ρ₁_eq_substitute A]
  have h := coordinateFrobenius_comp_substitute_of_not_mem (Λ := 1 / Λ) (A := A)
    (j := (2 : Fin 3)) (hj := by intro i; fin_cases i; decide)
    (φ := fun _ : Unit => (0 : Fin 3))
  simpa only [F3Inv, coordinateFrobeniusRingHomInv] using h

lemma F3Inv_comp_ρ₂_eq : (F3Inv (Λ := Λ) A).comp (realC A).ρ₂ = (realC A).ρ₂ := by
  rw [ρ₂_eq_substitute A]
  have h := coordinateFrobenius_comp_substitute_of_not_mem (Λ := 1 / Λ) (A := A)
    (j := (2 : Fin 3)) (hj := by intro i; fin_cases i; decide)
    (φ := fun _ : Unit => (1 : Fin 3))
  simpa only [F3Inv, coordinateFrobeniusRingHomInv] using h

end FaceFrobenius

section FMDefinitions

variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

/-- Frobenius on `π₂^* M` (conjugate `id ⊗ F₂` on `π₁^* M` by the descent
cocycle). -/
noncomputable def FM2 (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) :
    π₂s (realC A) M.M ≃ₛₗ[F2 (Λ := Λ) (A := A)] π₂s (realC A) M.M :=
  letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
  let F_sl : π₁s (realC A) M.M ≃ₛₗ[F2 (Λ := Λ) (A := A)] π₁s (realC A) M.M :=
    baseChangeSemilinearSelf (realC A).π₁ (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
      (F2_comp_π₁_eq (Λ := Λ) A) (F2Inv_comp_π₁_eq (Λ := Λ) A) M.M
  ((LinearEquiv.symm M.φ).trans F_sl).trans M.φ

/-- Pointwise form of `FM2`, used to keep heavier face compatibility lemmas from
asking the kernel to unfold `FM2` while also checking a generic theorem
application. -/
lemma FM2_apply (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (x : π₂s (realC A) M.M) :
    FM2 (Λ := Λ) A M x =
      (((M.φ.symm.trans
        (baseChangeSemilinearSelf (realC A).π₁ (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
          (F2_comp_π₁_eq (Λ := Λ) A) (F2Inv_comp_π₁_eq (Λ := Λ) A) M.M)).trans
        M.φ) x) :=
  rfl

/-- Frobenius on `ρ₃^* M` constructed via `pullbackMap_13`. -/
noncomputable def FM3_13 (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) :
    ρ₃s (realC A) M.M ≃ₛₗ[F3 (Λ := Λ) (A := A)] ρ₃s (realC A) M.M :=
  ((LinearEquiv.symm (pullbackMap_13 (realC A) M.M M.φ)).trans
    (baseChangeSemilinearSelf (realC A).ρ₁ (F3 (Λ := Λ) A) (F3Inv (Λ := Λ) A)
      (F3_comp_ρ₁_eq (Λ := Λ) A) (F3Inv_comp_ρ₁_eq (Λ := Λ) A) M.M)).trans
    (pullbackMap_13 (realC A) M.M M.φ)

/-- Frobenius on `ρ₃^* M` constructed via `pullbackMap_23`. -/
noncomputable def FM3_23 (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) :
    ρ₃s (realC A) M.M ≃ₛₗ[F3 (Λ := Λ) (A := A)] ρ₃s (realC A) M.M :=
  ((LinearEquiv.symm (pullbackMap_23 (realC A) M.M M.φ)).trans
    (baseChangeSemilinearSelf (realC A).ρ₂ (F3 (Λ := Λ) A) (F3Inv (Λ := Λ) A)
      (F3_comp_ρ₂_eq (Λ := Λ) A) (F3Inv_comp_ρ₂_eq (Λ := Λ) A) M.M)).trans
    (pullbackMap_23 (realC A) M.M M.φ)

-- Treat the heavy base-change constructions as opaque while unfolding the
-- conjugation: `whnf`/the kernel then only reduces the `LinearEquiv.trans`
-- coercion instead of chasing into the tensor/Frobenius bodies.
attribute [local irreducible] baseChangeSemilinearSelf pullbackMap_13 pullbackMap_23

/-- Pointwise form of `FM3_13`, isolating the (heavy) unfolding of the
conjugation into its own declaration. -/
lemma FM3_13_apply (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (y : ρ₃s (realC A) M.M) :
    FM3_13 (Λ := Λ) A M y =
      pullbackMap_13 (realC A) M.M M.φ
        (baseChangeSemilinearSelf (realC A).ρ₁ (F3 (Λ := Λ) A) (F3Inv (Λ := Λ) A)
          (F3_comp_ρ₁_eq (Λ := Λ) A) (F3Inv_comp_ρ₁_eq (Λ := Λ) A) M.M
          ((pullbackMap_13 (realC A) M.M M.φ).symm y)) :=
  (LinearEquiv.trans_apply y).trans (congrArg _ (LinearEquiv.trans_apply y))

/-- Pointwise form of `FM3_23`. -/
lemma FM3_23_apply (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (y : ρ₃s (realC A) M.M) :
    FM3_23 (Λ := Λ) A M y =
      pullbackMap_23 (realC A) M.M M.φ
        (baseChangeSemilinearSelf (realC A).ρ₂ (F3 (Λ := Λ) A) (F3Inv (Λ := Λ) A)
          (F3_comp_ρ₂_eq (Λ := Λ) A) (F3Inv_comp_ρ₂_eq (Λ := Λ) A) M.M
          ((pullbackMap_23 (realC A) M.M M.φ).symm y)) :=
  (LinearEquiv.trans_apply y).trans (congrArg _ (LinearEquiv.trans_apply y))

-- Restore reducibility: the equalizer assembly below relies on `pullbackMap_12`
-- unfolding (in `hnat`) and produces a leaner term without the opaque marking.
attribute [local semireducible] baseChangeSemilinearSelf pullbackMap_13 pullbackMap_23

/-- Naturality: `φ₁₂` intertwines the Frobenius self-maps on `ρ₁^*` and `ρ₂^*`,
for any face-fixing semilinear `σ`.  Stated generically over `C` so the (heavy)
kernel check involves no concrete cosimplicial-ring structure. -/
lemma pullbackMap_12_frob {C : CosimplicialRing}
    (σ σinv : C.R₃ →+* C.R₃) [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hπ12 : σ.comp C.π₁₂ = C.π₁₂) (hπ12i : σinv.comp C.π₁₂ = C.π₁₂)
    (hρ1 : σ.comp C.ρ₁ = C.ρ₁) (hρ1i : σinv.comp C.ρ₁ = C.ρ₁)
    (hρ2 : σ.comp C.ρ₂ = C.ρ₂) (hρ2i : σinv.comp C.ρ₂ = C.ρ₂)
    (M : Type*) [AddCommGroup M] [Module C.R₁ M]
    (φ : π₁s C M ≃ₗ[C.R₂] π₂s C M)
    (w : ρ₁s C M) :
    pullbackMap_12 C M φ (baseChangeSemilinearSelf C.ρ₁ σ σinv hρ1 hρ1i M w) =
      baseChangeSemilinearSelf C.ρ₂ σ σinv hρ2 hρ2i M (pullbackMap_12 C M φ w) :=
  pullbackMap_baseChangeSemilinearSelf C.π₁ C.π₂ C.π₁₂
    C.ρ₁_eq_π₁₂_π₁.symm C.ρ₂_eq_π₁₂_π₂.symm σ σinv hπ12 hπ12i hρ1 hρ1i hρ2 hρ2i M M φ w

/-- Generic conjugation chain underlying `FM3_13 = FM3_23`, stated over an
abstract cosimplicial ring `C` and a face-fixing semilinear `σ`.  Proving it
generically keeps the concrete `novikovCosimplicialRing` projections out of the
kernel reduction triggered by `pullbackMap_12_frob`.

The argument is `cocycle_symm` (rewrites `φ₁₃⁻¹` as `φ₁₂⁻¹ φ₂₃⁻¹`), then the
cocycle `φ₁₃ = φ₂₃ φ₁₂`, then `pullbackMap_12_frob` to slide the Frobenius
self-map across `φ₁₂`, and finally `φ₁₂ φ₁₂⁻¹ = id`. -/
lemma FM3_13_eq_FM3_23_generic {C : CosimplicialRing}
    (σ σinv : C.R₃ →+* C.R₃) [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hπ12 : σ.comp C.π₁₂ = C.π₁₂) (hπ12i : σinv.comp C.π₁₂ = C.π₁₂)
    (hρ1 : σ.comp C.ρ₁ = C.ρ₁) (hρ1i : σinv.comp C.ρ₁ = C.ρ₁)
    (hρ2 : σ.comp C.ρ₂ = C.ρ₂) (hρ2i : σinv.comp C.ρ₂ = C.ρ₂)
    (M : DescentDatum C) (y : ρ₃s C M.M) :
    pullbackMap_13 C M.M M.φ
      (baseChangeSemilinearSelf C.ρ₁ σ σinv hρ1 hρ1i M.M
        ((pullbackMap_13 C M.M M.φ).symm y)) =
    pullbackMap_23 C M.M M.φ
      (baseChangeSemilinearSelf C.ρ₂ σ σinv hρ2 hρ2i M.M
        ((pullbackMap_23 C M.M M.φ).symm y)) := by
  rw [← M.cocycle_symm y]
  have hcoc := congrFun M.cocycle
    (baseChangeSemilinearSelf C.ρ₁ σ σinv hρ1 hρ1i M.M
      ((pullbackMap_12 C M.M M.φ).symm ((pullbackMap_23 C M.M M.φ).symm y)))
  simp only [Function.comp_apply, LinearEquiv.coe_coe] at hcoc
  rw [← hcoc, pullbackMap_12_frob σ σinv hπ12 hπ12i hρ1 hρ1i hρ2 hρ2i M.M M.φ,
      (pullbackMap_12 C M.M M.φ).apply_symm_apply]

-- Apply the generic chain at `realC A` with the heavy bodies opaque, so the
-- `exact` matches `FM3_13_eq_FM3_23_generic`'s conclusion syntactically (~25s → fast).
attribute [local irreducible] baseChangeSemilinearSelf pullbackMap_13 pullbackMap_23

lemma FM3_13_eq_FM3_23 (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) :
    FM3_13 (Λ := Λ) A M = FM3_23 (Λ := Λ) A M := by
  ext y
  rw [FM3_13_apply, FM3_23_apply]
  exact FM3_13_eq_FM3_23_generic (F3 (Λ := Λ) A) (F3Inv (Λ := Λ) A)
    (F3_comp_π₁₂_eq (Λ := Λ) A) (F3Inv_comp_π₁₂_eq (Λ := Λ) A)
    (F3_comp_ρ₁_eq (Λ := Λ) A) (F3Inv_comp_ρ₁_eq (Λ := Λ) A)
    (F3_comp_ρ₂_eq (Λ := Λ) A) (F3Inv_comp_ρ₂_eq (Λ := Λ) A) M y

attribute [local semireducible] baseChangeSemilinearSelf pullbackMap_13 pullbackMap_23


/-- The Frobenius on `ρ₃^* M`; uses the `_13` construction. -/
noncomputable def FM3 (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) :
    ρ₃s (realC A) M.M ≃ₛₗ[F3 (Λ := Λ) (A := A)] ρ₃s (realC A) M.M :=
  FM3_13 (Λ := Λ) A M

end FMDefinitions

section NatExt

variable {R₁ R₂ R₃ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₃]

/-- Scalar extension `baseChange_along f M → baseChange_along h M`
along `g` (where `h = g.comp f`), sending `s ⊗ m ↦ g s ⊗ m`.  The middle map is
`g` viewed as an `R₁`-linear map (`R₂` an `R₁`-module via `f`, `R₃` via `g.comp f`). -/
noncomputable def natExt (f : R₁ →+* R₂) (g : R₂ →+* R₃)
    {h : R₁ →+* R₃} (hh : g.comp f = h)
    (M : Type*) [AddCommGroup M] [Module R₁ M] :
    baseChange_along f M →ₗ[R₁] baseChange_along h M := by
  subst hh
  letI : Algebra R₁ R₂ := f.toAlgebra
  letI : Algebra R₁ R₃ := (g.comp f).toAlgebra
  -- `g` is automatically an `R₁`-algebra hom (`commutes'` is `rfl` here), so its
  -- underlying `R₁`-linear map is `AlgHom.toLinearMap`.
  exact LinearMap.rTensor M
    (({ g with commutes' := fun _ => rfl } : R₂ →ₐ[R₁] R₃).toLinearMap)

@[simp]
lemma natExt_tmul (f : R₁ →+* R₂) (g : R₂ →+* R₃)
    {h : R₁ →+* R₃} (hh : g.comp f = h)
    (M : Type*) [AddCommGroup M] [Module R₁ M] (s : R₂) (m : M) :
    natExt f g hh M (letI : Algebra R₁ R₂ := f.toAlgebra; s ⊗ₜ[R₁] m) =
      (letI : Algebra R₁ R₃ := h.toAlgebra; g s ⊗ₜ[R₁] m) := by
  subst hh
  rfl

/-- `natExt` intertwines the semilinear self-maps `τ` (at `R₂`) and `σ` (at
`R₃`) when `g` intertwines them, i.e. `σ.comp g = g.comp τ`. -/
lemma natExt_baseChangeSemilinearSelf
    (f : R₁ →+* R₂) (g : R₂ →+* R₃)
    (τ τinv : R₂ →+* R₂) (σ σinv : R₃ →+* R₃)
    [RingHomInvPair τ τinv] [RingHomInvPair τinv τ]
    [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    {h : R₁ →+* R₃} (hh : g.comp f = h)
    (hτ : τ.comp f = f) (hτinv : τinv.comp f = f)
    (hσ : σ.comp h = h) (hσinv : σinv.comp h = h)
    (hcompat : σ.comp g = g.comp τ)
    (M : Type*) [AddCommGroup M] [Module R₁ M]
    (w : baseChange_along f M) :
    natExt f g hh M (baseChangeSemilinearSelf f τ τinv hτ hτinv M w) =
      baseChangeSemilinearSelf h σ σinv hσ hσinv M (natExt f g hh M w) := by
  subst hh
  letI : Algebra R₁ R₂ := f.toAlgebra
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      rw [baseChangeSemilinearSelf_tmul, natExt_tmul, natExt_tmul,
          baseChangeSemilinearSelf_tmul]
      congr 1
      exact (congrFun (congrArg DFunLike.coe hcompat) s).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `natExt` is `baseChange_assoc` applied to the unit `w ↦ 1 ⊗ w`. -/
lemma natExt_eq_assoc (f : R₁ →+* R₂) (g : R₂ →+* R₃)
    (M : Type*) [AddCommGroup M] [Module R₁ M]
    (w : baseChange_along f M) :
    natExt f g rfl M w =
      (letI : Algebra R₁ R₂ := f.toAlgebra
       letI : Algebra R₂ R₃ := g.toAlgebra
       baseChange_assoc f g M (1 ⊗ₜ[R₂] w)) := by
  letI : Algebra R₁ R₂ := f.toAlgebra
  letI : Algebra R₂ R₃ := g.toAlgebra
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      rw [natExt_tmul, baseChange_assoc_tmul]
      congr 1
      rw [Algebra.smul_def, mul_one]
      rfl
  | add x y hx hy =>
      rw [map_add, hx, hy, TensorProduct.tmul_add, map_add]

/-- Naturality of `pullbackMap` with respect to `natExt`: pulling back `φ` along
`g` intertwines the scalar extensions `natExt f₁ g` and `natExt f₂ g`. -/
lemma pullbackMap_natExt
    (f₁ f₂ : R₁ →+* R₂) (g : R₂ →+* R₃)
    {h₁ h₂ : R₁ →+* R₃} (hh₁ : g.comp f₁ = h₁) (hh₂ : g.comp f₂ = h₂)
    (M : Type*) [AddCommGroup M] [Module R₁ M]
    (φ : baseChange_along f₁ M ≃ₗ[R₂] baseChange_along f₂ M)
    (w : baseChange_along f₁ M) :
    pullbackMap f₁ f₂ g hh₁ hh₂ M M φ (natExt f₁ g hh₁ M w) =
      natExt f₂ g hh₂ M (φ w) := by
  subst hh₁ hh₂
  rw [natExt_eq_assoc f₁ g M, natExt_eq_assoc f₂ g M]
  simp only [pullbackMap, LinearEquiv.trans_apply,
             LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul]

/-- Generic compatibility of a face scalar-extension `natExt π₂ g` with the
conjugated Frobenius self-maps.  Specialises (via `g := π₁₃` or `g := π₂₃`) to
`face13_FM2`/`face23_FM2`.  `τ` is the Frobenius on `R₂` and `σ` on `R₃`, with
`g` intertwining them. -/
lemma natExt_FM_generic {C : CosimplicialRing}
    (M : DescentDatum C)
    (g : C.R₂ →+* C.R₃)
    {ρa : C.R₁ →+* C.R₃} (hgπ₁ : g.comp C.π₁ = ρa) (hgπ₂ : g.comp C.π₂ = C.ρ₃)
    (τ τinv : C.R₂ →+* C.R₂) (σ σinv : C.R₃ →+* C.R₃)
    [RingHomInvPair τ τinv] [RingHomInvPair τinv τ]
    [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hτπ₁ : τ.comp C.π₁ = C.π₁) (hτπ₁inv : τinv.comp C.π₁ = C.π₁)
    (hσρa : σ.comp ρa = ρa) (hσρainv : σinv.comp ρa = ρa)
    (hcompat : σ.comp g = g.comp τ)
    (x : π₂s C M.M) :
    natExt C.π₂ g hgπ₂ M.M
        (((M.φ.symm.trans
            (baseChangeSemilinearSelf C.π₁ τ τinv hτπ₁ hτπ₁inv M.M)).trans M.φ) x) =
      pullbackMap C.π₁ C.π₂ g hgπ₁ hgπ₂ M.M M.M M.φ
        (baseChangeSemilinearSelf ρa σ σinv hσρa hσρainv M.M
          ((pullbackMap C.π₁ C.π₂ g hgπ₁ hgπ₂ M.M M.M M.φ).symm
            (natExt C.π₂ g hgπ₂ M.M x))) := by
  have hkey : natExt C.π₁ g hgπ₁ M.M (M.φ.symm x) =
      (pullbackMap C.π₁ C.π₂ g hgπ₁ hgπ₂ M.M M.M M.φ).symm
        (natExt C.π₂ g hgπ₂ M.M x) := by
    apply (pullbackMap C.π₁ C.π₂ g hgπ₁ hgπ₂ M.M M.M M.φ).injective
    rw [pullbackMap_natExt]
    simp only [LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      ← pullbackMap_natExt C.π₁ C.π₂ g hgπ₁ hgπ₂ M.M M.φ,
      natExt_baseChangeSemilinearSelf C.π₁ g τ τinv σ σinv hgπ₁ hτπ₁ hτπ₁inv
        hσρa hσρainv hcompat M.M,
      hkey]

/-- The `π₁₃`-face specialisation of `natExt_FM_generic`, stated with the
`pullbackMap_13` wrapper folded (rather than the bare `pullbackMap C.π₁ C.π₂ π₁₃`).
Because this lemma is *generic* over `C` (no concrete `novikovCosimplicialRing`),
the definitional bridge `pullbackMap_13 ≡ pullbackMap` is discharged here with no
`realC A` reduction.  At a concrete call site the conclusion's `pullbackMap_13`
head then matches the goal structurally, so the kernel never whnf-reduces the
heavy tensor bodies (which is what causes the deterministic timeout). -/
lemma natExt_FM13 {C : CosimplicialRing} (M : DescentDatum C)
    (τ τinv : C.R₂ →+* C.R₂) (σ σinv : C.R₃ →+* C.R₃)
    [RingHomInvPair τ τinv] [RingHomInvPair τinv τ]
    [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hτπ₁ : τ.comp C.π₁ = C.π₁) (hτπ₁inv : τinv.comp C.π₁ = C.π₁)
    (hσρ₁ : σ.comp C.ρ₁ = C.ρ₁) (hσρ₁inv : σinv.comp C.ρ₁ = C.ρ₁)
    (hcompat : σ.comp C.π₁₃ = C.π₁₃.comp τ)
    (x : π₂s C M.M) :
    (natExt C.π₂ C.π₁₃ C.ρ₃_eq_π₁₃_π₂.symm M.M)
        (((M.φ.symm.trans
            (baseChangeSemilinearSelf C.π₁ τ τinv hτπ₁ hτπ₁inv M.M)).trans M.φ) x) =
      pullbackMap_13 C M.M M.φ
        ((baseChangeSemilinearSelf C.ρ₁ σ σinv hσρ₁ hσρ₁inv M.M)
          ((pullbackMap_13 C M.M M.φ).symm
            ((natExt C.π₂ C.π₁₃ C.ρ₃_eq_π₁₃_π₂.symm M.M) x))) :=
  natExt_FM_generic M C.π₁₃ C.ρ₁_eq_π₁₃_π₁.symm C.ρ₃_eq_π₁₃_π₂.symm
    τ τinv σ σinv hτπ₁ hτπ₁inv hσρ₁ hσρ₁inv hcompat x

/-- The `π₂₃`-face specialisation of `natExt_FM_generic`, stated with the
`pullbackMap_23` wrapper folded. -/
lemma natExt_FM23 {C : CosimplicialRing} (M : DescentDatum C)
    (τ τinv : C.R₂ →+* C.R₂) (σ σinv : C.R₃ →+* C.R₃)
    [RingHomInvPair τ τinv] [RingHomInvPair τinv τ]
    [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hτπ₁ : τ.comp C.π₁ = C.π₁) (hτπ₁inv : τinv.comp C.π₁ = C.π₁)
    (hσρ₂ : σ.comp C.ρ₂ = C.ρ₂) (hσρ₂inv : σinv.comp C.ρ₂ = C.ρ₂)
    (hcompat : σ.comp C.π₂₃ = C.π₂₃.comp τ)
    (x : π₂s C M.M) :
    (natExt C.π₂ C.π₂₃ C.ρ₃_eq_π₂₃_π₂.symm M.M)
        (((M.φ.symm.trans
            (baseChangeSemilinearSelf C.π₁ τ τinv hτπ₁ hτπ₁inv M.M)).trans M.φ) x) =
      pullbackMap_23 C M.M M.φ
        ((baseChangeSemilinearSelf C.ρ₂ σ σinv hσρ₂ hσρ₂inv M.M)
          ((pullbackMap_23 C M.M M.φ).symm
            ((natExt C.π₂ C.π₂₃ C.ρ₃_eq_π₂₃_π₂.symm M.M) x))) :=
  natExt_FM_generic M C.π₂₃ C.ρ₂_eq_π₂₃_π₁.symm C.ρ₃_eq_π₂₃_π₂.symm
    τ τinv σ σinv hτπ₁ hτπ₁inv hσρ₂ hσρ₂inv hcompat x

end NatExt

section DescentFrobenius

variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

noncomputable local instance : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
noncomputable local instance : Algebra (realC A).R₁ (realC A).R₃ := (realC A).ρ₃.toAlgebra

/-- `π₁₃^*` as a linear map `π₂s M → ρ₃s M`, using the algebra structures
from `π₂` and `ρ₃`. -/
noncomputable def π₁₃star (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] :
    π₂s (realC A) M →ₗ[(realC A).R₁] ρ₃s (realC A) M :=
  (π₁₃Linear (A := A)).rTensor M

/-- `π₂₃^*` as a linear map `π₂s M → ρ₃s M`. -/
noncomputable def π₂₃star (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] :
    π₂s (realC A) M →ₗ[(realC A).R₁] ρ₃s (realC A) M :=
  (π₂₃Linear (A := A)).rTensor M

/-- `π₁₃^*` is the scalar extension `natExt` along `π₁₃`. -/
lemma π₁₃star_eq_natExt (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] :
    π₁₃star A M = natExt (realC A).π₂ (realC A).π₁₃ (realC A).ρ₃_eq_π₁₃_π₂.symm M := by
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      simp only [π₁₃star, π₁₃Linear, LinearMap.rTensor_tmul, natExt_tmul,
        AlgHom.toLinearMap_apply, AlgHom.coe_mk]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `π₂₃^*` is the scalar extension `natExt` along `π₂₃`. -/
lemma π₂₃star_eq_natExt (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] :
    π₂₃star A M = natExt (realC A).π₂ (realC A).π₂₃ (realC A).ρ₃_eq_π₂₃_π₂.symm M := by
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      simp only [π₂₃star, π₂₃Linear, LinearMap.rTensor_tmul, natExt_tmul,
        AlgHom.toLinearMap_apply, AlgHom.coe_mk]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private lemma oneTmulπ₂_faces (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] (m : M) :
    (π₁₃star A M) (oneTmulπ₂ (A := A) M m) =
      (π₂₃star A M) (oneTmulπ₂ (A := A) M m) := by
  rw [π₁₃star_eq_natExt, π₂₃star_eq_natExt, oneTmulπ₂_apply]
  simp only [natExt_tmul, map_one]

-- Treat the heavy base-change / pullback / scalar-extension constructions as
-- opaque while specialising `natExt_FM13`/`natExt_FM23` to `realC A`: the
-- generic conclusion then matches the wrapped statement *syntactically*, so the
-- unifier never unfolds the tensor/Frobenius bodies (which otherwise costs ~30s
-- per `exact`).
attribute [local irreducible] baseChangeSemilinearSelf pullbackMap_13 pullbackMap_23 natExt

/-- Application of the generic `natExt_FM13` at the concrete `realC A`, stated in
the *wrapped* form produced by `π₁₃star_eq_natExt`/`FM3_13_apply` (with `FM2` and
`pullbackMap_13`).  Isolated in its own declaration: the diagnostic build showed
that this application and the rewrite stack of `face13_FM2` are each individually
under the heartbeat budget, but their combination in a single declaration is not.
There is no residual `FM2` unfolding in the statement: that small bridge is kept
in `FM2_apply`, so this declaration checks the generic theorem application
without simultaneously reducing the concrete Novikov face machinery. -/
private lemma face13_FM2_app (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (x : π₂s (realC A) M.M) :
    (natExt (realC A).π₂ (realC A).π₁₃ (realC A).ρ₃_eq_π₁₃_π₂.symm M.M)
        ((((M.φ.symm.trans
          (baseChangeSemilinearSelf (realC A).π₁ (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
            (F2_comp_π₁_eq (Λ := Λ) A) (F2Inv_comp_π₁_eq (Λ := Λ) A) M.M)).trans
          M.φ) x)) =
      pullbackMap_13 (realC A) M.M M.φ
        ((baseChangeSemilinearSelf (realC A).ρ₁ (F3 (Λ := Λ) A) (F3Inv (Λ := Λ) A)
            (F3_comp_ρ₁_eq (Λ := Λ) A) (F3Inv_comp_ρ₁_eq (Λ := Λ) A) M.M)
          ((pullbackMap_13 (realC A) M.M M.φ).symm
            ((natExt (realC A).π₂ (realC A).π₁₃ (realC A).ρ₃_eq_π₁₃_π₂.symm M.M) x))) :=
  natExt_FM13 M (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A) (F3 (Λ := Λ) A)
    (F3Inv (Λ := Λ) A) (F2_comp_π₁_eq (Λ := Λ) A) (F2Inv_comp_π₁_eq (Λ := Λ) A)
    (F3_comp_ρ₁_eq (Λ := Λ) A) (F3Inv_comp_ρ₁_eq (Λ := Λ) A)
    (F3_comp_π₁₃_eq (Λ := Λ) A) x

/-- Compatibility: `π₁₃^* ∘ FM2 = FM3 ∘ π₁₃^*`.

Proof sketch:
1. Both sides are `F3`-semilinear maps `π₂s M → ρ₃s M`.
2. Unfold `FM2 = M.φ ∘ T₂_pi ∘ M.φ.symm` where `T₂_pi = baseChangeSemilinearSelf π₁ F2 ...`.
3. Unfold `FM3_13 = φ13 ∘ T₁_rho ∘ φ13.symm` where `φ13 = pullbackMap_13 M.φ`.
4. The key commutativity is packaged generically in `natExt_FM13` and specialised
   to `realC A` in `face13_FM2_app`; here we only do the light wrapper rewrites
   and close with an opaque constant (so the kernel never re-checks the
   heavy application together with the rewrite stack — that combination is what
   triggers the deterministic timeout). -/
private lemma face13_FM2 (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (x : π₂s (realC A) M.M) :
    (π₁₃star A M.M) (FM2 (Λ := Λ) A M x) =
    FM3 (Λ := Λ) A M ((π₁₃star A M.M) x) := by
  rw [π₁₃star_eq_natExt]
  simp only [FM3]
  rw [FM3_13_apply]
  rw [FM2_apply]
  exact face13_FM2_app A M x

/-- Application of the generic `natExt_FM23` at the concrete `realC A`, with the
`FM2` unfolding kept out of the theorem application as in `face13_FM2_app`. -/
private lemma face23_FM2_app (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (x : π₂s (realC A) M.M) :
    (natExt (realC A).π₂ (realC A).π₂₃ (realC A).ρ₃_eq_π₂₃_π₂.symm M.M)
        ((((M.φ.symm.trans
          (baseChangeSemilinearSelf (realC A).π₁ (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
            (F2_comp_π₁_eq (Λ := Λ) A) (F2Inv_comp_π₁_eq (Λ := Λ) A) M.M)).trans
          M.φ) x)) =
      pullbackMap_23 (realC A) M.M M.φ
        ((baseChangeSemilinearSelf (realC A).ρ₂ (F3 (Λ := Λ) A) (F3Inv (Λ := Λ) A)
            (F3_comp_ρ₂_eq (Λ := Λ) A) (F3Inv_comp_ρ₂_eq (Λ := Λ) A) M.M)
          ((pullbackMap_23 (realC A) M.M M.φ).symm
            ((natExt (realC A).π₂ (realC A).π₂₃ (realC A).ρ₃_eq_π₂₃_π₂.symm M.M) x))) :=
  natExt_FM23 M (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A) (F3 (Λ := Λ) A)
    (F3Inv (Λ := Λ) A) (F2_comp_π₁_eq (Λ := Λ) A) (F2Inv_comp_π₁_eq (Λ := Λ) A)
    (F3_comp_ρ₂_eq (Λ := Λ) A) (F3Inv_comp_ρ₂_eq (Λ := Λ) A)
    (F3_comp_π₂₃_eq (Λ := Λ) A) x

/-- Compatibility: `π₂₃^* ∘ FM2 = FM3 ∘ π₂₃^*`.

Proof sketch: analogous to `face13_FM2`, using `FM3_13_eq_FM3_23` to replace
`FM3` with `FM3_23` which is defined via `pullbackMap_23`. -/
private lemma face23_FM2 (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (x : π₂s (realC A) M.M) :
    (π₂₃star A M.M) (FM2 (Λ := Λ) A M x) =
    FM3 (Λ := Λ) A M ((π₂₃star A M.M) x) := by
  rw [π₂₃star_eq_natExt]
  simp only [FM3]
  rw [FM3_13_eq_FM3_23]
  rw [FM3_23_apply]
  rw [FM2_apply]
  exact face23_FM2_app A M x

attribute [local semireducible] baseChangeSemilinearSelf pullbackMap_13 pullbackMap_23 natExt

private lemma FM2_oneTmulπ₂_mem_equalizer (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (m : M.M) :
    (π₁₃star A M.M) (FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M m)) =
      (π₂₃star A M.M) (FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M m)) := by
  rw [face13_FM2, face23_FM2, oneTmulπ₂_faces]

private lemma FM2_symm_oneTmulπ₂_mem_equalizer (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (m : M.M) :
    (π₁₃star A M.M) ((FM2 (Λ := Λ) A M).symm (oneTmulπ₂ (A := A) M.M m)) =
      (π₂₃star A M.M) ((FM2 (Λ := Λ) A M).symm (oneTmulπ₂ (A := A) M.M m)) := by
  apply (FM3 (Λ := Λ) A M).injective
  rw [← face13_FM2, ← face23_FM2]
  simp only [LinearEquiv.apply_symm_apply]
  exact oneTmulπ₂_faces A M.M m

noncomputable def descentFrobeniusToFun (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (m : M.M) : M.M :=
  Classical.choose <| pi2_module_equalizer_oneTmul (A := A) M.M
    (FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M m))
    (FM2_oneTmulπ₂_mem_equalizer (Λ := Λ) A M m)

private lemma descentFrobeniusToFun_spec (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (m : M.M) :
    FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M m) =
      oneTmulπ₂ (A := A) M.M (descentFrobeniusToFun (Λ := Λ) A M m) :=
  Classical.choose_spec <| pi2_module_equalizer_oneTmul (A := A) M.M
    (FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M m))
    (FM2_oneTmulπ₂_mem_equalizer (Λ := Λ) A M m)

noncomputable def descentFrobeniusInvFun (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (m : M.M) : M.M :=
  Classical.choose <| pi2_module_equalizer_oneTmul (A := A) M.M
    ((FM2 (Λ := Λ) A M).symm (oneTmulπ₂ (A := A) M.M m))
    (FM2_symm_oneTmulπ₂_mem_equalizer (Λ := Λ) A M m)

private lemma descentFrobeniusInvFun_spec (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (m : M.M) :
    (FM2 (Λ := Λ) A M).symm (oneTmulπ₂ (A := A) M.M m) =
      oneTmulπ₂ (A := A) M.M (descentFrobeniusInvFun (Λ := Λ) A M m) :=
  Classical.choose_spec <| pi2_module_equalizer_oneTmul (A := A) M.M
    ((FM2 (Λ := Λ) A M).symm (oneTmulπ₂ (A := A) M.M m))
    (FM2_symm_oneTmulπ₂_mem_equalizer (Λ := Λ) A M m)

lemma oneTmulπ₂_smul (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M]
    (r : (realC A).R₁) (m : M) :
    oneTmulπ₂ (A := A) M (r • m) =
      (realC A).π₂ r • oneTmulπ₂ (A := A) M m := by
  rw [oneTmulπ₂_apply, oneTmulπ₂_apply]
  change (1 : (realC A).R₂) ⊗ₜ[(realC A).R₁] (r • m) =
    (realC A).π₂ r • ((1 : (realC A).R₂) ⊗ₜ[(realC A).R₁] m)
  rw [TensorProduct.tmul_smul]
  symm
  rw [TensorProduct.smul_tmul']
  congr 1

private lemma F2_π₂_apply (r : (realC A).R₁) :
    F2 (Λ := Λ) A ((realC A).π₂ r) =
      (realC A).π₂ (frobeniusRingHom (Λ := Λ) (A := A) r) := by
  exact congrFun (congrArg DFunLike.coe (F2_comp_π₂_eq (Λ := Λ) A)) r

/-- The Frobenius `F_M : M.M → M.M` obtained from the equalizer.

Construction:
- For `m : M.M`, consider `(1 : R₂) ⊗ m` in `π₂s M`.
- Apply `FM2` to get an element of `π₂s M`.
- By `face13_FM2` and `face23_FM2`, this element is in the equalizer of `π₁₃^*` and `π₂₃^*`.
- `pi2_module_equalizer_oneTmul` gives a unique preimage in `M.M` — that's `F_M(m)`.
- Prove `F_M` is a `frobeniusRingHom`-semilinear bijection.

The key semilinearity calculation: `F_M (r • m) = frobeniusRingHom(r) • F_M(m)`
follows from `FM2` being `F2`-semilinear and `F2_comp_π₂` commuting with the
one-variable Frobenius. -/
noncomputable def descentFrobenius (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) :
    letI : Module (RealNovikovSeries A) M.M := by
      dsimp [RealNovikovSeries, OneVarNovikovSeries, realC]
      exact M.instModule
    M.M ≃ₛₗ[frobeniusRingHom (Λ := Λ) (A := A)] M.M := by
  letI : Module (RealNovikovSeries A) M.M := by
    dsimp [RealNovikovSeries, OneVarNovikovSeries, realC]
    exact M.instModule
  refine
    { toFun := descentFrobeniusToFun (Λ := Λ) A M
      map_add' := ?_
      map_smul' := ?_
      invFun := descentFrobeniusInvFun (Λ := Λ) A M
      left_inv := ?_
      right_inv := ?_ }
  · -- additivity
    intro m n
    apply oneTmulπ₂_injective (A := A) M.M
    calc
      oneTmulπ₂ (A := A) M.M (descentFrobeniusToFun (Λ := Λ) A M (m + n)) =
          FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M (m + n)) := by
            rw [← descentFrobeniusToFun_spec]
      _ = FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M m + oneTmulπ₂ (A := A) M.M n) := by
            rw [map_add]
      _ = FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M m) +
          FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M n) := by
            rw [map_add]
      _ = oneTmulπ₂ (A := A) M.M (descentFrobeniusToFun (Λ := Λ) A M m) +
          oneTmulπ₂ (A := A) M.M (descentFrobeniusToFun (Λ := Λ) A M n) := by
            rw [descentFrobeniusToFun_spec, descentFrobeniusToFun_spec]
      _ = oneTmulπ₂ (A := A) M.M
          (descentFrobeniusToFun (Λ := Λ) A M m + descentFrobeniusToFun (Λ := Λ) A M n) := by
            rw [map_add]
  · -- Frobenius semilinearity
    intro r m
    change descentFrobeniusToFun (Λ := Λ) A M ((r : (realC A).R₁) • m) =
      frobeniusRingHom (Λ := Λ) (A := A) (r : (realC A).R₁) •
        descentFrobeniusToFun (Λ := Λ) A M m
    apply oneTmulπ₂_injective (A := A) M.M
    calc
      oneTmulπ₂ (A := A) M.M
          (descentFrobeniusToFun (Λ := Λ) A M ((r : (realC A).R₁) • m)) =
          FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M ((r : (realC A).R₁) • m)) := by
            rw [← descentFrobeniusToFun_spec]
      _ = FM2 (Λ := Λ) A M ((realC A).π₂ (r : (realC A).R₁) • oneTmulπ₂ (A := A) M.M m) := by
            exact congrArg (FM2 (Λ := Λ) A M)
              (oneTmulπ₂_smul (A := A) M.M (r : (realC A).R₁) m)
      _ = F2 (Λ := Λ) A ((realC A).π₂ (r : (realC A).R₁)) •
          FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M m) := by
            rw [map_smulₛₗ]
      _ = (realC A).π₂ (frobeniusRingHom (Λ := Λ) (A := A) (r : (realC A).R₁)) •
          oneTmulπ₂ (A := A) M.M (descentFrobeniusToFun (Λ := Λ) A M m) := by
            rw [F2_π₂_apply, descentFrobeniusToFun_spec]
      _ = oneTmulπ₂ (A := A) M.M
          (frobeniusRingHom (Λ := Λ) (A := A) (r : (realC A).R₁) •
            descentFrobeniusToFun (Λ := Λ) A M m) := by
            exact (oneTmulπ₂_smul (A := A) M.M
              (frobeniusRingHom (Λ := Λ) (A := A) (r : (realC A).R₁))
              (descentFrobeniusToFun (Λ := Λ) A M m)).symm
  · -- left inverse
    intro m
    apply oneTmulπ₂_injective (A := A) M.M
    calc
      oneTmulπ₂ (A := A) M.M
          (descentFrobeniusInvFun (Λ := Λ) A M (descentFrobeniusToFun (Λ := Λ) A M m)) =
          (FM2 (Λ := Λ) A M).symm
            (oneTmulπ₂ (A := A) M.M (descentFrobeniusToFun (Λ := Λ) A M m)) := by
            rw [← descentFrobeniusInvFun_spec]
      _ = (FM2 (Λ := Λ) A M).symm
            (FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M m)) := by
            rw [← descentFrobeniusToFun_spec]
      _ = oneTmulπ₂ (A := A) M.M m := by simp only [LinearEquiv.symm_apply_apply]
  · -- right inverse
    intro m
    apply oneTmulπ₂_injective (A := A) M.M
    calc
      oneTmulπ₂ (A := A) M.M
          (descentFrobeniusToFun (Λ := Λ) A M (descentFrobeniusInvFun (Λ := Λ) A M m)) =
          FM2 (Λ := Λ) A M
            (oneTmulπ₂ (A := A) M.M (descentFrobeniusInvFun (Λ := Λ) A M m)) := by
            rw [← descentFrobeniusToFun_spec]
      _ = FM2 (Λ := Λ) A M
            ((FM2 (Λ := Λ) A M).symm (oneTmulπ₂ (A := A) M.M m)) := by
            rw [← descentFrobeniusInvFun_spec]
      _ = oneTmulπ₂ (A := A) M.M m := by simp only [LinearEquiv.apply_symm_apply]

private lemma baseChangeMap_π₂_oneTmulπ₂ {M N : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A}
    (f : M ⟶ N) (m : M.M) :
    baseChangeMap (realC A).π₂ f.toLinearMap (oneTmulπ₂ (A := A) M.M m) =
      oneTmulπ₂ (A := A) N.M (f.toLinearMap m) := by
  rw [oneTmulπ₂_apply, baseChangeMap_tmul, oneTmulπ₂_apply]

private lemma descentHom_baseChangeMap_π₂_FM2 {M N : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A}
    (f : M ⟶ N) (x : π₂s (realC A) M.M) :
    baseChangeMap (realC A).π₂ f.toLinearMap (FM2 (Λ := Λ) A M x) =
      FM2 (Λ := Λ) A N (baseChangeMap (realC A).π₂ f.toLinearMap x) := by
  let B₁ :
      letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
      ((realC A).R₂ ⊗[(realC A).R₁] M.M) →ₗ[(realC A).R₂]
        ((realC A).R₂ ⊗[(realC A).R₁] N.M) :=
    letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
    baseChangeMap (realC A).π₁ f.toLinearMap
  let B₂ :
      letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
      ((realC A).R₂ ⊗[(realC A).R₁] M.M) →ₗ[(realC A).R₂]
        ((realC A).R₂ ⊗[(realC A).R₁] N.M) :=
    letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
    baseChangeMap (realC A).π₂ f.toLinearMap
  let T_M :
      letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
      ((realC A).R₂ ⊗[(realC A).R₁] M.M) ≃ₛₗ[F2 (Λ := Λ) (A := A)]
        ((realC A).R₂ ⊗[(realC A).R₁] M.M) :=
    baseChangeSemilinearSelf (realC A).π₁ (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
      (F2_comp_π₁_eq (Λ := Λ) A) (F2Inv_comp_π₁_eq (Λ := Λ) A) M.M
  let T_N :
      letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
      ((realC A).R₂ ⊗[(realC A).R₁] N.M) ≃ₛₗ[F2 (Λ := Λ) (A := A)]
        ((realC A).R₂ ⊗[(realC A).R₁] N.M) :=
    baseChangeSemilinearSelf (realC A).π₁ (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
      (F2_comp_π₁_eq (Λ := Λ) A) (F2Inv_comp_π₁_eq (Λ := Λ) A) N.M
  have hφ_apply (y : π₁s (realC A) M.M) : N.φ (B₁ y) = B₂ (M.φ y) := by
    have h := congrFun (congrArg DFunLike.coe f.commute_φ) y
    simpa [B₁, B₂] using h
  have hφ_symm (y : π₂s (realC A) M.M) :
      B₁ (M.φ.symm y) = N.φ.symm (B₂ y) := by
    apply N.φ.injective
    rw [LinearEquiv.apply_symm_apply]
    simpa using hφ_apply (M.φ.symm y)
  have hT (y : π₁s (realC A) M.M) : B₁ (T_M y) = T_N (B₁ y) := by
    simpa [B₁, T_M, T_N] using
      (baseChangeSemilinearSelf_baseChangeMap (realC A).π₁ (F2 (Λ := Λ) A)
        (F2Inv (Λ := Λ) A) (F2_comp_π₁_eq (Λ := Λ) A)
        (F2Inv_comp_π₁_eq (Λ := Λ) A) f.toLinearMap y).symm
  change B₂ (FM2 (Λ := Λ) A M x) = FM2 (Λ := Λ) A N (B₂ x)
  rw [FM2_apply, FM2_apply]
  change B₂ (M.φ (T_M (M.φ.symm x))) = N.φ (T_N (N.φ.symm (B₂ x)))
  rw [← hφ_apply, hT, hφ_symm]

/-- Object part of the functor from descent data to isocrystals. -/
noncomputable def descentToIsocrystalObj (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) :
    NovikovIsocrystal (Λ := Λ) A :=
  letI : Module (RealNovikovSeries A) M.M := by
    dsimp [RealNovikovSeries, OneVarNovikovSeries, realC]
    exact M.instModule
  haveI : Module.Finite (RealNovikovSeries A) M.M := by
    dsimp [RealNovikovSeries, OneVarNovikovSeries, realC]
    exact M.instFinite
  haveI : Module.Projective (RealNovikovSeries A) M.M := by
    dsimp [RealNovikovSeries, OneVarNovikovSeries, realC]
    exact M.instProjective
  { M := M.M
    F_M := descentFrobenius (Λ := Λ) A M }

/-- Morphism part of the functor.

The underlying map is just the underlying `R₁`-linear map of the descent-datum
morphism.  The remaining compatibility is the naturality of the descended
Frobenius with respect to descent morphisms. -/
noncomputable def descentToIsocrystalMap {M N : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A}
    (f : M ⟶ N) : descentToIsocrystalObj (Λ := Λ) A M ⟶ descentToIsocrystalObj (Λ := Λ) A N :=
  { toLinearMap := by
      dsimp [descentToIsocrystalObj, RealNovikovSeries, OneVarNovikovSeries, realC]
      exact f.toLinearMap
    commute_frobenius := by
      intro x
      change descentFrobeniusToFun (Λ := Λ) A N (f.toLinearMap x) =
        f.toLinearMap (descentFrobeniusToFun (Λ := Λ) A M x)
      apply oneTmulπ₂_injective (A := A) N.M
      calc
        oneTmulπ₂ (A := A) N.M
            (descentFrobeniusToFun (Λ := Λ) A N (f.toLinearMap x)) =
            FM2 (Λ := Λ) A N (oneTmulπ₂ (A := A) N.M (f.toLinearMap x)) := by
              rw [← descentFrobeniusToFun_spec]
        _ = FM2 (Λ := Λ) A N
              (baseChangeMap (realC A).π₂ f.toLinearMap (oneTmulπ₂ (A := A) M.M x)) := by
              rw [baseChangeMap_π₂_oneTmulπ₂]
        _ = baseChangeMap (realC A).π₂ f.toLinearMap
              (FM2 (Λ := Λ) A M (oneTmulπ₂ (A := A) M.M x)) := by
              rw [← descentHom_baseChangeMap_π₂_FM2]
        _ = baseChangeMap (realC A).π₂ f.toLinearMap
              (oneTmulπ₂ (A := A) M.M (descentFrobeniusToFun (Λ := Λ) A M x)) := by
              rw [descentFrobeniusToFun_spec]
        _ = oneTmulπ₂ (A := A) N.M
              (f.toLinearMap (descentFrobeniusToFun (Λ := Λ) A M x)) := by
              rw [baseChangeMap_π₂_oneTmulπ₂] }

/-- Functor from Novikov descent data to Novikov isocrystals. -/
noncomputable def descentToIsocrystal :
    NovikovDescentDatum (⊤ : AddSubgroup ℝ) A ⥤ NovikovIsocrystal (Λ := Λ) A where
  obj := descentToIsocrystalObj (Λ := Λ) A
  map {M N} f := descentToIsocrystalMap (Λ := Λ) A f
  map_id M := by
    apply NovikovIsocrystal.hom_ext
    rfl
  map_comp {M N P} f g := by
    apply NovikovIsocrystal.hom_ext
    rfl

end DescentFrobenius

end Novikov.Descent

