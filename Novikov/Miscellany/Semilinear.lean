import Novikov.Miscellany.BaseChange
import Mathlib.Algebra.Ring.CompTypeclasses

/-!
# Semilinear base change

The *semilinear companion* to base change.  Given a ring homomorphism
`f : R →+* S` and an `S`-ring automorphism `σ` that fixes the image of `f`, the
map `s ⊗ m ↦ σ s ⊗ m` is a `σ`-semilinear automorphism `baseChangeSemilinearSelf`
of `baseChange_along f M = S ⊗[R] M`.  This file records that construction and its
naturality with respect to `baseChangeMap`, `baseChange_assoc`,
`LinearEquiv.baseChange`, and `rTensor`.

The naturality of `baseChangeSemilinearSelf` with respect to the cosimplicial
`pullbackMap` lives with the descent machinery (`Novikov.Descent.Isocrystal`),
since it depends on `pullbackMap`.
-/

open TensorProduct

namespace Novikov.Miscellany

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

/-- Base change of a semilinear equivalence.  If `σS` and `σR` are compatible
with the base-change map `f`, and `φ : M ≃ₛₗ[σR] N`, then
`s ⊗ m ↦ σS s ⊗ φ m` is a `σS`-semilinear equivalence
`S ⊗[R] M ≃ S ⊗[R] N`. -/
noncomputable def baseChangeSemilinearMap
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (σR σRinv : R →+* R) (σS σSinv : S →+* S)
    [RingHomInvPair σR σRinv] [RingHomInvPair σRinv σR]
    [RingHomInvPair σS σSinv] [RingHomInvPair σSinv σS]
    (hσ : σS.comp f = f.comp σR) (hσinv : σSinv.comp f = f.comp σRinv)
    (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M ≃ₛₗ[σR] N) :
    baseChange_along f M ≃ₛₗ[σS] baseChange_along f N := by
  letI : Algebra R S := f.toAlgebra
  let σS_sl : S →ₛₗ[σR] S :=
    { toFun := σS
      map_add' := σS.map_add
      map_smul' := by
        intro r s
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        exact congrFun (congrArg DFunLike.coe hσ) r }
  let σSinv_sl : S →ₛₗ[σRinv] S :=
    { toFun := σSinv
      map_add' := σSinv.map_add
      map_smul' := by
        intro r s
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        exact congrFun (congrArg DFunLike.coe hσinv) r }
  let F_fwd : S ⊗[R] M →ₛₗ[σR] S ⊗[R] N :=
    TensorProduct.map σS_sl (φ : M →ₛₗ[σR] N)
  let F_bwd : S ⊗[R] N →ₛₗ[σRinv] S ⊗[R] M :=
    TensorProduct.map σSinv_sl (φ.symm : N →ₛₗ[σRinv] M)
  have h_F_tmul (s m) : F_fwd (s ⊗ₜ[R] m) = σS s ⊗ₜ[R] φ m :=
    TensorProduct.map_tmul σS_sl (φ : M →ₛₗ[σR] N) s m
  have h_G_tmul (s n) : F_bwd (s ⊗ₜ[R] n) = σSinv s ⊗ₜ[R] φ.symm n :=
    TensorProduct.map_tmul σSinv_sl (φ.symm : N →ₛₗ[σRinv] M) s n
  have h_FG (x : S ⊗[R] M) : F_bwd (F_fwd x) = x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s m => simp [h_F_tmul, h_G_tmul, φ.symm_apply_apply]
    | add x y hx hy => simp [hx, hy]
  have h_GF (x : S ⊗[R] N) : F_fwd (F_bwd x) = x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s n => simp [h_F_tmul, h_G_tmul, φ.apply_symm_apply]
    | add x y hx hy => simp [hx, hy]
  have h_F_semilinear (s : S) (x : S ⊗[R] M) : F_fwd (s • x) = σS s • F_fwd x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m => simp [h_F_tmul, TensorProduct.smul_tmul', smul_eq_mul, RingHom.map_mul]
    | add x y hx hy => simp [smul_add, map_add, hx, hy]
  exact
    { toFun := F_fwd
      invFun := F_bwd
      left_inv := h_FG
      right_inv := h_GF
      map_add' := map_add _
      map_smul' := h_F_semilinear }

@[simp]
lemma baseChangeSemilinearMap_tmul
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (σR σRinv : R →+* R) (σS σSinv : S →+* S)
    [RingHomInvPair σR σRinv] [RingHomInvPair σRinv σR]
    [RingHomInvPair σS σSinv] [RingHomInvPair σSinv σS]
    (hσ : σS.comp f = f.comp σR) (hσinv : σSinv.comp f = f.comp σRinv)
    (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M ≃ₛₗ[σR] N) (s : S) (m : M) :
    baseChangeSemilinearMap f σR σRinv σS σSinv hσ hσinv M N φ
      (letI : Algebra R S := f.toAlgebra; s ⊗ₜ[R] m) =
      (letI : Algebra R S := f.toAlgebra; σS s ⊗ₜ[R] φ m) := by
  simp [baseChangeSemilinearMap]

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

/-- The `σ`-semilinear self-map `baseChangeSemilinearSelf f σ …` on `S ⊗[R] M`
agrees, as a function, with `F.rTensor M` for any `R`-linear `F : S → S` equal to
`σ` pointwise.  Packages the recurring `TensorProduct.induction_on` bridge between
a Frobenius self-map and `F ⊗ id`. -/
lemma baseChangeSemilinearSelf_eq_rTensor
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (σ σinv : S →+* S) [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hσ : σ.comp f = f) (hσinv : σinv.comp f = f)
    (M : Type*) [AddCommGroup M] [Module R M]
    (F : letI := f.toAlgebra; S →ₗ[R] S) (hF : ∀ s, F s = σ s)
    (w : baseChange_along f M) :
    baseChangeSemilinearSelf f σ σinv hσ hσinv M w
      = (letI := f.toAlgebra; F.rTensor M w) := by
  letI := f.toAlgebra
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => rw [baseChangeSemilinearSelf_tmul, LinearMap.rTensor_tmul, hF]
  | add a b ha hb => simp only [map_add, ha, hb]

end Novikov.Miscellany
