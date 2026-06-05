import Novikov.Miscellany.Projective
import Novikov.Miscellany.BaseChange
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.CategoryTheory.Iso

/-! # Products of uniformly bounded finite-dimensional vector spaces

Given vector spaces `P i` over fields `K i` with uniformly bounded finrank, their
product is a finite projective module over the product ring `∀ i, K i`.  The
proof constructs an explicit split injection into the finite free module
`Fin N → ∀ i, K i` by choosing coordinates on each fiber and extending by zero. -/

open LinearMap TensorProduct CategoryTheory
open scoped BigOperators

namespace Novikov.Miscellany

section UniformProduct

variable {I : Type*} (K : I → Type*) [∀ i, Field (K i)]
variable (P : I → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module (K i) (P i)]
variable [∀ i, Module.Finite (K i) (P i)]
variable (N : ℕ) (hN : ∀ i, Module.finrank (K i) (P i) ≤ N)

private noncomputable def fiberEquiv (i : I) : P i ≃ₗ[K i]
    (Fin (Module.finrank (K i) (P i)) → K i) :=
  (Module.finBasis (K i) (P i)).equivFun

private noncomputable def fiberExtend (i : I) :
    (Fin (Module.finrank (K i) (P i)) → K i) →ₗ[K i] (Fin N → K i) where
  toFun v j := if h : (j : ℕ) < Module.finrank (K i) (P i) then v ⟨j, h⟩ else 0
  map_add' v w := by
    ext j
    by_cases h : (j : ℕ) < Module.finrank (K i) (P i)
    · simp [h]
    · simp [h]
  map_smul' a v := by
    ext j
    by_cases h : (j : ℕ) < Module.finrank (K i) (P i)
    · simp [h]
    · simp [h]

private noncomputable def fiberTruncate (i : I) :
    (Fin N → K i) →ₗ[K i] (Fin (Module.finrank (K i) (P i)) → K i) where
  toFun v j := v ⟨j, lt_of_lt_of_le j.isLt (hN i)⟩
  map_add' v w := by
    ext j
    rfl
  map_smul' a v := by
    ext j
    rfl

private noncomputable def fiberIntoFree (i : I) : P i →ₗ[K i] (Fin N → K i) :=
  (fiberExtend K P N i).comp (fiberEquiv K P i).toLinearMap

private noncomputable def fiberFromFree (i : I) : (Fin N → K i) →ₗ[K i] P i :=
  (fiberEquiv K P i).symm.toLinearMap.comp (fiberTruncate K P N hN i)

omit [∀ i, Module.Finite (K i) (P i)] in
private lemma fiberTruncate_comp_fiberExtend (i : I) :
    (fiberTruncate K P N hN i).comp (fiberExtend K P N i) = LinearMap.id := by
  ext v j
  simp [fiberTruncate, fiberExtend, j.isLt]

private lemma fiberFromFree_comp_fiberIntoFree (i : I) :
    (fiberFromFree K P N hN i).comp (fiberIntoFree K P N i) = LinearMap.id := by
  ext p
  change (fiberEquiv K P i).symm
      ((fiberTruncate K P N hN i) ((fiberExtend K P N i) ((fiberEquiv K P i) p))) = p
  rw [← LinearMap.comp_apply, fiberTruncate_comp_fiberExtend]
  exact LinearEquiv.symm_apply_apply (fiberEquiv K P i) p

/-- The split injection from a product of uniformly bounded finite-dimensional
fibers into a finite free module over the product ring. -/
noncomputable def prodModuleIntoFree :
    (∀ i, P i) →ₗ[∀ i, K i] (Fin N → ∀ i, K i) where
  toFun p j i := fiberIntoFree K P N i (p i) j
  map_add' p q := by
    ext j i
    change (fiberIntoFree K P N i ((p + q) i)) j =
      (fiberIntoFree K P N i (p i) + fiberIntoFree K P N i (q i)) j
    rw [Pi.add_apply, map_add]
  map_smul' a p := by
    ext j i
    change (fiberIntoFree K P N i (a i • p i)) j =
      (a i • fiberIntoFree K P N i (p i)) j
    rw [map_smul]

/-- A retraction from the finite free module onto the product module. -/
noncomputable def prodModuleFromFree :
    (Fin N → ∀ i, K i) →ₗ[∀ i, K i] (∀ i, P i) where
  toFun v i := fiberFromFree K P N hN i (fun j => v j i)
  map_add' v w := by
    ext i
    change fiberFromFree K P N hN i (fun j => v j i + w j i) =
      fiberFromFree K P N hN i (fun j => v j i) +
        fiberFromFree K P N hN i (fun j => w j i)
    exact map_add (fiberFromFree K P N hN i) (fun j => v j i) (fun j => w j i)
  map_smul' a v := by
    ext i
    change fiberFromFree K P N hN i (fun j => a i • v j i) =
      a i • fiberFromFree K P N hN i (fun j => v j i)
    exact map_smul (fiberFromFree K P N hN i) (a i) (fun j => v j i)

/-- The explicit retraction is left inverse to the explicit injection. -/
lemma prodModuleFromFree_comp_prodModuleIntoFree :
    (prodModuleFromFree K P N hN).comp
      (prodModuleIntoFree K P N) = LinearMap.id := by
  ext p i
  exact LinearMap.ext_iff.mp (fiberFromFree_comp_fiberIntoFree K P N hN i) (p i)

/-- Products of vector spaces with uniformly bounded fiber dimension are finite
over the product ring. -/
instance prodModule_finite_of_uniform_finrank :
    Module.Finite (∀ i, K i) (∀ i, P i) := by
  exact Module.Finite.of_surjective
    (prodModuleFromFree K P N hN)
    (fun x => ⟨prodModuleIntoFree K P N x,
      LinearMap.congr_fun (prodModuleFromFree_comp_prodModuleIntoFree K P N hN) x⟩)

/-- Products of vector spaces with uniformly bounded fiber dimension are
projective over the product ring. -/
instance prodModule_projective_of_uniform_finrank :
    Module.Projective (∀ i, K i) (∀ i, P i) := by
  exact Module.Projective.of_split
    (prodModuleIntoFree K P N)
    (prodModuleFromFree K P N hN)
    (prodModuleFromFree_comp_prodModuleIntoFree K P N hN)

end UniformProduct

section EvalTensorPi

variable {I : Type*} (K : I → Type*) [∀ i, Field (K i)]
variable (P : I → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module (K i) (P i)]

/-- Evaluating the product coefficient ring at one factor commutes with tensoring
with the product module.  The equivalence sends `s ⊗ p` to `s ⊗ p i` and its
inverse sends `s ⊗ pᵢ` to `s ⊗ Pi.single i pᵢ`. -/
noncomputable def evalTensorPiEquiv (i : I) (S : Type*) [CommRing S] [Algebra (K i) S] :
    letI : Algebra (∀ i, K i) S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra
    S ⊗[(∀ i, K i)] (∀ i, P i) ≃ₗ[S] S ⊗[K i] P i := by
  classical
  let A := ∀ i, K i
  letI : Algebra A S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra
  let forward : S ⊗[A] (∀ i, P i) →ₗ[S] S ⊗[K i] P i :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun s =>
          { toFun := fun p => s ⊗ₜ[K i] p i
            map_add' := by intro p q; simp [TensorProduct.tmul_add]
            map_smul' := by
              intro a p
              change s ⊗ₜ[K i] (a i • p i) =
                (a • (s ⊗ₜ[K i] p i) : S ⊗[K i] P i)
              rw [TensorProduct.tmul_smul]
              rw [TensorProduct.smul_tmul']
              rw [TensorProduct.smul_tmul']
              have hs : (a i • s : S) = (a • s : S) := by
                simp only [Algebra.smul_def]
                rfl
              rw [hs] }
        map_add' := by
          intro s t
          apply LinearMap.ext
          intro p
          simp [TensorProduct.add_tmul]
        map_smul' := by
          intro s t
          apply LinearMap.ext
          intro p
          rw [LinearMap.smul_apply]
          change (s * t) ⊗ₜ[K i] p i = s • (t ⊗ₜ[K i] p i)
          rw [TensorProduct.smul_tmul']
          rfl }
  let backward : S ⊗[K i] P i →ₗ[S] S ⊗[A] (∀ i, P i) :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun s =>
          { toFun := fun p => s ⊗ₜ[A] (Pi.single i p : ∀ i, P i)
            map_add' := by
              intro p q
              have hsingle : (Pi.single i (p + q) : ∀ i, P i) = Pi.single i p + Pi.single i q := by
                ext j
                by_cases h : j = i
                · subst j
                  simp
                · simp [Pi.single_eq_of_ne h]
              rw [hsingle, TensorProduct.tmul_add]
            map_smul' := by
              intro a p
              let e : A := Pi.single i a
              have hsingle : (Pi.single i (a • p) : ∀ i, P i) =
                  (Pi.single i a : A) • Pi.single i p := by
                ext j
                by_cases h : j = i
                · subst j
                  simp
                · simp [Pi.single_eq_of_ne h]
              change s ⊗ₜ[A] (Pi.single i (a • p) : ∀ i, P i) =
                (a • (s ⊗ₜ[A] (Pi.single i p : ∀ i, P i)) : S ⊗[A] (∀ i, P i))
              rw [hsingle]
              rw [TensorProduct.tmul_smul]
              rw [TensorProduct.smul_tmul']
              have hs : (e • s : S) = (a • s : S) := by
                simp only [Algebra.smul_def]
                dsimp [e]
                change (algebraMap (K i) S ((Pi.single i a) i)) * s =
                  (algebraMap (K i) S a) * s
                rw [Pi.single_eq_same]
              rw [hs]
              change (a • s) ⊗ₜ[A] (Pi.single i p : ∀ i, P i) =
                (a • s) ⊗ₜ[A] (Pi.single i p : ∀ i, P i)
              rfl }
        map_add' := by
          intro s t
          apply LinearMap.ext
          intro p
          simp [TensorProduct.add_tmul]
        map_smul' := by
          intro s t
          apply LinearMap.ext
          intro p
          rw [LinearMap.smul_apply]
          change (s * t) ⊗ₜ[A] (Pi.single i p : ∀ i, P i) =
            s • (t ⊗ₜ[A] (Pi.single i p : ∀ i, P i))
          rw [TensorProduct.smul_tmul']
          rfl }
  refine LinearEquiv.ofLinear forward backward ?_ ?_
  · apply TensorProduct.AlgebraTensorModule.ext
    intro s p
    change forward (backward (s ⊗ₜ[K i] p)) = s ⊗ₜ[K i] p
    dsimp [forward, backward]
    rw [Pi.single_eq_same]
  · apply TensorProduct.AlgebraTensorModule.ext
    intro s p
    change backward (forward (s ⊗ₜ[A] p)) = s ⊗ₜ[A] p
    dsimp [forward, backward]
    let e : A := Pi.single i (1 : K i)
    have hp : (Pi.single i (p i) : ∀ i, P i) = e • p := by
      dsimp [e]
      ext j
      by_cases h : j = i
      · subst j
        rw [Pi.smul_apply']
        rw [Pi.single_eq_same]
        simp
      · rw [Pi.smul_apply']
        rw [Pi.single_eq_of_ne h]
        simp [Pi.single_eq_of_ne h]
    have he : (e • s : S) = s := by
      change (algebraMap A S e) * s = s
      dsimp [e]
      change (algebraMap (K i) S ((Pi.single i (1 : K i)) i)) * s = s
      rw [Pi.single_eq_same]
      simp
    calc
      s ⊗ₜ[A] (Pi.single i (p i) : ∀ i, P i) = s ⊗ₜ[A] (e • p) := by rw [hp]
      _ = (e • s) ⊗ₜ[A] p := by
        rw [TensorProduct.tmul_smul]
        change e • s ⊗ₜ[A] p = (e • s) ⊗ₜ[A] p
        rfl
      _ = s ⊗ₜ[A] p := by rw [he]

@[simp]
lemma evalTensorPiEquiv_tmul
    (i : I) (S : Type*) [CommRing S] [Algebra (K i) S]
    (s : S) (p : ∀ i, P i) :
    (letI : Algebra (∀ i, K i) S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra;
      evalTensorPiEquiv K P i S (s ⊗ₜ[(∀ i, K i)] p)) = s ⊗ₜ[K i] p i := by
  rfl

end EvalTensorPi

section TensorProductPiLeft

variable {R : Type*} [CommRing R]
variable {I : Type*} (S : I → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- The natural map from tensoring with a product ring on the left to the product
of tensor products. It sends `s ⊗ m` to the family `i ↦ s i ⊗ m`. -/
noncomputable def tensorProductPiLeftHom :
    (∀ i, S i) ⊗[R] M →ₗ[∀ i, S i] ∀ i, S i ⊗[R] M :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun s =>
        { toFun := fun m i => s i ⊗ₜ[R] m
          map_add' := by intro m n; ext i; simp [tmul_add]
          map_smul' := by
            intro r m
            ext i
            simp [TensorProduct.smul_tmul'] }
      map_add' := by
        intro s t
        ext m i
        simp [add_tmul]
      map_smul' := by
        intro s t
        ext m i
        change (s i * t i) ⊗ₜ[R] m = s i • (t i ⊗ₜ[R] m)
        rw [TensorProduct.smul_tmul', Algebra.smul_def]
        simp }

@[simp]
lemma tensorProductPiLeftHom_tmul (s : ∀ i, S i) (m : M) (i : I) :
    tensorProductPiLeftHom S M (s ⊗ₜ[R] m) i = s i ⊗ₜ[R] m := by
  rfl

/-- Componentwise compatibility of `tensorProductPiLeftHom` with a further scalar
extension of the product scalar ring. -/
lemma tensorProductPiLeftHom_cancelBaseChange_apply
    (T : I → Type*) [∀ i, CommRing (T i)] [∀ i, Algebra (S i) (T i)]
    [∀ i, Algebra R (T i)] [∀ i, IsScalarTower R (S i) (T i)]
    (x : (∀ i, S i) ⊗[R] M) (i : I) :
    let B₁ := ∀ i, S i
    let B₂ := ∀ i, T i
    (tensorProductPiLeftHom T M
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R B₁ B₂ B₂ M)
        ((1 : B₂) ⊗ₜ[B₁] x)) : ∀ i, T i ⊗[R] M) i =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (S i) (T i) (T i) M)
        ((1 : T i) ⊗ₜ[S i] ((tensorProductPiLeftHom S M x : ∀ i, S i ⊗[R] M) i)) := by
  classical
  intro B₁ B₂
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | add x y hx hy =>
      rw [TensorProduct.tmul_add]
      rw [map_add (TensorProduct.AlgebraTensorModule.cancelBaseChange R B₁ B₂ B₂ M)]
      rw [map_add (tensorProductPiLeftHom T M)]
      rw [Pi.add_apply]
      rw [map_add (tensorProductPiLeftHom S M)]
      rw [Pi.add_apply]
      rw [TensorProduct.tmul_add]
      rw [map_add (TensorProduct.AlgebraTensorModule.cancelBaseChange R (S i) (T i) (T i) M)]
      rw [hx, hy]
  | tmul s m =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      rw [tensorProductPiLeftHom_tmul]
      rw [tensorProductPiLeftHom_tmul]
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      have h : (s • (1 : B₂)) i = s i • (1 : T i) := rfl
      exact congrArg (fun t => t ⊗ₜ[R] m) h

/-- Swap a finite product with an arbitrary product, linearly over the product ring. -/
noncomputable def finPiSwapLinearEquiv (n : ℕ) :
    (Fin n → ∀ i, S i) ≃ₗ[∀ i, S i] ∀ i, Fin n → S i where
  toFun x i j := x j i
  invFun y j i := y i j
  left_inv x := by ext j i; rfl
  right_inv y := by ext i j; rfl
  map_add' x y := by ext i j; rfl
  map_smul' a x := by ext i j; rfl

/-- Coordinate equivalence on a product of tensor products with a finite free module. -/
noncomputable def piTensorFreeCoordEquiv (n : ℕ) :
    (∀ i, S i ⊗[R] (Fin n → R)) ≃ₗ[∀ i, S i] ∀ i, Fin n → S i where
  toFun x i := TensorProduct.piScalarRight R (S i) (S i) (Fin n) (x i)
  invFun y i := (TensorProduct.piScalarRight R (S i) (S i) (Fin n)).symm (y i)
  left_inv x := by
    ext i
    exact LinearEquiv.symm_apply_apply (TensorProduct.piScalarRight R (S i) (S i) (Fin n)) (x i)
  right_inv y := by
    ext i j
    exact congrFun
      (LinearEquiv.apply_symm_apply (TensorProduct.piScalarRight R (S i) (S i) (Fin n)) (y i)) j
  map_add' x y := by
    ext i j
    simp
  map_smul' a x := by
    ext i j
    simp

/-- Tensoring a finite free module commutes with arbitrary products on the left. -/
noncomputable def tensorProductPiLeftFreeEquiv (n : ℕ) :
    (∀ i, S i) ⊗[R] (Fin n → R) ≃ₗ[∀ i, S i]
      ∀ i, S i ⊗[R] (Fin n → R) :=
  (TensorProduct.piScalarRight R (∀ i, S i) (∀ i, S i) (Fin n)).trans
    ((finPiSwapLinearEquiv S n).trans (piTensorFreeCoordEquiv S n).symm)

/-- On pure tensors, the finite-free equivalence agrees with
`tensorProductPiLeftHom`. -/
lemma tensorProductPiLeftFreeEquiv_apply_tmul (n : ℕ) (s : ∀ i, S i) (v : Fin n → R) :
    tensorProductPiLeftFreeEquiv S n (s ⊗ₜ[R] v) =
      tensorProductPiLeftHom S (Fin n → R) (s ⊗ₜ[R] v) := by
  ext i
  change (TensorProduct.piScalarRight R (S i) (S i) (Fin n)).symm
      (fun j => v j • s i) = s i ⊗ₜ[R] v
  apply (TensorProduct.piScalarRight R (S i) (S i) (Fin n)).injective
  ext j
  simp

/-- The finite-free equivalence has the natural map as its underlying linear map. -/
lemma tensorProductPiLeftFreeEquiv_toLinearMap (n : ℕ) :
    (tensorProductPiLeftFreeEquiv S n).toLinearMap =
      tensorProductPiLeftHom S (Fin n → R) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s v
  exact tensorProductPiLeftFreeEquiv_apply_tmul S n s v

/-- Apply a base-changed map in each factor of a product of tensor products. -/
noncomputable def piBaseChangeMap {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) :
    (∀ i, S i ⊗[R] M) →ₗ[∀ i, S i] ∀ i, S i ⊗[R] N where
  toFun x i := LinearMap.baseChange (S i) φ (x i)
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    exact map_smul (LinearMap.baseChange (S i) φ) (a i) (x i)

/-- Naturality of `tensorProductPiLeftHom` with respect to a map in the tensor
factor. -/
lemma piBaseChangeMap_comp_tensorProductPiLeftHom {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) :
    (piBaseChangeMap S φ).comp (tensorProductPiLeftHom S M) =
      (tensorProductPiLeftHom S N).comp (LinearMap.baseChange (∀ i, S i) φ) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s m
  ext i
  simp [piBaseChangeMap]

/-- Functoriality of applying base-changed maps in each product factor. -/
lemma piBaseChangeMap_comp {M N P : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (ψ : N →ₗ[R] P) (φ : M →ₗ[R] N) :
    (piBaseChangeMap S ψ).comp (piBaseChangeMap S φ) = piBaseChangeMap S (ψ.comp φ) := by
  ext x i
  simp [piBaseChangeMap, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]

@[simp]
lemma piBaseChangeMap_id (M : Type*) [AddCommGroup M] [Module R M] :
    piBaseChangeMap S (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext x i
  simp [piBaseChangeMap]

/-- Tensoring a finite projective module commutes with arbitrary products on the
left. -/
noncomputable def tensorProductPiLeftOfFiniteProjective (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    (∀ i, S i) ⊗[R] M ≃ₗ[∀ i, S i] ∀ i, S i ⊗[R] M := by
  classical
  let h0 := Module.Finite.exists_comp_eq_id_of_projective R M
  let n := Classical.choose h0
  let h1 := Classical.choose_spec h0
  let f := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let g := Classical.choose h2
  let h3 := Classical.choose_spec h2
  have hfg : f.comp g = (LinearMap.id : M →ₗ[R] M) := h3.2.2
  let F := Fin n → R
  let A := ∀ i, S i
  let freeEquiv := tensorProductPiLeftFreeEquiv (R := R) S n
  let forward : A ⊗[R] M →ₗ[A] ∀ i, S i ⊗[R] M := tensorProductPiLeftHom S M
  let inverse : (∀ i, S i ⊗[R] M) →ₗ[A] A ⊗[R] M :=
    (LinearMap.baseChange A f).comp (freeEquiv.symm.toLinearMap.comp (piBaseChangeMap S g))
  refine LinearEquiv.ofLinear forward inverse ?_ ?_
  · apply LinearMap.ext
    intro y
    change forward (inverse y) = y
    have hnat := LinearMap.congr_fun (piBaseChangeMap_comp_tensorProductPiLeftHom S f)
      (freeEquiv.symm ((piBaseChangeMap S g) y))
    have hsplit_pi : (piBaseChangeMap S f).comp (piBaseChangeMap S g) = LinearMap.id := by
      rw [piBaseChangeMap_comp, hfg, piBaseChangeMap_id]
    simp only [inverse, forward, LinearMap.comp_apply] at hnat ⊢
    change (tensorProductPiLeftHom S M)
      ((LinearMap.baseChange ((i : I) → S i) f) (freeEquiv.symm ((piBaseChangeMap S g) y))) = y
    rw [← hnat]
    change (piBaseChangeMap S f)
      (tensorProductPiLeftHom S F (freeEquiv.symm ((piBaseChangeMap S g) y))) = y
    rw [← tensorProductPiLeftFreeEquiv_toLinearMap]
    change (piBaseChangeMap S f) (freeEquiv (freeEquiv.symm ((piBaseChangeMap S g) y))) = y
    simp only [LinearEquiv.apply_symm_apply]
    change ((piBaseChangeMap S f).comp (piBaseChangeMap S g)) y = y
    rw [hsplit_pi]
    rfl
  · apply LinearMap.ext
    intro x
    change inverse (forward x) = x
    have hnat := LinearMap.congr_fun (piBaseChangeMap_comp_tensorProductPiLeftHom S g) x
    have hsplit : (LinearMap.baseChange A f).comp (LinearMap.baseChange A g) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_id]
    simp only [inverse, forward, LinearMap.comp_apply] at hnat ⊢
    rw [hnat]
    change (LinearMap.baseChange A f)
      (freeEquiv.symm (tensorProductPiLeftHom S F ((LinearMap.baseChange A g) x))) = x
    rw [← tensorProductPiLeftFreeEquiv_toLinearMap]
    change (LinearMap.baseChange A f)
      (freeEquiv.symm (freeEquiv ((LinearMap.baseChange A g) x))) = x
    simp only [LinearEquiv.symm_apply_apply]
    change ((LinearMap.baseChange A f).comp (LinearMap.baseChange A g)) x = x
    rw [hsplit]
    rfl

@[simp]
lemma tensorProductPiLeftOfFiniteProjective_tmul (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (s : ∀ i, S i) (m : M) (i : I) :
    (tensorProductPiLeftOfFiniteProjective (R := R) S M (s ⊗ₜ[R] m)) i =
      s i ⊗ₜ[R] m := by
  change tensorProductPiLeftHom S M (s ⊗ₜ[R] m) i = s i ⊗ₜ[R] m
  rfl

end TensorProductPiLeft

namespace FiniteProjectiveModule

variable {I : Type*} (K : I → Type*) [∀ i, Field (K i)]
variable (P : ∀ i, FiniteProjectiveModule (K i))
variable (N : ℕ) (hN : ∀ i, Module.finrank (K i) (P i).M ≤ N)

/-- A product of finite-dimensional vector spaces with uniformly bounded dimensions,
as a finite projective module over the product ring. -/
noncomputable def piOfUniformFinrank : FiniteProjectiveModule (∀ i, K i) where
  M := ∀ i, (P i).M
  instAddCommGroup := inferInstance
  instModule := inferInstance
  instFinite := prodModule_finite_of_uniform_finrank K (fun i => (P i).M) N hN
  instProjective := prodModule_projective_of_uniform_finrank K (fun i => (P i).M) N hN

/-- A componentwise isomorphism between uniformly bounded products.  The two
uniform bounds may be different. -/
noncomputable def piOfUniformFinrankIso
    {Q : ∀ i, FiniteProjectiveModule (K i)} {NQ : ℕ}
    {hQ : ∀ i, Module.finrank (K i) (Q i).M ≤ NQ}
    (e : ∀ i, CategoryTheory.Iso (P i) (Q i)) :
    CategoryTheory.Iso (piOfUniformFinrank K P N hN) (piOfUniformFinrank K Q NQ hQ) where
  hom := {
    toFun := fun p i =>
      let h : (P i).M →ₗ[K i] (Q i).M := (e i).hom
      h (p i)
    map_add' := by
      intro p q
      funext i
      let h : (P i).M →ₗ[K i] (Q i).M := (e i).hom
      exact map_add h (p i) (q i)
    map_smul' := by
      intro a p
      funext i
      let h : (P i).M →ₗ[K i] (Q i).M := (e i).hom
      exact map_smul h (a i) (p i) }
  inv := {
    toFun := fun q i =>
      let h : (Q i).M →ₗ[K i] (P i).M := (e i).inv
      h (q i)
    map_add' := by
      intro p q
      funext i
      let h : (Q i).M →ₗ[K i] (P i).M := (e i).inv
      exact map_add h (p i) (q i)
    map_smul' := by
      intro a p
      funext i
      let h : (Q i).M →ₗ[K i] (P i).M := (e i).inv
      exact map_smul h (a i) (p i) }
  hom_inv_id := by
    apply LinearMap.ext
    intro p
    funext i
    let hPQ : (P i).M →ₗ[K i] (Q i).M := (e i).hom
    let hQP : (Q i).M →ₗ[K i] (P i).M := (e i).inv
    change hQP (hPQ (p i)) = p i
    have hlin : hQP.comp hPQ = LinearMap.id := by
      exact (e i).hom_inv_id
    exact LinearMap.congr_fun hlin (p i)
  inv_hom_id := by
    apply LinearMap.ext
    intro q
    funext i
    let hPQ : (P i).M →ₗ[K i] (Q i).M := (e i).hom
    let hQP : (Q i).M →ₗ[K i] (P i).M := (e i).inv
    change hPQ (hQP (q i)) = q i
    have hlin : hPQ.comp hQP = LinearMap.id := by
      exact (e i).inv_hom_id
    exact LinearMap.congr_fun hlin (q i)

@[simp]
lemma piOfUniformFinrankIso_hom_apply
    {Q : ∀ i, FiniteProjectiveModule (K i)} {NQ : ℕ}
    {hQ : ∀ i, Module.finrank (K i) (Q i).M ≤ NQ}
    (e : ∀ i, CategoryTheory.Iso (P i) (Q i))
    (p : (piOfUniformFinrank K P N hN).M) (i : I) :
    (let h : (piOfUniformFinrank K P N hN).M →ₗ[∀ i, K i]
        (piOfUniformFinrank K Q NQ hQ).M := (piOfUniformFinrankIso K P N hN e).hom;
      (h p) i) =
      (let h : (P i).M →ₗ[K i] (Q i).M := (e i).hom
       h (p i)) := rfl

@[simp]
lemma piOfUniformFinrankIso_inv_apply
    {Q : ∀ i, FiniteProjectiveModule (K i)} {NQ : ℕ}
    {hQ : ∀ i, Module.finrank (K i) (Q i).M ≤ NQ}
    (e : ∀ i, CategoryTheory.Iso (P i) (Q i))
    (q : (piOfUniformFinrank K Q NQ hQ).M) (i : I) :
    (let h : (piOfUniformFinrank K Q NQ hQ).M →ₗ[∀ i, K i]
        (piOfUniformFinrank K P N hN).M := (piOfUniformFinrankIso K P N hN e).inv;
      (h q) i) =
      (let h : (Q i).M →ₗ[K i] (P i).M := (e i).inv
       h (q i)) := rfl

/-- The chosen split injection of a single fiber into the uniform finite free
module. -/
noncomputable def fiberCoordIntoFree (i : I) :
    (P i).M →ₗ[K i] (Fin N → K i) :=
  fiberIntoFree K (fun i => (P i).M) N i

/-- The split injection of `piOfUniformFinrank` into a finite free module. -/
noncomputable def piUniformIntoFree :
    (piOfUniformFinrank K P N hN).M →ₗ[∀ i, K i] (Fin N → ∀ i, K i) :=
  prodModuleIntoFree K (fun i => (P i).M) N

@[simp]
lemma piUniformIntoFree_apply
    (p : (piOfUniformFinrank K P N hN).M) (c : Fin N) (i : I) :
    piUniformIntoFree K P N hN p c i = fiberCoordIntoFree K P N i (p i) c :=
  rfl

/-- The retraction from the finite free module onto `piOfUniformFinrank`. -/
noncomputable def piUniformFromFree :
    (Fin N → ∀ i, K i) →ₗ[∀ i, K i] (piOfUniformFinrank K P N hN).M :=
  prodModuleFromFree K (fun i => (P i).M) N hN

/-- The free-module retraction is left inverse to the free-module injection. -/
lemma piUniformFromFree_comp_piUniformIntoFree :
    (piUniformFromFree K P N hN).comp (piUniformIntoFree K P N hN) = LinearMap.id :=
  prodModuleFromFree_comp_prodModuleIntoFree K (fun i => (P i).M) N hN

/-- Base change of the split injection into the finite free module. -/
noncomputable def piUniformBaseChangeIntoFree
    (S : Type*) [CommRing S] [Algebra (∀ i, K i) S] :
    S ⊗[∀ i, K i] (piOfUniformFinrank K P N hN).M →ₗ[S]
      S ⊗[∀ i, K i] (Fin N → ∀ i, K i) :=
  LinearMap.baseChange S (piUniformIntoFree K P N hN)

/-- Coordinates of a base-changed `piOfUniformFinrank` element in the ambient
finite free module. -/
noncomputable def piUniformBaseChangeCoord
    (S : Type*) [CommRing S] [Algebra (∀ i, K i) S] :
    S ⊗[∀ i, K i] (piOfUniformFinrank K P N hN).M →ₗ[S] (Fin N → S) :=
  (TensorProduct.piScalarRight (∀ i, K i) S S (Fin N)).toLinearMap.comp
    (piUniformBaseChangeIntoFree K P N hN S)

@[simp]
lemma piUniformBaseChangeCoord_tmul
    (S : Type*) [CommRing S] [Algebra (∀ i, K i) S]
    (s : S) (p : (piOfUniformFinrank K P N hN).M) :
    piUniformBaseChangeCoord K P N hN S (s ⊗ₜ[∀ i, K i] p) =
      fun c => ((piUniformIntoFree K P N hN p c) : (∀ i, K i)) • s := by
  ext c
  simp [piUniformBaseChangeCoord, piUniformBaseChangeIntoFree]

/-- Coordinates in a single fiber after base change to an algebra over that
fiber. -/
noncomputable def fiberBaseChangeCoord
    (i : I) (S : Type*) [CommRing S] [Algebra (K i) S] :
    S ⊗[K i] (P i).M →ₗ[S] (Fin N → S) :=
  (TensorProduct.piScalarRight (K i) S S (Fin N)).toLinearMap.comp
    (LinearMap.baseChange S (fiberCoordIntoFree K P N i))

@[simp]
lemma fiberBaseChangeCoord_tmul
    (i : I) (S : Type*) [CommRing S] [Algebra (K i) S]
    (s : S) (p : (P i).M) :
    fiberBaseChangeCoord K P N i S (s ⊗ₜ[K i] p) =
      fun c => (fiberCoordIntoFree K P N i p c) • s := by
  ext c
  simp [fiberBaseChangeCoord]

/-- The evaluation tensor equivalence preserves the explicit finite-free
coordinates used for uniformly bounded product modules. -/
lemma fiberBaseChangeCoord_evalTensorPiEquiv
    (i : I) (S : Type*) [CommRing S] [Algebra (K i) S]
    (z : (letI : Algebra (∀ i, K i) S :=
        ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra;
      S ⊗[(∀ i, K i)] (∀ i, (P i).M)))
    (c : Fin N) :
    (letI : Algebra (∀ i, K i) S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra;
      fiberBaseChangeCoord K P N i S
        ((evalTensorPiEquiv K (fun i => (P i).M) i S) z) c) =
      (letI : Algebra (∀ i, K i) S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra;
        piUniformBaseChangeCoord K P N hN S z c) := by
  classical
  let A := ∀ i, K i
  letI : Algebra A S := ((algebraMap (K i) S).comp (Pi.evalRingHom K i)).toAlgebra
  induction z using TensorProduct.induction_on with
  | zero =>
      exact (congrFun (map_zero (piUniformBaseChangeCoord K P N hN S)) c).symm
  | add x y hx hy =>
      rw [map_add, map_add]
      rw [Pi.add_apply]
      rw [hx, hy]
      exact (congrFun (map_add (piUniformBaseChangeCoord K P N hN S) x y) c).symm
  | tmul s p =>
      rw [evalTensorPiEquiv_tmul]
      rw [fiberBaseChangeCoord_tmul]
      have hcoord := congrFun (piUniformBaseChangeCoord_tmul K P N hN S s p) c
      calc
        (fun c => (fiberCoordIntoFree K P N i) (p i) c • s) c =
            (piUniformIntoFree K P N hN p c) • s := by
          simp only [Algebra.smul_def]
          change (algebraMap (K i) S) ((fiberCoordIntoFree K P N i) (p i) c) * s =
            (algebraMap ((i : I) → K i) S) ((piUniformIntoFree K P N hN) p c) * s
          change (algebraMap (K i) S)
              ((fiberIntoFree K (fun i => (P i).M) N i) (p i) c) * s =
            (algebraMap (K i) S)
              (((prodModuleIntoFree K (fun i => (P i).M) N) p c) i) * s
          rfl
        _ = (piUniformBaseChangeCoord K P N hN S) (s ⊗ₜ[(∀ i, K i)] p) c :=
          hcoord.symm

/-- Coordinates commute with a further scalar extension in a single fiber. -/
lemma fiberBaseChangeCoord_baseChange_assoc
    (i : I) (S T : Type*) [CommRing S] [CommRing T]
    (f : K i →+* S) (g : S →+* T)
    (x : baseChange_along f (P i).M) :
    letI : Algebra (K i) S := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra (K i) T := (g.comp f).toAlgebra
    fiberBaseChangeCoord K P N i T
        ((baseChange_assoc f g (P i).M) ((1 : T) ⊗ₜ[S] x)) =
      fun c => g (fiberBaseChangeCoord K P N i S x c) := by
  letI : Algebra (K i) S := f.toAlgebra
  letI : Algebra S T := g.toAlgebra
  letI : Algebra (K i) T := (g.comp f).toAlgebra
  change fiberBaseChangeCoord K P N i T
        ((baseChange_assoc f g (P i).M) ((1 : T) ⊗ₜ[S] x)) =
      fun c => g (fiberBaseChangeCoord K P N i S x c)
  induction x using TensorProduct.induction_on with
  | zero =>
      ext c
      simp
  | add x y hx hy =>
      ext c
      rw [TensorProduct.tmul_add, map_add]
      simp [hx, hy]
  | tmul s p =>
      ext c
      simp [fiberBaseChangeCoord, Algebra.smul_def]
      rfl

/-- Version of `fiberBaseChangeCoord_baseChange_assoc` using
`baseChange_assoc_eq`. -/
lemma fiberBaseChangeCoord_baseChange_assoc_eq
    (i : I) (S T : Type*) [CommRing S] [CommRing T]
    (f : K i →+* S) (g : S →+* T) {ρ : K i →+* T} (h : g.comp f = ρ)
    (x : baseChange_along f (P i).M) :
    letI : Algebra (K i) S := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra (K i) T := ρ.toAlgebra
    fiberBaseChangeCoord K P N i T
        ((baseChange_assoc_eq f g h (P i).M) ((1 : T) ⊗ₜ[S] x)) =
      fun c => g (fiberBaseChangeCoord K P N i S x c) := by
  subst h
  exact fiberBaseChangeCoord_baseChange_assoc K P N i S T f g x

/-- The coordinate map after any base change is injective. -/
lemma piUniformBaseChangeCoord_injective
    (S : Type*) [CommRing S] [Algebra (∀ i, K i) S] :
    Function.Injective (piUniformBaseChangeCoord K P N hN S) := by
  intro x y hxy
  let A := ∀ i, K i
  let into := piUniformIntoFree K P N hN
  let down := piUniformFromFree K P N hN
  let e := TensorProduct.piScalarRight A S S (Fin N)
  have hinto : (LinearMap.baseChange S into) x = (LinearMap.baseChange S into) y := by
    change e ((LinearMap.baseChange S into) x) = e ((LinearMap.baseChange S into) y) at hxy
    exact e.injective hxy
  have hsplit : (LinearMap.baseChange S down).comp (LinearMap.baseChange S into) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, piUniformFromFree_comp_piUniformIntoFree,
      LinearMap.baseChange_id]
  have h := congrArg (fun z => (LinearMap.baseChange S down) z) hinto
  change ((LinearMap.baseChange S down).comp (LinearMap.baseChange S into)) x =
    ((LinearMap.baseChange S down).comp (LinearMap.baseChange S into)) y at h
  simpa [hsplit] using h

/-- Coordinates commute with the canonical cancellation equivalence for a further
scalar extension `S → T`. -/
lemma piUniformBaseChangeCoord_cancelBaseChange
    (S T : Type*) [CommRing S] [Algebra (∀ i, K i) S]
    [CommRing T] [Algebra S T] [Algebra (∀ i, K i) T]
    [IsScalarTower (∀ i, K i) S T]
    (x : S ⊗[∀ i, K i] (piOfUniformFinrank K P N hN).M) :
    piUniformBaseChangeCoord K P N hN T
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange (∀ i, K i) S T T
          (piOfUniformFinrank K P N hN).M)
          ((1 : T) ⊗ₜ[S] x)) =
      fun c => algebraMap S T (piUniformBaseChangeCoord K P N hN S x c) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero =>
      ext c
      simp
  | add x y hx hy =>
      ext c
      rw [TensorProduct.tmul_add, map_add]
      simp [hx, hy]
  | tmul s p =>
      ext c
      simp only [piUniformBaseChangeCoord, piUniformBaseChangeIntoFree,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        LinearMap.comp_apply, LinearMap.baseChange_tmul]
      change (TensorProduct.piScalarRight (∀ i, K i) T T (Fin N))
          ((s • (1 : T)) ⊗ₜ[∀ i, K i] (piUniformIntoFree K P N hN p)) c =
        algebraMap S T ((TensorProduct.piScalarRight (∀ i, K i) S S (Fin N))
          (s ⊗ₜ[∀ i, K i] (piUniformIntoFree K P N hN p)) c)
      simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
        Algebra.smul_def, map_mul]
      rw [IsScalarTower.algebraMap_apply ((i : I) → K i) S T]
      ring

/-- Coordinates commute with a further scalar extension.  After extending an
`S`-valued base-changed element to `T`, its finite-free coordinates are obtained
by applying the ring map `S → T` to the original coordinates. -/
lemma piUniformBaseChangeCoord_baseChange_assoc
    (S T : Type*) [CommRing S] [CommRing T]
    (f : (∀ i, K i) →+* S) (g : S →+* T)
    (x : baseChange_along f (piOfUniformFinrank K P N hN).M) :
    letI : Algebra (∀ i, K i) S := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra (∀ i, K i) T := (g.comp f).toAlgebra
    piUniformBaseChangeCoord K P N hN T
        ((baseChange_assoc f g (piOfUniformFinrank K P N hN).M)
          ((1 : T) ⊗ₜ[S] x)) =
      fun c => g (piUniformBaseChangeCoord K P N hN S x c) := by
  classical
  letI : Algebra (∀ i, K i) S := f.toAlgebra
  letI : Algebra S T := g.toAlgebra
  letI : Algebra (∀ i, K i) T := (g.comp f).toAlgebra
  change piUniformBaseChangeCoord K P N hN T
        ((baseChange_assoc f g (piOfUniformFinrank K P N hN).M)
          ((1 : T) ⊗ₜ[S] x)) =
      fun c => g (piUniformBaseChangeCoord K P N hN S x c)
  induction x using TensorProduct.induction_on with
  | zero =>
      ext c
      simp
  | add x y hx hy =>
      ext c
      rw [TensorProduct.tmul_add, map_add]
      simp [hx, hy]
  | tmul s p =>
      ext c
      simp [piUniformBaseChangeCoord, piUniformBaseChangeIntoFree, Algebra.smul_def]
      rfl

/-- Scalar version of `piUniformBaseChangeCoord_baseChange_assoc`. -/
lemma piUniformBaseChangeCoord_baseChange_assoc_tmul_apply
    (S T : Type*) [CommRing S] [CommRing T]
    (f : (∀ i, K i) →+* S) (g : S →+* T)
    (t : T) (x : baseChange_along f (piOfUniformFinrank K P N hN).M)
    (c : Fin N) :
    letI : Algebra (∀ i, K i) S := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra (∀ i, K i) T := (g.comp f).toAlgebra
    piUniformBaseChangeCoord K P N hN T
        ((baseChange_assoc f g (piOfUniformFinrank K P N hN).M)
          (t ⊗ₜ[S] x)) c =
      t * g (piUniformBaseChangeCoord K P N hN S x c) := by
  letI : Algebra (∀ i, K i) S := f.toAlgebra
  letI : Algebra S T := g.toAlgebra
  letI : Algebra (∀ i, K i) T := (g.comp f).toAlgebra
  have ht : (t ⊗ₜ[S] x : T ⊗[S] baseChange_along f (piOfUniformFinrank K P N hN).M) =
      t • ((1 : T) ⊗ₜ[S] x) := by
    rw [TensorProduct.smul_tmul']
    simp
  rw [ht]
  rw [map_smul]
  rw [map_smul]
  change t * (piUniformBaseChangeCoord K P N hN T
        ((baseChange_assoc f g (piOfUniformFinrank K P N hN).M)
          ((1 : T) ⊗ₜ[S] x)) c) = _
  have hcoord := congrFun
    (piUniformBaseChangeCoord_baseChange_assoc K P N hN S T f g x) c
  rw [hcoord]

/-- Version of `piUniformBaseChangeCoord_baseChange_assoc` using
`baseChange_assoc_eq`. -/
lemma piUniformBaseChangeCoord_baseChange_assoc_eq
    (S T : Type*) [CommRing S] [CommRing T]
    (f : (∀ i, K i) →+* S) (g : S →+* T) {ρ : (∀ i, K i) →+* T}
    (h : g.comp f = ρ)
    (x : baseChange_along f (piOfUniformFinrank K P N hN).M) :
    letI : Algebra (∀ i, K i) S := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra (∀ i, K i) T := ρ.toAlgebra
    piUniformBaseChangeCoord K P N hN T
        ((baseChange_assoc_eq f g h (piOfUniformFinrank K P N hN).M)
          ((1 : T) ⊗ₜ[S] x)) =
      fun c => g (piUniformBaseChangeCoord K P N hN S x c) := by
  subst h
  exact piUniformBaseChangeCoord_baseChange_assoc K P N hN S T f g x

/-- Pointwise version of `piUniformBaseChangeCoord_baseChange_assoc_eq`. -/
lemma piUniformBaseChangeCoord_baseChange_assoc_eq_apply
    (S T : Type*) [CommRing S] [CommRing T]
    (f : (∀ i, K i) →+* S) (g : S →+* T) {ρ : (∀ i, K i) →+* T}
    (h : g.comp f = ρ)
    (x : baseChange_along f (piOfUniformFinrank K P N hN).M)
    (c : Fin N) :
    letI : Algebra (∀ i, K i) S := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra (∀ i, K i) T := ρ.toAlgebra
    piUniformBaseChangeCoord K P N hN T
        ((baseChange_assoc_eq f g h (piOfUniformFinrank K P N hN).M)
          ((1 : T) ⊗ₜ[S] x)) c =
      g (piUniformBaseChangeCoord K P N hN S x c) := by
  exact congrFun (piUniformBaseChangeCoord_baseChange_assoc_eq K P N hN S T f g h x) c

/-- Product finite-free coordinates are unchanged by the canonical congruence
between base changes along propositionally equal ring homomorphisms. -/
lemma piUniformBaseChangeCoord_congrRingHom
    (S : Type*) [CommRing S]
    {f g : (∀ i, K i) →+* S} (h : f = g)
    (x : letI : Algebra (∀ i, K i) S := f.toAlgebra;
      S ⊗[∀ i, K i] (piOfUniformFinrank K P N hN).M)
    (c : Fin N) :
    letI : Algebra (∀ i, K i) S := f.toAlgebra
    piUniformBaseChangeCoord K P N hN S x c =
      letI : Algebra (∀ i, K i) S := g.toAlgebra
      piUniformBaseChangeCoord K P N hN S
        ((baseChangeCongrRingHom (f := f) (g := g) h
          (piOfUniformFinrank K P N hN).M) x) c := by
  subst h
  rfl

section AssocEqCongr

attribute [local irreducible] piUniformBaseChangeCoord baseChange_assoc baseChange_assoc_eq

/-- Coordinates after `baseChange_assoc_eq` agree with coordinates after ordinary
`baseChange_assoc`, after transporting the composite scalar map along the
specified equality. -/
lemma piUniformBaseChangeCoord_baseChange_assoc_eq_congr
    (S T : Type*) [CommRing S] [CommRing T]
    (f : (∀ i, K i) →+* S) (g : S →+* T) {ρ : (∀ i, K i) →+* T}
    (h : g.comp f = ρ)
    (z : letI : Algebra (∀ i, K i) S := f.toAlgebra;
      letI : Algebra S T := g.toAlgebra;
      T ⊗[S] (S ⊗[∀ i, K i] (piOfUniformFinrank K P N hN).M))
    (c : Fin N) :
    letI : Algebra (∀ i, K i) S := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra (∀ i, K i) T := (g.comp f).toAlgebra
    piUniformBaseChangeCoord K P N hN T
        ((baseChange_assoc f g (piOfUniformFinrank K P N hN).M) z) c =
      letI : Algebra (∀ i, K i) T := ρ.toAlgebra
      piUniformBaseChangeCoord K P N hN T
        ((baseChange_assoc_eq f g h (piOfUniformFinrank K P N hN).M) z) c := by
  letI : Algebra (∀ i, K i) S := f.toAlgebra
  letI : Algebra S T := g.toAlgebra
  letI : Algebra (∀ i, K i) T := (g.comp f).toAlgebra
  have hcoord := piUniformBaseChangeCoord_congrRingHom K P N hN T h
    ((baseChange_assoc f g (piOfUniformFinrank K P N hN).M) z) c
  rw [baseChange_assoc_eq_apply_eq_congr]
  exact hcoord

end AssocEqCongr

/-- Scalar version of `piUniformBaseChangeCoord_baseChange_assoc_eq_apply`. -/
lemma piUniformBaseChangeCoord_baseChange_assoc_eq_tmul_apply
    (S T : Type*) [CommRing S] [CommRing T]
    (f : (∀ i, K i) →+* S) (g : S →+* T) {ρ : (∀ i, K i) →+* T}
    (h : g.comp f = ρ)
    (t : T) (x : baseChange_along f (piOfUniformFinrank K P N hN).M)
    (c : Fin N) :
    letI : Algebra (∀ i, K i) S := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra (∀ i, K i) T := ρ.toAlgebra
    piUniformBaseChangeCoord K P N hN T
        ((baseChange_assoc_eq f g h (piOfUniformFinrank K P N hN).M)
          (t ⊗ₜ[S] x)) c =
      t * g (piUniformBaseChangeCoord K P N hN S x c) := by
  letI : Algebra (∀ i, K i) S := f.toAlgebra
  letI : Algebra S T := g.toAlgebra
  letI : Algebra (∀ i, K i) T := ρ.toAlgebra
  have ht : (t ⊗ₜ[S] x : T ⊗[S] baseChange_along f (piOfUniformFinrank K P N hN).M) =
      t • ((1 : T) ⊗ₜ[S] x) := by
    rw [TensorProduct.smul_tmul']
    simp
  rw [ht]
  rw [map_smul]
  rw [map_smul]
  change t * (piUniformBaseChangeCoord K P N hN T
        ((baseChange_assoc_eq f g h (piOfUniformFinrank K P N hN).M)
          ((1 : T) ⊗ₜ[S] x)) c) = _
  rw [piUniformBaseChangeCoord_baseChange_assoc_eq_apply]

section AssocEqSum

attribute [local irreducible] piUniformBaseChangeCoord baseChange_assoc_eq

/-- Coordinate formula for a finite sum of scalar multiples of `1 ⊗ x` after
`baseChange_assoc_eq`. -/
lemma piUniformBaseChangeCoord_baseChange_assoc_eq_sum_smul_one_tmul_apply
    {ι : Type*} [Fintype ι]
    (S T : Type*) [CommRing S] [CommRing T]
    (f : (∀ i, K i) →+* S) (g : S →+* T) {ρ : (∀ i, K i) →+* T}
    (h : g.comp f = ρ)
    (a : ι → T)
    (x : ι → baseChange_along f (piOfUniformFinrank K P N hN).M)
    (c : Fin N) :
    letI : Algebra (∀ i, K i) S := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra (∀ i, K i) T := ρ.toAlgebra
    piUniformBaseChangeCoord K P N hN T
        ((baseChange_assoc_eq f g h (piOfUniformFinrank K P N hN).M)
          (∑ k : ι, a k • ((1 : T) ⊗ₜ[S] x k))) c =
      ∑ k : ι, a k * g (piUniformBaseChangeCoord K P N hN S (x k) c) := by
  classical
  letI : Algebra (∀ i, K i) S := f.toAlgebra
  letI : Algebra S T := g.toAlgebra
  letI : Algebra (∀ i, K i) T := ρ.toAlgebra
  let Amap := (baseChange_assoc_eq f g h (piOfUniformFinrank K P N hN).M).toLinearMap
  let L := piUniformBaseChangeCoord K P N hN T
  let base : ι → T ⊗[S] baseChange_along f (piOfUniformFinrank K P N hN).M := fun k =>
    (1 : T) ⊗ₜ[S] x k
  change L (Amap (∑ k : ι, a k • base k)) c =
    ∑ k : ι, a k * g (piUniformBaseChangeCoord K P N hN S (x k) c)
  calc
    L (Amap (∑ k : ι, a k • base k)) c =
        L (∑ k : ι, Amap (a k • base k)) c := by
          exact congrArg (fun q => L q c) (map_sum Amap (fun k : ι => a k • base k) Finset.univ)
    _ = (∑ k : ι, L (Amap (a k • base k))) c := by
          exact congrFun (map_sum L (fun k : ι => Amap (a k • base k)) Finset.univ) c
    _ = ∑ k : ι, L (Amap (a k • base k)) c := by
          rw [Finset.sum_apply]
    _ = ∑ k : ι, a k * g (piUniformBaseChangeCoord K P N hN S (x k) c) := by
          apply Finset.sum_congr rfl
          intro k _
          calc
            L (Amap (a k • base k)) c = L (a k • Amap (base k)) c := by
              exact congrArg (fun q => L q c) (map_smul Amap (a k) (base k))
            _ = (a k • L (Amap (base k))) c := by
              exact congrFun (map_smul L (a k) (Amap (base k))) c
            _ = a k * L (Amap (base k)) c := rfl
            _ = a k * g (piUniformBaseChangeCoord K P N hN S (x k) c) := by
              refine congrArg (fun t => a k * t) ?_
              dsimp [base, Amap, L]
              have hone := piUniformBaseChangeCoord_baseChange_assoc_eq_tmul_apply
                K P N hN S T f g h (1 : T) (x k) c
              simpa using hone

end AssocEqSum

/-- If a finite-free coordinate vector already comes from a base-changed
`piOfUniformFinrank` element, then applying the explicit split retraction and
then taking coordinates recovers the same vector. -/
lemma piUniformBaseChangeCoord_fromFree_of_eq
    (S : Type*) [CommRing S] [Algebra (∀ i, K i) S]
    (v : Fin N → S)
    (y : S ⊗[∀ i, K i] (piOfUniformFinrank K P N hN).M)
    (hy : piUniformBaseChangeCoord K P N hN S y = v) :
    piUniformBaseChangeCoord K P N hN S
      ((LinearMap.baseChange S (piUniformFromFree K P N hN))
        ((TensorProduct.piScalarRight (∀ i, K i) S S (Fin N)).symm v)) = v := by
  classical
  let A := ∀ i, K i
  let into := piUniformIntoFree K P N hN
  let down := piUniformFromFree K P N hN
  let e := TensorProduct.piScalarRight A S S (Fin N)
  subst v
  change e ((LinearMap.baseChange S into)
      ((LinearMap.baseChange S down) (e.symm (e ((LinearMap.baseChange S into) y))))) =
    e ((LinearMap.baseChange S into) y)
  rw [LinearEquiv.symm_apply_apply]
  have hsplit : (LinearMap.baseChange S down).comp (LinearMap.baseChange S into) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, piUniformFromFree_comp_piUniformIntoFree,
      LinearMap.baseChange_id]
  change e ((LinearMap.baseChange S into)
      (((LinearMap.baseChange S down).comp (LinearMap.baseChange S into)) y)) = _
  rw [hsplit]
  rfl

/-- The coordinate projector onto the finite-free coordinate image of
`piOfUniformFinrank`, after base change to an algebra `S`. -/
noncomputable def piUniformProjectorCoord
    (S : Type*) [CommRing S] [Algebra (∀ i, K i) S] :
    (Fin N → S) →ₗ[S] (Fin N → S) :=
  (piUniformBaseChangeCoord K P N hN S).comp
    ((LinearMap.baseChange S (piUniformFromFree K P N hN)).comp
      (TensorProduct.piScalarRight (∀ i, K i) S S (Fin N)).symm.toLinearMap)

/-- A finite-free vector is recovered by applying the explicit split retraction
and taking coordinates iff it is fixed by the coordinate projector. -/
lemma piUniformBaseChangeCoord_fromFree_eq_iff_projector
    (S : Type*) [CommRing S] [Algebra (∀ i, K i) S]
    (v : Fin N → S) :
    piUniformBaseChangeCoord K P N hN S
      ((LinearMap.baseChange S (piUniformFromFree K P N hN))
        ((TensorProduct.piScalarRight (∀ i, K i) S S (Fin N)).symm v)) = v ↔
      piUniformProjectorCoord K P N hN S v = v := by
  rfl

/-- Coordinate vectors of actual base-changed `piOfUniformFinrank` elements are
fixed by the coordinate projector. -/
lemma piUniformProjectorCoord_baseChangeCoord
    (S : Type*) [CommRing S] [Algebra (∀ i, K i) S]
    (y : S ⊗[∀ i, K i] (piOfUniformFinrank K P N hN).M) :
    piUniformProjectorCoord K P N hN S
      (piUniformBaseChangeCoord K P N hN S y) =
    piUniformBaseChangeCoord K P N hN S y := by
  classical
  let A := ∀ i, K i
  let into := piUniformIntoFree K P N hN
  let down := piUniformFromFree K P N hN
  let e := TensorProduct.piScalarRight A S S (Fin N)
  change e ((LinearMap.baseChange S into)
      ((LinearMap.baseChange S down) (e.symm (e ((LinearMap.baseChange S into) y))))) =
    e ((LinearMap.baseChange S into) y)
  rw [LinearEquiv.symm_apply_apply]
  have hsplit : (LinearMap.baseChange S down).comp (LinearMap.baseChange S into) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, piUniformFromFree_comp_piUniformIntoFree,
      LinearMap.baseChange_id]
  change e ((LinearMap.baseChange S into)
      (((LinearMap.baseChange S down).comp (LinearMap.baseChange S into)) y)) = _
  rw [hsplit]
  rfl

/-- Matrix coefficients of the coordinate projector onto the finite-free image of
`piOfUniformFinrank`. -/
noncomputable def piUniformProjectorMatrix (d c : Fin N) : (∀ i, K i) :=
  piUniformIntoFree K P N hN (piUniformFromFree K P N hN (Pi.single c 1)) d

/-- The coordinate projector sends a coordinate basis vector to the corresponding
column of its matrix. -/
lemma piUniformProjectorCoord_single
    (S : Type*) [CommRing S] [Algebra (∀ i, K i) S]
    (d c : Fin N) :
    piUniformProjectorCoord K P N hN S (Pi.single c (1 : S)) d =
      algebraMap (∀ i, K i) S (piUniformProjectorMatrix K P N hN d c) := by
  classical
  simp [piUniformProjectorCoord, piUniformBaseChangeCoord,
    piUniformBaseChangeIntoFree, piUniformProjectorMatrix, Algebra.smul_def]

private lemma fin_sum_single_eq {S : Type*} [AddCommMonoid S]
    (v : Fin N → S) :
    (∑ c : Fin N, Pi.single c (v c)) = v := by
  ext d
  simp

/-- Finite matrix formula for the coordinate projector after any base change. -/
lemma piUniformProjectorCoord_apply
    (S : Type*) [CommRing S] [Algebra (∀ i, K i) S]
    (v : Fin N → S) (d : Fin N) :
    piUniformProjectorCoord K P N hN S v d =
      ∑ c : Fin N,
        algebraMap (∀ i, K i) S (piUniformProjectorMatrix K P N hN d c) * v c := by
  classical
  calc
    piUniformProjectorCoord K P N hN S v d =
        piUniformProjectorCoord K P N hN S (∑ c : Fin N, Pi.single c (v c)) d := by
          rw [fin_sum_single_eq]
    _ = (∑ c : Fin N, piUniformProjectorCoord K P N hN S (Pi.single c (v c)) :
          Fin N → S) d := by
          rw [map_sum]
    _ = ∑ c : Fin N, piUniformProjectorCoord K P N hN S (Pi.single c (v c)) d := by
          simp
    _ = ∑ c : Fin N,
          algebraMap (∀ i, K i) S (piUniformProjectorMatrix K P N hN d c) * v c := by
          apply Finset.sum_congr rfl
          intro c _
          have hsingle := piUniformProjectorCoord_single K P N hN S d c
          have hsmul : Pi.single c (v c) = v c • Pi.single c (1 : S) := by
            ext e
            by_cases h : e = c
            · subst e
              simp
            · rw [Pi.single_eq_of_ne h]
              simp [Pi.single_eq_of_ne h]
          rw [hsmul, map_smul]
          change (v c * (piUniformProjectorCoord K P N hN S (Pi.single c (1 : S)) d)) = _
          rw [hsingle]
          ring

/-- The split retraction from the uniform finite free module onto a single fiber. -/
noncomputable def fiberCoordFromFree (i : I) :
    (Fin N → K i) →ₗ[K i] (P i).M :=
  fiberFromFree K (fun i => (P i).M) N hN i

/-- The fiber free-module retraction is left inverse to the fiber injection. -/
lemma fiberCoordFromFree_comp_fiberCoordIntoFree (i : I) :
    (fiberCoordFromFree K P N hN i).comp (fiberCoordIntoFree K P N i) = LinearMap.id :=
  fiberFromFree_comp_fiberIntoFree K (fun i => (P i).M) N hN i

/-- The single-fiber coordinate map after base change is injective. -/
lemma fiberBaseChangeCoord_injective
    (hN : ∀ i, Module.finrank (K i) (P i).M ≤ N)
    (i : I) (S : Type*) [CommRing S] [Algebra (K i) S] :
    Function.Injective (fiberBaseChangeCoord K P N i S) := by
  intro x y hxy
  let into := fiberCoordIntoFree K P N i
  let down := fiberCoordFromFree K P N hN i
  let e := TensorProduct.piScalarRight (K i) S S (Fin N)
  have hinto : (LinearMap.baseChange S into) x = (LinearMap.baseChange S into) y := by
    change e ((LinearMap.baseChange S into) x) = e ((LinearMap.baseChange S into) y) at hxy
    exact e.injective hxy
  have hsplit : (LinearMap.baseChange S down).comp (LinearMap.baseChange S into) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, fiberCoordFromFree_comp_fiberCoordIntoFree,
      LinearMap.baseChange_id]
  have h := congrArg (fun z => (LinearMap.baseChange S down) z) hinto
  change ((LinearMap.baseChange S down).comp (LinearMap.baseChange S into)) x =
    ((LinearMap.baseChange S down).comp (LinearMap.baseChange S into)) y at h
  simpa [hsplit] using h

/-- The coordinate projector onto the finite-free coordinate image of one fiber,
after base change to an algebra `S`. -/
noncomputable def fiberBaseChangeProjectorCoord
    (i : I) (S : Type*) [CommRing S] [Algebra (K i) S] :
    (Fin N → S) →ₗ[S] (Fin N → S) :=
  (fiberBaseChangeCoord K P N i S).comp
    ((LinearMap.baseChange S (fiberCoordFromFree K P N hN i)).comp
      (TensorProduct.piScalarRight (K i) S S (Fin N)).symm.toLinearMap)

/-- Coordinate vectors of actual base-changed fiber elements are fixed by the
fiber coordinate projector. -/
lemma fiberBaseChangeProjectorCoord_baseChangeCoord
    (i : I) (S : Type*) [CommRing S] [Algebra (K i) S]
    (y : S ⊗[K i] (P i).M) :
    fiberBaseChangeProjectorCoord K P N hN i S
      (fiberBaseChangeCoord K P N i S y) =
    fiberBaseChangeCoord K P N i S y := by
  let into := fiberCoordIntoFree K P N i
  let down := fiberCoordFromFree K P N hN i
  let e := TensorProduct.piScalarRight (K i) S S (Fin N)
  change e ((LinearMap.baseChange S into)
      ((LinearMap.baseChange S down) (e.symm (e ((LinearMap.baseChange S into) y))))) =
    e ((LinearMap.baseChange S into) y)
  rw [LinearEquiv.symm_apply_apply]
  have hsplit : (LinearMap.baseChange S down).comp (LinearMap.baseChange S into) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, fiberCoordFromFree_comp_fiberCoordIntoFree,
      LinearMap.baseChange_id]
  change e ((LinearMap.baseChange S into)
      (((LinearMap.baseChange S down).comp (LinearMap.baseChange S into)) y)) = _
  rw [hsplit]
  rfl

/-- Matrix coefficients of the coordinate projector on one fiber. -/
noncomputable def fiberProjectorMatrix (i : I) (d c : Fin N) : K i :=
  fiberCoordIntoFree K P N i (fiberCoordFromFree K P N hN i (Pi.single c 1)) d

/-- The product projector matrix evaluates to the fiber projector matrix. -/
@[simp]
lemma piUniformProjectorMatrix_apply (d c : Fin N) (i : I) :
    piUniformProjectorMatrix K P N hN d c i = fiberProjectorMatrix K P N hN i d c := by
  dsimp [piUniformProjectorMatrix, piUniformIntoFree, piUniformFromFree,
    fiberProjectorMatrix, fiberCoordIntoFree, fiberCoordFromFree,
    prodModuleIntoFree, prodModuleFromFree]
  have hsingle : (fun j : Fin N => ((Pi.single c (1 : ∀ i, K i) :
        Fin N → (∀ i, K i)) j) i) = Pi.single c (1 : K i) := by
    ext j
    by_cases h : j = c
    · subst j
      simp
    · simp [Pi.single_eq_of_ne h]
  change (fiberIntoFree K (fun i => (P i).M) N i)
      ((fiberFromFree K (fun i => (P i).M) N hN i)
        (fun j : Fin N => ((Pi.single c (1 : ∀ i, K i) : Fin N → (∀ i, K i)) j) i)) d =
    (fiberIntoFree K (fun i => (P i).M) N i)
      ((fiberFromFree K (fun i => (P i).M) N hN i) (Pi.single c (1 : K i))) d
  rw [hsingle]

/-- The fiber coordinate projector sends a coordinate basis vector to the
corresponding column of its matrix. -/
lemma fiberBaseChangeProjectorCoord_single
    (i : I) (S : Type*) [CommRing S] [Algebra (K i) S]
    (d c : Fin N) :
    fiberBaseChangeProjectorCoord K P N hN i S (Pi.single c (1 : S)) d =
      algebraMap (K i) S (fiberProjectorMatrix K P N hN i d c) := by
  classical
  simp [fiberBaseChangeProjectorCoord, fiberBaseChangeCoord,
    fiberProjectorMatrix, Algebra.smul_def]

/-- Finite matrix formula for the coordinate projector on one fiber. -/
lemma fiberBaseChangeProjectorCoord_apply
    (i : I) (S : Type*) [CommRing S] [Algebra (K i) S]
    (v : Fin N → S) (d : Fin N) :
    fiberBaseChangeProjectorCoord K P N hN i S v d =
      ∑ c : Fin N,
        algebraMap (K i) S (fiberProjectorMatrix K P N hN i d c) * v c := by
  classical
  calc
    fiberBaseChangeProjectorCoord K P N hN i S v d =
        fiberBaseChangeProjectorCoord K P N hN i S (∑ c : Fin N, Pi.single c (v c)) d := by
          rw [fin_sum_single_eq]
    _ = (∑ c : Fin N, fiberBaseChangeProjectorCoord K P N hN i S (Pi.single c (v c)) :
          Fin N → S) d := by
          rw [map_sum]
    _ = ∑ c : Fin N, fiberBaseChangeProjectorCoord K P N hN i S (Pi.single c (v c)) d := by
          simp
    _ = ∑ c : Fin N,
          algebraMap (K i) S (fiberProjectorMatrix K P N hN i d c) * v c := by
          apply Finset.sum_congr rfl
          intro c _
          have hsingle := fiberBaseChangeProjectorCoord_single K P N hN i S d c
          have hsmul : Pi.single c (v c) = v c • Pi.single c (1 : S) := by
            ext e
            by_cases h : e = c
            · subst e
              simp
            · rw [Pi.single_eq_of_ne h]
              simp [Pi.single_eq_of_ne h]
          rw [hsmul, map_smul]
          change (v c * (fiberBaseChangeProjectorCoord K P N hN i S (Pi.single c (1 : S)) d)) = _
          rw [hsingle]
          ring

end FiniteProjectiveModule

end Novikov.Miscellany
