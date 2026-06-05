import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.CategoryTheory.Category.Basic

namespace Novikov.Miscellany

open LinearMap TensorProduct

/-- A bundled type for finite projective modules. -/
structure FiniteProjectiveModule (A : Type*) [CommRing A] where
  M : Type*
  [instAddCommGroup : AddCommGroup M]
  [instModule : Module A M]
  [instFinite : Module.Finite A M]
  [instProjective : Module.Projective A M]

attribute [instance] FiniteProjectiveModule.instAddCommGroup FiniteProjectiveModule.instModule
  FiniteProjectiveModule.instFinite FiniteProjectiveModule.instProjective

instance {A : Type*} [CommRing A] : CategoryTheory.Category (FiniteProjectiveModule A) where
  Hom M N := M.M →ₗ[A] N.M
  id _ := LinearMap.id
  comp f g := g.comp f
  id_comp f := LinearMap.comp_id f
  comp_id f := LinearMap.id_comp f
  assoc f g h := LinearMap.comp_assoc f g h

section

variable {R : Type*} [CommRing R]

/-- If fM : F -> M is a retraction with gM : M -> F its section, 
    and fN : G -> N is a retraction with gN : N -> G its section,
    then Hom(M, N) is a retract of Hom(F, G). -/
private def homUP {M N F G : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
    (gN : N →ₗ[R] G) (fM : F →ₗ[R] M) : (M →ₗ[R] N) →ₗ[R] (F →ₗ[R] G) where
  toFun := fun f => gN.comp (f.comp fM)
  map_add' := fun f g => by ext; simp
  map_smul' := fun r f => by ext; simp

private def homDOWN {M N F G : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
    (fN : G →ₗ[R] N) (gM : M →ₗ[R] F) : (F →ₗ[R] G) →ₗ[R] (M →ₗ[R] N) where
  toFun := fun f => fN.comp (f.comp gM)
  map_add' := fun f g => by ext; simp
  map_smul' := fun r f => by ext; simp

private theorem homDOWN_homUP {M N F G : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
    (gN : N →ₗ[R] G) (fM : F →ₗ[R] M) (fN : G →ₗ[R] N) (gM : M →ₗ[R] F)
    (hM : fM.comp gM = .id) (hN : fN.comp gN = .id) (f : M →ₗ[R] N) :
    homDOWN fN gM (homUP gN fM f) = f := by
  apply LinearMap.ext; intro x
  simp only [homDOWN, homUP, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
  rw [← LinearMap.comp_apply fM gM x, hM, LinearMap.id_apply]
  rw [← LinearMap.comp_apply fN gN (f x), hN, LinearMap.id_apply]

private theorem homDOWN_comp_homUP {M N F G : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
    (gN : N →ₗ[R] G) (fM : F →ₗ[R] M) (fN : G →ₗ[R] N) (gM : M →ₗ[R] F)
    (hM : fM.comp gM = .id) (hN : fN.comp gN = .id) :
    (homDOWN fN gM).comp (homUP gN fM) = LinearMap.id :=
  LinearMap.ext (homDOWN_homUP gN fM fN gM hM hN)

/-- If M and N are finite projective over R, then Hom(M, N) is finite over R. -/
instance linearMap_finite_projective {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] : Module.Finite R (M →ₗ[R] N) := by
  obtain ⟨nM, fM, gM, _, _, hM⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  obtain ⟨nN, fN, gN, _, _, hN⟩ := Module.Finite.exists_comp_eq_id_of_projective R N
  exact Module.Finite.of_surjective (homDOWN fN gM)
    (fun f => ⟨homUP gN fM f, LinearMap.ext_iff.mp (homDOWN_comp_homUP gN fM fN gM hM hN) f⟩)

/-- If M and N are finite projective over R, then Hom(M, N) is projective over R. -/
instance linearMap_projective_projective {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] : Module.Projective R (M →ₗ[R] N) := by
  obtain ⟨nM, fM, gM, _, _, hM⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  obtain ⟨nN, fN, gN, _, _, hN⟩ := Module.Finite.exists_comp_eq_id_of_projective R N
  exact Module.Projective.of_split (homUP gN fM) (homDOWN fN gM)
    (homDOWN_comp_homUP gN fM fN gM hM hN)

/-- The Hom between two finite projective modules as a finite projective module. -/
noncomputable def FiniteProjectiveModule.homModule (M₀ N₀ : FiniteProjectiveModule R) :
    FiniteProjectiveModule R where
  M := M₀.M →ₗ[R] N₀.M
  instFinite := linearMap_finite_projective (M := M₀.M) (N := N₀.M)
  instProjective := linearMap_projective_projective (M := M₀.M) (N := N₀.M)

/-- The natural map S ⊗[R] (M →ₗ[R] N) →ₗ[S] (S ⊗[R] M →ₗ[S] S ⊗[R] N) -/
def homBaseChangeMap {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (S : Type*) [CommRing S] [Algebra R S] :
    S ⊗[R] (M →ₗ[R] N) →ₗ[S] (S ⊗[R] M →ₗ[S] S ⊗[R] N) :=
  TensorProduct.AlgebraTensorModule.lift
    ({ toFun := fun s => s • LinearMap.baseChangeHom R S M N,
       map_add' := fun s1 s2 => by ext; simp [add_smul],
       map_smul' := fun s1 s2 => by ext; simp [mul_smul] } : S →ₗ[S] (M →ₗ[R] N) →ₗ[R] _)

private theorem homBaseChangeMap_comp_homUP {M N F G : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
    (gN : N →ₗ[R] G) (fM : F →ₗ[R] M) (S : Type*) [CommRing S] [Algebra R S] :
    (homUP (LinearMap.baseChange S gN) (LinearMap.baseChange S fM)) ∘ₗ
      (homBaseChangeMap (R := R) (M := M) (N := N) S) =
    (homBaseChangeMap (R := R) (M := F) (N := G) S) ∘ₗ
      (LinearMap.baseChange S (homUP gN fM)) := by
  let up_hom := homUP (LinearMap.baseChange S gN) (LinearMap.baseChange S fM)
  let upS := LinearMap.baseChange S (homUP gN fM)
  apply LinearMap.ext_iff.mpr; intro f_tensor; apply LinearMap.ext_iff.mpr; intro m_tensor
  change (up_hom (homBaseChangeMap S f_tensor)) m_tensor =
    (homBaseChangeMap S (upS f_tensor)) m_tensor
  refine TensorProduct.induction_on (motive := fun x => (up_hom (homBaseChangeMap S x)) m_tensor =
    (homBaseChangeMap S (upS x)) m_tensor) f_tensor ?_ ?_ ?_
  · simp
  · intro s f
    refine TensorProduct.induction_on (motive := fun y => (up_hom (homBaseChangeMap S (s ⊗ₜ f))) y =
      (homBaseChangeMap S (upS (s ⊗ₜ f))) y) m_tensor ?_ ?_ ?_
    · simp
    · intro s' m; simp [homBaseChangeMap, up_hom, upS, homUP, baseChangeHom,
        LinearMap.baseChange_tmul]
    · intro m1 m2 hm1 hm2; rw [map_add, map_add, hm1, hm2]
  · intro f1 f2 hf1 hf2
    simp only [map_add, LinearMap.add_apply]
    rw [hf1, hf2]

private theorem homBaseChangeMap_comp_homDOWN {M N F G : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
    (fN : G →ₗ[R] N) (gM : M →ₗ[R] F) (S : Type*) [CommRing S] [Algebra R S] :
    (homBaseChangeMap (R := R) (M := M) (N := N) S) ∘ₗ
      (LinearMap.baseChange S (homDOWN fN gM)) =
    (homDOWN (LinearMap.baseChange S fN) (LinearMap.baseChange S gM)) ∘ₗ
      (homBaseChangeMap (R := R) (M := F) (N := G) S) := by
  let down_hom := homDOWN (LinearMap.baseChange S fN) (LinearMap.baseChange S gM)
  let downS := LinearMap.baseChange S (homDOWN fN gM)
  apply LinearMap.ext_iff.mpr; intro f_tensor; apply LinearMap.ext_iff.mpr; intro m_tensor
  change (homBaseChangeMap S (downS f_tensor)) m_tensor =
    (down_hom (homBaseChangeMap S f_tensor)) m_tensor
  refine TensorProduct.induction_on (motive := fun x => (homBaseChangeMap S (downS x)) m_tensor =
    (down_hom (homBaseChangeMap S x)) m_tensor) f_tensor ?_ ?_ ?_
  · simp
  · intro s f
    refine TensorProduct.induction_on (motive := fun y => (homBaseChangeMap S (downS (s ⊗ₜ f))) y =
      (down_hom (homBaseChangeMap S (s ⊗ₜ f))) y) m_tensor ?_ ?_ ?_
    · simp
    · intro s' m; simp [homBaseChangeMap, down_hom, downS, homDOWN, baseChangeHom,
        LinearMap.baseChange_tmul]
    · intro m1 m2 hm1 hm2; rw [map_add, map_add, hm1, hm2]
  · intro f1 f2 hf1 hf2
    simp only [map_add, LinearMap.add_apply]
    rw [hf1, hf2]

/-- Hom commutes with base change for finite projective modules. -/
theorem homBaseChange_bijective {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]
    (S : Type*) [CommRing S] [Algebra R S] :
    Function.Bijective (homBaseChangeMap (R := R) (M := M) (N := N) S) := by
  obtain ⟨nM, fM, gM, _, _, hM⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  obtain ⟨nN, fN, gN, _, _, hN⟩ := Module.Finite.exists_comp_eq_id_of_projective R N
  let F := Fin nM → R
  let G := Fin nN → R
  let up := homUP gN fM
  let down := homDOWN fN gM
  let upS := LinearMap.baseChange S up
  let downS := LinearMap.baseChange S down
  let up_hom := homUP (LinearMap.baseChange S gN) (LinearMap.baseChange S fM)
  let down_hom := homDOWN (LinearMap.baseChange S fN) (LinearMap.baseChange S gM)
  have h_free : Function.Bijective (homBaseChangeMap (R := R) (M := F) (N := G) S) := by
    let jF : IsBaseChange S ((TensorProduct.mk R S F) 1) := TensorProduct.isBaseChange R F S
    let jG : IsBaseChange S ((TensorProduct.mk R S G) 1) := TensorProduct.isBaseChange R G S
    have h_ibc : IsBaseChange S (jF.linearMapLeftRightHom (β := (TensorProduct.mk R S G) 1)) :=
      jF.linearMapLeftRight jG
    have hbc_eq : ∀ f : F →ₗ[R] G, LinearMap.baseChange S f =
        jF.linearMapLeftRightHom (β := (TensorProduct.mk R S G) 1) f := by
      intro f
      apply LinearMap.ext
      intro y
      refine TensorProduct.induction_on (motive := fun y => LinearMap.baseChange S f y =
          jF.linearMapLeftRightHom (β := (TensorProduct.mk R S G) 1) f y) y ?_ ?_ ?_
      · simp
      · intro s' x
        rw [LinearMap.baseChange_tmul]
        have h1 : s' ⊗ₜ[R] x = s' • ((TensorProduct.mk R S F) 1 x) := by
          change s' ⊗ₜ[R] x = s' • (1 ⊗ₜ[R] x : S ⊗[R] F)
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h1, LinearMap.map_smul]
        rw [IsBaseChange.linearMapLeftRightHom_comp_apply]
        change s' ⊗ₜ[R] f x = s' • (1 ⊗ₜ[R] f x : S ⊗[R] G)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      · intro y1 y2 hy1 hy2
        rw [map_add, map_add, hy1, hy2]
    have hmap : (homBaseChangeMap (R := R) (M := F) (N := G) S) = h_ibc.equiv.toLinearMap := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro s f
      change homBaseChangeMap S (s ⊗ₜ f) = h_ibc.equiv (s ⊗ₜ f)
      rw [h_ibc.equiv_tmul]
      change s • LinearMap.baseChange S f =
          s • jF.linearMapLeftRightHom (β := (TensorProduct.mk R S G) 1) f
      rw [hbc_eq]
    rw [hmap]
    exact h_ibc.equiv.bijective
  have h_comm : up_hom ∘ₗ (homBaseChangeMap (M := M) (N := N) S) =
      (homBaseChangeMap (M := F) (N := G) S) ∘ₗ upS :=
    homBaseChangeMap_comp_homUP gN fM S
  have h_comm_down : (homBaseChangeMap (M := M) (N := N) S) ∘ₗ downS =
      down_hom ∘ₗ (homBaseChangeMap (M := F) (N := G) S) :=
    homBaseChangeMap_comp_homDOWN fN gM S
  let k := LinearEquiv.ofBijective _ h_free
  let inv : (S ⊗[R] M →ₗ[S] S ⊗[R] N) →ₗ[S] S ⊗[R] (M →ₗ[R] N) := downS ∘ₗ (k.symm.toLinearMap ∘ₗ up_hom)
  have hcomp_du : down.comp up = LinearMap.id := homDOWN_comp_homUP gN fM fN gM hM hN
  have h_dnS_upS : ∀ y, downS (upS y) = y := fun y => by
    change LinearMap.baseChange S down (LinearMap.baseChange S up y) = y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp_du, LinearMap.baseChange_id]
    rfl
  have h_dn_up : ∀ h y, down_hom (up_hom h) y = h y := by
    intro h y
    change (LinearMap.baseChange S fN)
        ((LinearMap.baseChange S gN) (h ((LinearMap.baseChange S fM)
          ((LinearMap.baseChange S gM) y)))) = h y
    have e1 : (LinearMap.baseChange S fM) ((LinearMap.baseChange S gM) y) = y := by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hM, LinearMap.baseChange_id]; rfl
    have e2 : ∀ z, (LinearMap.baseChange S fN) ((LinearMap.baseChange S gN) z) = z := fun z => by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hN, LinearMap.baseChange_id]; rfl
    rw [e1, e2]
  have h_left : ∀ x, inv (homBaseChangeMap S x) = x := fun x => by
    refine TensorProduct.induction_on (motive := fun x => inv (homBaseChangeMap S x) = x) x ?_ ?_ ?_
    · simp
    · intro s f
      change downS (k.symm (up_hom (homBaseChangeMap S (s ⊗ₜ[R] f)))) = s ⊗ₜ[R] f
      rw [← LinearMap.comp_apply up_hom (homBaseChangeMap S), h_comm, LinearMap.comp_apply]
      change downS (k.symm (k (upS (s ⊗ₜ[R] f)))) = s ⊗ₜ[R] f
      rw [k.symm_apply_apply, h_dnS_upS]
    · intro x y hx hy; rw [map_add, map_add, hx, hy]
  have h_right : ∀ x, homBaseChangeMap S (inv x) = x := fun x => by
    apply LinearMap.ext; intro m_S
    change homBaseChangeMap S (downS (k.symm (up_hom x))) m_S = x m_S
    rw [← LinearMap.comp_apply (homBaseChangeMap S) downS, h_comm_down, LinearMap.comp_apply]
    change down_hom (k (k.symm (up_hom x))) m_S = x m_S
    rw [k.apply_symm_apply, h_dn_up]
  exact ⟨Function.LeftInverse.injective h_left, Function.RightInverse.surjective h_right⟩

/-- Formula for `homBaseChangeMap` on a pure tensor. -/
@[simp]
theorem homBaseChangeMap_tmul {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (S : Type*) [CommRing S] [Algebra R S] (s : S) (f : M →ₗ[R] N) :
    homBaseChangeMap (R := R) (M := M) (N := N) S (s ⊗ₜ[R] f) =
      s • LinearMap.baseChange S f := by
  unfold homBaseChangeMap
  rw [TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul]
  rfl

/-- Hom commutes with base change for finite projective modules. -/
noncomputable def homBaseChangeEquiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (S : Type*) [CommRing S] [Algebra R S] :
    (S ⊗[R] (M →ₗ[R] N)) ≃ₗ[S] (S ⊗[R] M →ₗ[S] S ⊗[R] N) :=
  LinearEquiv.ofBijective (homBaseChangeMap (R := R) (M := M) (N := N) S) (homBaseChange_bijective S)

/-- Formula for `homBaseChangeEquiv` on a pure tensor. -/
@[simp]
theorem homBaseChangeEquiv_tmul {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (S : Type*) [CommRing S] [Algebra R S] (s : S) (f : M →ₗ[R] N) :
    homBaseChangeEquiv (R := R) (M := M) (N := N) S (s ⊗ₜ[R] f) =
      s • LinearMap.baseChange S f :=
  homBaseChangeMap_tmul S s f

/-- Base-changing the double-dual evaluation map and then applying the
Hom/base-change equivalence is evaluation after base change. -/
lemma homBaseChangeEquiv_baseChange_eval_apply {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (S : Type*) [CommRing S] [Algebra R S]
    (x : S ⊗[R] M) (y : S ⊗[R] Module.Dual R M) :
    (homBaseChangeEquiv (R := R) (M := Module.Dual R M) (N := R) S
      ((LinearMap.baseChange S (Module.Dual.eval R M)) x)) y =
    (homBaseChangeEquiv (R := R) (M := M) (N := R) S y) x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul s m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
      | tmul t f =>
          rw [LinearMap.baseChange_tmul]
          rw [homBaseChangeEquiv_tmul]
          rw [homBaseChangeEquiv_tmul]
          simp only [LinearMap.smul_apply, LinearMap.baseChange_tmul, Module.Dual.eval_apply]
          change (s * t) ⊗ₜ[R] f m = (t * s) ⊗ₜ[R] f m
          rw [mul_comm]

/-- Base change preserves finite projectivity: if `P` is a finite projective
`R`-module, then `S ⊗[R] P` is a finite projective `S`-module. -/
lemma baseChange_projective {S : Type*} [CommRing S] [Algebra R S]
    (P : Type*) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] :
    Module.Projective S (TensorProduct R S P) := by
  infer_instance

end

/-- Base change of a finite projective module along a ring homomorphism. -/
noncomputable def FiniteProjectiveModule.baseChange {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (P : FiniteProjectiveModule A) : FiniteProjectiveModule B :=
  letI : Algebra A B := f.toAlgebra
  { M := B ⊗[A] P.M
    instFinite := inferInstance
    instProjective := baseChange_projective (R := A) (S := B) (P := P.M)
  }

end Novikov.Miscellany
