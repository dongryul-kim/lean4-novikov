import Novikov.Isocrystal.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Constant Novikov isocrystals and the `ConstIsocrystal` functor

This file constructs the functor `vectToNovIsoc` from finite projective `A`-modules
to Novikov isocrystals, and proves it is fully faithful.

## Main definitions

* `vectToNovIsoc A`: The functor from finite projective `A`-modules to Novikov isocrystals.

## Main results

* `vectToNovIsoc_fullyFaithful`: The functor `vectToNovIsoc` is fully faithful.
-/

open CategoryTheory
open TensorProduct

namespace Novikov
open Miscellany
variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]

section Isocrystal
variable {A : Type*} [CommRing A]

namespace NovikovIsocrystal

/-- The inverse of the Frobenius endomorphism as an algebra homomorphism. -/
noncomputable def frobeniusAlgHomInv : RealNovikovSeries A →ₐ[A] RealNovikovSeries A := 
  @Novikov.frobeniusAlgHom (1/Λ) hΛinv A _

/-- A finite projective `A`-module `M₀` gives rise to a Novikov isocrystal
    `M₀ ⊗_A A((t))` with the Frobenius map `id ⊗ F`. -/
noncomputable def ConstIsocrystal (M₀ : FiniteProjectiveModule A) :
    NovikovIsocrystal (Λ := Λ) A :=
  let R := RealNovikovSeries A
  let σ := frobeniusAlgHom (Λ := Λ) (A := A)
  let σinv := frobeniusAlgHomInv (Λ := Λ) (A := A)
  { M := R ⊗[A] M₀.M,
    F_M := {
      toFun := TensorProduct.map σ.toLinearMap LinearMap.id,
      invFun := TensorProduct.map σinv.toLinearMap LinearMap.id,
      left_inv := by
        intro x
        simp only [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id]
        have h_eq : σinv.toLinearMap.comp σ.toLinearMap = LinearMap.id := by
          refine LinearMap.ext fun r => ?_
          exact RingHomInvPair.comp_apply_eq (σ := frobeniusRingHom (Λ := Λ) (A := A))
        rw [h_eq]
        simp only [TensorProduct.map_id, LinearMap.id_apply]
      right_inv := by
        intro x
        simp only [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id]
        have h_eq : σ.toLinearMap.comp σinv.toLinearMap = LinearMap.id := by
          refine LinearMap.ext fun r => ?_
          exact RingHomInvPair.comp_apply_eq₂ (σ := frobeniusRingHom (Λ := Λ) (A := A))
        rw [h_eq]
        simp only [TensorProduct.map_id, LinearMap.id_apply]
      map_add' := map_add _
      map_smul' := by
        intro r x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul s m =>
          simp only [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply]
          rw [TensorProduct.smul_tmul', TensorProduct.map_tmul]
          simp only [LinearMap.id_apply, AlgHom.toLinearMap_apply]
          rw [smul_eq_mul, map_mul]
          rfl
        | add x y hx hy =>
          simp only [smul_add, map_add, hx, hy]
    }
  }

/-- The natural isomorphism between the base change of a Hom and the Hom of base changes. -/
noncomputable def ConstIsocrystalHomIsoModule (M₀ N₀ : FiniteProjectiveModule A) :
    (RealNovikovSeries A ⊗[A] (M₀.M →ₗ[A] N₀.M)) ≃ₗ[RealNovikovSeries A]
    ((ConstIsocrystal (Λ := Λ) M₀).M →ₗ[RealNovikovSeries A] (ConstIsocrystal (Λ := Λ) N₀).M) :=
  Novikov.Miscellany.homBaseChangeEquiv (R := A) (M := M₀.M) (N := N₀.M) (RealNovikovSeries A)

lemma ConstIsocrystalHomIsoModule_tmul (M₀ N₀ : FiniteProjectiveModule A) (r : RealNovikovSeries A) (f : M₀.M →ₗ[A] N₀.M) :
    (ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀) (r ⊗ₜ f) = r • f.baseChange (RealNovikovSeries A) :=
  rfl

private lemma ConstIsocrystalHomIso_commute (M₀ N₀ : FiniteProjectiveModule A)
    (x : RealNovikovSeries A ⊗[A] (M₀.M →ₗ[A] N₀.M)) :
    ((ConstIsocrystal (Λ := Λ) M₀).internalHom (ConstIsocrystal (Λ := Λ) N₀)).F_M
      (ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀ x) =
    ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀
      ((ConstIsocrystal (Λ := Λ) (M₀.homModule N₀)).F_M x) := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul r f₀ =>
    rw [ConstIsocrystalHomIsoModule_tmul]
    change ((ConstIsocrystal (Λ := Λ) M₀).internalHom (ConstIsocrystal (Λ := Λ) N₀)).F_M
        (r • LinearMap.baseChange (RealNovikovSeries A) f₀) =
      ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀
        ((frobeniusAlgHom (Λ := Λ) (A := A)) r ⊗ₜ f₀)
    rw [ConstIsocrystalHomIsoModule_tmul]
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rfl
    | tmul s m =>
      change (TensorProduct.map (frobeniusAlgHom (Λ := Λ) (A := A)).toLinearMap LinearMap.id)
          ((r • LinearMap.baseChange (RealNovikovSeries A) f₀)
            ((TensorProduct.map (frobeniusAlgHomInv (Λ := Λ) (A := A)).toLinearMap LinearMap.id)
              (s ⊗ₜ[A] m))) =
        (frobeniusAlgHom (Λ := Λ) (A := A) r) •
          (LinearMap.baseChange (RealNovikovSeries A) f₀ (s ⊗ₜ[A] m))
      rw [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
        LinearMap.smul_apply, LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul,
        TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
        LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]
      congr 1
      change frobeniusAlgHom (Λ := Λ) (A := A) (r * frobeniusAlgHomInv s) =
        frobeniusAlgHom (Λ := Λ) (A := A) r * s
      rw [map_mul]
      change frobeniusAlgHom (Λ := Λ) (A := A) r *
        frobeniusRingHom (Λ := Λ) (A := A) (frobeniusAlgHomInv (Λ := Λ) (A := A) s) =
        frobeniusAlgHom (Λ := Λ) (A := A) r * s
      rw [show frobeniusRingHom (Λ := Λ) (A := A) (frobeniusAlgHomInv (Λ := Λ) (A := A) s) = s
        from RingHomInvPair.comp_apply_eq₂ (σ := frobeniusRingHom (Λ := Λ) (A := A))]
    | add y₁ y₂ h₁ h₂ =>
      have hL := LinearMap.map_add
        (((ConstIsocrystal (Λ := Λ) M₀).internalHom (ConstIsocrystal (Λ := Λ) N₀)).F_M
          (r • LinearMap.baseChange (RealNovikovSeries A) f₀)) y₁ y₂
      have hR := LinearMap.map_add
        ((frobeniusAlgHom (Λ := Λ) (A := A) r) •
          LinearMap.baseChange (RealNovikovSeries A) f₀) y₁ y₂
      exact hL.trans (by rw [h₁, h₂]; exact hR.symm)
  | add x₁ x₂ h₁ h₂ =>
    have e1 :
        ((ConstIsocrystal (Λ := Λ) M₀).internalHom (ConstIsocrystal (Λ := Λ) N₀)).F_M
          (ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀ (x₁ + x₂)) =
        ((ConstIsocrystal (Λ := Λ) M₀).internalHom (ConstIsocrystal (Λ := Λ) N₀)).F_M
          (ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀ x₁) +
        ((ConstIsocrystal (Λ := Λ) M₀).internalHom (ConstIsocrystal (Λ := Λ) N₀)).F_M
          (ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀ x₂) := by
      rw [(ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀).map_add]
      exact (((ConstIsocrystal (Λ := Λ) M₀).internalHom (ConstIsocrystal (Λ := Λ) N₀)).F_M).map_add _ _
    have e2 :
        ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀
          ((ConstIsocrystal (Λ := Λ) (M₀.homModule N₀)).F_M (x₁ + x₂)) =
        ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀
          ((ConstIsocrystal (Λ := Λ) (M₀.homModule N₀)).F_M x₁) +
        ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀
          ((ConstIsocrystal (Λ := Λ) (M₀.homModule N₀)).F_M x₂) := by
      have h := ((ConstIsocrystal (Λ := Λ) (M₀.homModule N₀)).F_M).map_add x₁ x₂
      have h2 :
          ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀
              ((ConstIsocrystal (Λ := Λ) (M₀.homModule N₀)).F_M (x₁ + x₂)) =
            ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀
              ((ConstIsocrystal (Λ := Λ) (M₀.homModule N₀)).F_M x₁ +
                (ConstIsocrystal (Λ := Λ) (M₀.homModule N₀)).F_M x₂) :=
        congr_arg _ h
      rw [h2]
      exact (ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀).map_add _ _
    rw [e1, e2, h₁, h₂]
    rfl

/-- Internal Hom of induced isocrystals is the induced isocrystal of the internal Hom. -/
noncomputable def ConstIsocrystalHomIso (M₀ N₀ : FiniteProjectiveModule A) :
    ConstIsocrystal (Λ := Λ) (M₀.homModule N₀) ≅ internalHom (ConstIsocrystal (Λ := Λ) M₀) (ConstIsocrystal (Λ := Λ) N₀) :=
  let iso := ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀
  { hom := {
      toLinearMap := iso.toLinearMap
      commute_frobenius := ConstIsocrystalHomIso_commute M₀ N₀
    }
    inv := {
      toLinearMap := iso.symm.toLinearMap
      commute_frobenius := by
        intro x
        apply iso.injective
        change iso ((ConstIsocrystal (M₀.homModule N₀)).F_M (iso.symm x)) =
          iso (iso.symm (((ConstIsocrystal M₀).internalHom (ConstIsocrystal N₀)).F_M x))
        rw [iso.apply_symm_apply, ← ConstIsocrystalHomIso_commute M₀ N₀, iso.apply_symm_apply]
    }
    hom_inv_id := by apply hom_ext; ext; exact iso.left_inv _
    inv_hom_id := by apply hom_ext; ext; exact iso.right_inv _
  }

/-- The functor from the category of finite projective `A`-modules to the
    category of Novikov isocrystals. -/
noncomputable def vectToNovIsoc (A : Type*) [CommRing A] :
    (FiniteProjectiveModule A) ⥤ NovikovIsocrystal (Λ := Λ) A where
  obj M₀ := ConstIsocrystal M₀
  map {M₀ N₀} f := {
    toLinearMap := f.baseChange (RealNovikovSeries A)
    commute_frobenius := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => exact map_zero _
      | tmul r m =>
        erw [LinearMap.baseChange_tmul (R := A) (A := RealNovikovSeries A) f r m]
        dsimp [ConstIsocrystal]
        erw [TensorProduct.map_tmul]
      | add x y hx hy =>
        erw [map_add, map_add, map_add, map_add, hx, hy]
  }
  map_id M₀ := by
    apply hom_ext
    exact LinearMap.baseChange_id
  map_comp {M₀ N₀ P₀} f g := by
    apply hom_ext
    exact LinearMap.baseChange_comp f g

/-- The constant term of a Novikov series. -/
noncomputable def constantTerm (A : Type*) [CommRing A] : RealNovikovSeries A →ₗ[A] A where
  toFun f := f 0
  map_add' _ _ := rfl
  map_smul' a f := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    have h := novikovSeriesMul_left_monomial a f AddMonoidHom.mul 0 0
    simp only [zero_add, AddMonoidHom.coe_mul, AddMonoidHom.coe_mulLeft] at h
    exact h

lemma constantTerm_algebraMap (a : A) : constantTerm A (algebraMap A (RealNovikovSeries A) a) = a := by
  dsimp [constantTerm, algebraMap, Algebra.algebraMap, algebraMapNovikov]
  simp

section FrobeniusFixedPointsTensor

/-- If `x ∈ R ⊗[A] (Fin n → A)` is a Frobenius fixed point, then `x = 1 ⊗ a` for some `a : Fin n → A`. -/
private lemma frobenius_fixed_points_tensor_fin (n : ℕ) (x : RealNovikovSeries A ⊗[A] (Fin n → A))
    (hx : TensorProduct.map (frobeniusAlgHom (Λ := Λ) (A := A)).toLinearMap LinearMap.id x = x) :
    ∃ a : Fin n → A, x = TensorProduct.tmul A (1 : RealNovikovSeries A) a := by
  let σ := frobeniusAlgHom (Λ := Λ) (A := A)
  -- Projection maps π_j : R ⊗[A] (Fin n → A) →ₗ[A] R
  let π (j : Fin n) : RealNovikovSeries A ⊗[A] (Fin n → A) →ₗ[A] RealNovikovSeries A :=
    TensorProduct.lift
      { toFun := fun (r : RealNovikovSeries A) =>
        { toFun := fun (f : Fin n → A) => r * (algebraMap A (RealNovikovSeries A)) (f j)
          map_add' := fun f g => by simp [mul_add]
          map_smul' := fun a f => by
            simp [Algebra.smul_def, smul_eq_mul, mul_left_comm] }
        map_add' := fun r s => by
          ext f; simp [add_mul]
        map_smul' := fun a r => by
          ext f
          simp [Algebra.smul_def, mul_comm, mul_left_comm] }
  have hπ_tmul (j : Fin n) (r : RealNovikovSeries A) (f : Fin n → A) :
      π j (r ⊗ₜ[A] f) = r * (algebraMap A (RealNovikovSeries A)) (f j) := rfl
  -- π_j commutes with Frobenius
  have hπ_commute (j : Fin n) (y : RealNovikovSeries A ⊗[A] (Fin n → A)) :
      π j (TensorProduct.map σ.toLinearMap LinearMap.id y) = σ (π j y) := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r f =>
      rw [TensorProduct.map_tmul, hπ_tmul, hπ_tmul]
      dsimp
      simp
    | add y z hy hz => simp [map_add, hy, hz]
  -- Each coefficient is a Frobenius fixed point
  have h_const (j : Fin n) : ∃ a : A,
      π j x = algebraMap A (RealNovikovSeries A) a := by
    have h_fixed : σ (π j x) = π j x := by
      rw [← hπ_commute j x, hx]
    have h_fixed' : frobenius Λ (π j x) = π j x := by
      simpa [frobeniusAlgHom, frobeniusRingHom] using h_fixed
    rcases ((Novikov.frobenius_fixed_points (π j x)).mp h_fixed') with ⟨a, ha⟩
    exact ⟨a, by simpa [algebraMap, Algebra.algebraMap, algebraMapNovikov] using ha⟩
  choose a ha using h_const
  -- Inverse map: expansion in standard basis
  let ι : (Fin n → RealNovikovSeries A) →ₗ[A]
      RealNovikovSeries A ⊗[A] (Fin n → A) :=
    { toFun := fun v => (∑ j : Fin n, TensorProduct.tmul A (v j) (Pi.single j (1 : A) : Fin n → A))
      map_add' := fun x y => by
        dsimp; simp only [TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        dsimp; simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, Finset.smul_sum] }
  have h_pi_iota (j : Fin n) (v : Fin n → RealNovikovSeries A) : π j (ι v) = v j := by
    calc
      π j (ι v) = π j (∑ k : Fin n, TensorProduct.tmul A (v k)
            (Pi.single k (1 : A) : Fin n → A)) := rfl
      _ = ∑ k : Fin n, π j (TensorProduct.tmul A (v k)
            (Pi.single k (1 : A) : Fin n → A)) := by rw [map_sum]
      _ = ∑ k : Fin n, (v k * (algebraMap A (RealNovikovSeries A))
            ((Pi.single k (1 : A) : Fin n → A) j)) := by
        simp [hπ_tmul]
      _ = v j := by
        simp [Pi.single_apply, algebraMap, Algebra.algebraMap, algebraMapNovikov]
  have h_iota_pi (y : RealNovikovSeries A ⊗[A] (Fin n → A)) : ι (fun j => π j y) = y := by
    induction y using TensorProduct.induction_on with
    | zero => simp [ι]
    | tmul r f =>
      have h_expand : f = ∑ j : Fin n, (f j) • (Pi.single j (1 : A) : Fin n → A) := by
        ext i; simp [Finset.sum_apply, Pi.single_apply]
      calc
        ι (fun j => π j (TensorProduct.tmul A r f))
            = ∑ j : Fin n, TensorProduct.tmul A
                (r * (algebraMap A (RealNovikovSeries A)) (f j))
                (Pi.single j (1 : A) : Fin n → A) := by
              simp [ι, hπ_tmul]
        _ = ∑ j : Fin n, TensorProduct.tmul A ((f j : A) • r)
                (Pi.single j (1 : A) : Fin n → A) := by
          simp [Algebra.smul_def, mul_comm]
        _ = ∑ j : Fin n, TensorProduct.tmul A r ((f j : A) • (Pi.single j (1 : A) : Fin n → A)) := by
          simp_rw [TensorProduct.smul_tmul]
        _ = TensorProduct.tmul A r f := by
          rw [← TensorProduct.tmul_sum, ← h_expand]
    | add y z hy hz =>
      have h_eq : (fun j : Fin n => π j (y + z)) = (fun j => (π j y) + (π j z)) := by
        ext j; simp
      calc
        ι (fun j => π j (y + z)) = ι (fun j => (π j y) + (π j z)) := by rw [h_eq]
        _ = ι ((fun j => π j y) + (fun j => π j z)) := rfl
        _ = ι (fun j => π j y) + ι (fun j => π j z) := ι.map_add _ _
        _ = y + z := by rw [hy, hz]
  have h_one_tensor (a : Fin n → A) : ι (fun j => algebraMap A (RealNovikovSeries A) (a j)) =
      TensorProduct.tmul A (1 : RealNovikovSeries A) a := by
    calc
      ι (fun j => algebraMap A (RealNovikovSeries A) (a j))
          = ∑ j : Fin n, TensorProduct.tmul A (algebraMap A (RealNovikovSeries A) (a j))
            (Pi.single j (1 : A) : Fin n → A) := rfl
      _ = ∑ j : Fin n, TensorProduct.tmul A ((a j : A) • (1 : RealNovikovSeries A))
            (Pi.single j (1 : A) : Fin n → A) := by
        simp [Algebra.algebraMap_eq_smul_one]
      _ = ∑ j : Fin n, TensorProduct.tmul A (1 : RealNovikovSeries A) ((a j : A) •
              (Pi.single j (1 : A) : Fin n → A)) := by
        simp_rw [TensorProduct.smul_tmul]
      _ = TensorProduct.tmul A (1 : RealNovikovSeries A) (∑ j : Fin n, (a j : A) •
              (Pi.single j (1 : A) : Fin n → A)) := by
        rw [← TensorProduct.tmul_sum]
      _ = TensorProduct.tmul A (1 : RealNovikovSeries A) a := by
        congr 1
        ext i
        simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨a, ?_⟩
  calc
    x = ι (fun j => π j x) := by rw [h_iota_pi]
    _ = ι (fun j => algebraMap A (RealNovikovSeries A) (a j)) := by
      refine congrArg ι (funext fun j => ha j)
    _ = TensorProduct.tmul A (1 : RealNovikovSeries A) a := by rw [h_one_tensor a]

/-- Frobenius fixed points of `R ⊗[A] P` (with `P` finite projective)
    are exactly `1 ⊗ p` for some `p : P`. -/
lemma frobenius_fixed_points_tensor (P : Type*) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P]
    (x : RealNovikovSeries A ⊗[A] P)
    (hx : TensorProduct.map (frobeniusAlgHom (Λ := Λ) (A := A)).toLinearMap LinearMap.id x = x) :
    ∃ p : P, x = TensorProduct.tmul A (1 : RealNovikovSeries A) p := by
  let σ := frobeniusAlgHom (Λ := Λ) (A := A)
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  -- f : (Fin n → A) →ₗ[A] P, g : P →ₗ[A] (Fin n → A), hfg : f.comp g = .id
  have h_recover (x' : RealNovikovSeries A ⊗[A] P) :
      TensorProduct.map LinearMap.id f (TensorProduct.map LinearMap.id g x') = x' := by
    calc
      (TensorProduct.map LinearMap.id f) ((TensorProduct.map LinearMap.id g) x')
          = ((TensorProduct.map LinearMap.id f) ∘ₗ (TensorProduct.map LinearMap.id g)) x' := rfl
      _ = TensorProduct.map (LinearMap.id ∘ₗ LinearMap.id) (f ∘ₗ g) x' := by rw [TensorProduct.map_comp]
      _ = TensorProduct.map LinearMap.id LinearMap.id x' := by simp [hfg]
      _ = x' := by simp
  set y := TensorProduct.map LinearMap.id g x with hy_def
  have h_comm : TensorProduct.map σ.toLinearMap LinearMap.id ∘ₗ TensorProduct.map LinearMap.id g =
      TensorProduct.map LinearMap.id g ∘ₗ TensorProduct.map σ.toLinearMap LinearMap.id := by
    calc
      TensorProduct.map σ.toLinearMap LinearMap.id ∘ₗ TensorProduct.map LinearMap.id g
          = TensorProduct.map (σ.toLinearMap ∘ₗ LinearMap.id) (LinearMap.id ∘ₗ g) := by
        rw [TensorProduct.map_comp]
      _ = TensorProduct.map σ.toLinearMap g := by simp
      _ = TensorProduct.map (LinearMap.id ∘ₗ σ.toLinearMap) (g ∘ₗ LinearMap.id) := by simp
      _ = TensorProduct.map LinearMap.id g ∘ₗ TensorProduct.map σ.toLinearMap LinearMap.id := by
        rw [← TensorProduct.map_comp]
  have hy_fixed : TensorProduct.map σ.toLinearMap LinearMap.id y = y := by
    dsimp [y]
    calc
      TensorProduct.map σ.toLinearMap LinearMap.id (TensorProduct.map LinearMap.id g x)
          = (TensorProduct.map σ.toLinearMap LinearMap.id ∘ₗ TensorProduct.map LinearMap.id g) x := rfl
      _ = (TensorProduct.map LinearMap.id g ∘ₗ TensorProduct.map σ.toLinearMap LinearMap.id) x := by
        rw [h_comm]
      _ = TensorProduct.map LinearMap.id g (TensorProduct.map σ.toLinearMap LinearMap.id x) := rfl
      _ = TensorProduct.map LinearMap.id g x := by rw [hx]
      _ = y := hy_def.symm
  rcases frobenius_fixed_points_tensor_fin n y hy_fixed with ⟨a, ha⟩
  refine ⟨f a, ?_⟩
  calc
    x = TensorProduct.map LinearMap.id f (TensorProduct.map LinearMap.id g x) := by rw [h_recover x]
    _ = TensorProduct.map LinearMap.id f y := by rw [hy_def]
    _ = TensorProduct.map LinearMap.id f
          (TensorProduct.tmul A (1 : RealNovikovSeries A) a) := by rw [ha]
    _ = TensorProduct.tmul A (1 : RealNovikovSeries A) (f a) := by simp

end FrobeniusFixedPointsTensor

/-- The functor `vectToNovIsoc` is fully faithful. -/
noncomputable def vectToNovIsoc_fullyFaithful :
    (vectToNovIsoc (Λ := Λ) (A := A)).FullyFaithful := by
  have hFull : (vectToNovIsoc (Λ := Λ) (A := A)).Full := by
    refine { map_surjective := ?_ }
    intro M₀ N₀ g
    let R := RealNovikovSeries A
    let σ := frobeniusAlgHom (Λ := Λ) (A := A)
    let iso := ConstIsocrystalHomIsoModule (Λ := Λ) M₀ N₀
    set f : R ⊗[A] (M₀.M →ₗ[A] N₀.M) := iso.symm g.toLinearMap with hf_def
    have h_g_fixed : ((ConstIsocrystal (Λ := Λ) M₀).internalHom (ConstIsocrystal (Λ := Λ) N₀)).F_M g.toLinearMap =
        g.toLinearMap :=
      ((frobenius_fixed_points (ConstIsocrystal (Λ := Λ) M₀) (ConstIsocrystal (Λ := Λ) N₀) g.toLinearMap).mp
        g.commute_frobenius)
    have h_fixed : TensorProduct.map σ.toLinearMap LinearMap.id f = f := by
      have h_ofMod_fixed : (ConstIsocrystal (Λ := Λ) (M₀.homModule N₀)).F_M f = f := by
        apply iso.injective
        have h_eq : iso ((ConstIsocrystal (Λ := Λ) (M₀.homModule N₀)).F_M f) = iso f := by
          rw [← ConstIsocrystalHomIso_commute M₀ N₀ f]
          dsimp [f]
          rw [iso.apply_symm_apply]
          exact h_g_fixed
        exact h_eq
      dsimp [ConstIsocrystal] at h_ofMod_fixed
      exact h_ofMod_fixed
    rcases frobenius_fixed_points_tensor (M₀.M →ₗ[A] N₀.M) f h_fixed with ⟨f₀, hf₀⟩
    refine ⟨f₀, ?_⟩
    have h_eq : ((vectToNovIsoc (Λ := Λ) (A := A)).map f₀).toLinearMap = g.toLinearMap := by
      dsimp [vectToNovIsoc]
      rw [← one_smul (RealNovikovSeries A) (f₀.baseChange (RealNovikovSeries A)),
        ← ConstIsocrystalHomIsoModule_tmul M₀ N₀ (1 : RealNovikovSeries A) f₀, ← hf₀, hf_def,
        iso.apply_symm_apply]
    apply hom_ext
    exact h_eq
  have hFaithful : (vectToNovIsoc (Λ := Λ) (A := A)).Faithful := by
    constructor
    intro M₀ N₀ f g h_eq
    refine LinearMap.ext (fun m => ?_)
    let r := constantTerm A
    let ret := TensorProduct.map r (LinearMap.id (M := N₀.M))
    have h_val : (f.baseChange (RealNovikovSeries A)) (1 ⊗ₜ m) = (g.baseChange (RealNovikovSeries A)) (1 ⊗ₜ m) := by
      have := congr_arg NovikovIsocrystal.Hom.toLinearMap h_eq
      dsimp [vectToNovIsoc] at this
      exact DFunLike.congr_fun this (1 ⊗ₜ m)
    let lid := TensorProduct.lid A N₀.M
    have h_eval := congr_arg (lid.toLinearMap ∘ₗ ret) h_val
    dsimp [ret, r, LinearMap.coe_comp, Function.comp_apply] at h_eval
    have h3 : constantTerm A (1 : RealNovikovSeries A) = 1 := by
      change constantTerm A (algebraMap A (RealNovikovSeries A) 1) = 1
      rw [constantTerm_algebraMap]
    simp only [h3] at h_eval
    erw [TensorProduct.lid_tmul, TensorProduct.lid_tmul] at h_eval
    simp only [one_smul] at h_eval
    exact h_eval
  letI := hFull
  letI := hFaithful
  exact Functor.FullyFaithful.ofFullyFaithful (vectToNovIsoc (Λ := Λ) (A := A))

end NovikovIsocrystal

end Isocrystal

end Novikov
