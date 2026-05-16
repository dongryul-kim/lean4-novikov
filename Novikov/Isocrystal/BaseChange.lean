import Novikov.Isocrystal.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps

open CategoryTheory
open TensorProduct

namespace Novikov
variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]

section BaseChange

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)

noncomputable instance : Algebra A (RealNovikovSeries B) :=
  Algebra.compHom (RealNovikovSeries B) f

@[reducible]
noncomputable def realNovikovSeriesAlgebra : Algebra (RealNovikovSeries A) (RealNovikovSeries B) :=
  (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) f).toAlgebra

lemma frobeniusRingHom_comp_baseChange :
    (frobeniusRingHom (Λ := Λ) (A := B)).comp
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) f) =
    (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) f).comp
      (frobeniusRingHom (Λ := Λ) (A := A)) := by
  apply RingHom.ext; intro s; ext d
  dsimp [frobeniusRingHom]
  simp [mapRingHom_apply, frobenius_apply_val]

/-- The image of `mapRingHom` on real Novikov series is closed when `B` has
discrete topology. -/
lemma realNovikovSeriesRingHom_closed_range [TopologicalSpace B] [DiscreteTopology B] :
    IsClosed (Set.range (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) f) :
      Set (RealNovikovSeries B)) :=
  map_range_closed (Γ := (⊤ : AddSubgroup ℝ)) f.toAddMonoidHom

end BaseChange

section BaseChangeFunctor

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)

lemma projective_base_change {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Type*) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] :
    Module.Projective S (TensorProduct R S P) := by
  obtain ⟨n, i, g, _, _, hig⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  let iS : TensorProduct R S ((Fin n) → R) →ₗ[S] TensorProduct R S P := i.baseChange S
  let gS : TensorProduct R S P →ₗ[S] TensorProduct R S ((Fin n) → R) := g.baseChange S
  have higS : iS ∘ₗ gS = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hig, LinearMap.baseChange_id]
  have h_free : Module.Projective S (TensorProduct R S ((Fin n) → R)) := by
    have h_iso : TensorProduct R S ((Fin n) → R) ≃ₗ[S] (Fin n) → S :=
      TensorProduct.piScalarRight (N := S) (R := R) (S := S) (ι := Fin n)
    exact Module.Projective.of_equiv h_iso.symm
  exact Module.Projective.of_split gS iS higS

-- Synthesizing Module.Projective is expensive
noncomputable def baseChange (M : NovikovIsocrystal (Λ := Λ) A) : NovikovIsocrystal (Λ := Λ) B :=
  letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) := realNovikovSeriesAlgebra f
  letI : Module (RealNovikovSeries A) (RealNovikovSeries B) := Algebra.toModule
  let φ_A := frobeniusRingHom (Λ := Λ) (A := A)
  let φ_B := frobeniusRingHom (Λ := Λ) (A := B)
  let φ_A_inv := frobeniusRingHomInv (Λ := Λ) (A := A)
  let φ_B_inv := frobeniusRingHomInv (Λ := Λ) (A := B)
  let rnghom := mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) f
  haveI : Module.Finite (RealNovikovSeries B) ((RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M) :=
    Module.Finite.base_change (RealNovikovSeries A) (RealNovikovSeries B) M.M
  haveI : Module.Projective (RealNovikovSeries B) ((RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M) :=
    projective_base_change (R := RealNovikovSeries A) (S := RealNovikovSeries B) M.M
  let φ_B_sl : (RealNovikovSeries B) →ₛₗ[φ_A] (RealNovikovSeries B) :=
    { toFun := φ_B
      map_add' := φ_B.map_add
      map_smul' := by
        intro r b
        have h_comm := frobeniusRingHom_comp_baseChange (Λ := Λ) f
        dsimp [φ_A, φ_B]
        have h : (frobeniusRingHom (Λ := Λ) (A := B)) (r • b) =
            ((frobeniusRingHom (Λ := Λ) (A := A)) r) •
            (frobeniusRingHom (Λ := Λ) (A := B)) b := by
          calc
            (frobeniusRingHom (Λ := Λ) (A := B)) (r • b) =
                (frobeniusRingHom (Λ := Λ) (A := B)) ((rnghom r) * b) := rfl
            _ = (frobeniusRingHom (Λ := Λ) (A := B)) (rnghom r) *
                (frobeniusRingHom (Λ := Λ) (A := B)) b :=
              by rw [(frobeniusRingHom (Λ := Λ) (A := B)).map_mul]
            _ = rnghom ((frobeniusRingHom (Λ := Λ) (A := A)) r) *
                (frobeniusRingHom (Λ := Λ) (A := B)) b := by
                have h := RingHom.congr_fun h_comm r
                simpa [RingHom.comp_apply] using
                  congrArg (· * (frobeniusRingHom (Λ := Λ) (A := B)) b) h
            _ = ((frobeniusRingHom (Λ := Λ) (A := A)) r) •
                (frobeniusRingHom (Λ := Λ) (A := B)) b := rfl
        exact h
    }
  have h_comm_inv : (frobeniusRingHomInv (Λ := Λ) (A := B)).comp rnghom =
      rnghom.comp φ_A_inv := by
    apply RingHom.ext; intro s; ext d
    dsimp [φ_A_inv, frobeniusRingHomInv, frobeniusRingHom, rnghom]
    simp [mapRingHom_apply, frobenius_apply_val]
  let φ_B_inv_sl : (RealNovikovSeries B) →ₛₗ[φ_A_inv] (RealNovikovSeries B) :=
    { toFun := frobeniusRingHomInv (Λ := Λ) (A := B)
      map_add' := (frobeniusRingHomInv (Λ := Λ) (A := B)).map_add
      map_smul' := by
        intro r b
        dsimp [φ_A_inv, φ_B_inv]
        have h : (frobeniusRingHomInv (Λ := Λ) (A := B)) (r • b) =
            ((frobeniusRingHomInv (Λ := Λ) (A := A)) r) •
            (frobeniusRingHomInv (Λ := Λ) (A := B)) b := by
          calc
            (frobeniusRingHomInv (Λ := Λ) (A := B)) (r • b) =
                (frobeniusRingHomInv (Λ := Λ) (A := B)) ((rnghom r) * b) := rfl
            _ = (frobeniusRingHomInv (Λ := Λ) (A := B)) (rnghom r) *
                (frobeniusRingHomInv (Λ := Λ) (A := B)) b :=
              by rw [(frobeniusRingHomInv (Λ := Λ) (A := B)).map_mul]
            _ = rnghom ((frobeniusRingHomInv (Λ := Λ) (A := A)) r) *
                (frobeniusRingHomInv (Λ := Λ) (A := B)) b := by
                have h := RingHom.congr_fun h_comm_inv r
                simpa [RingHom.comp_apply] using
                  congrArg (· * (frobeniusRingHomInv (Λ := Λ) (A := B)) b) h
            _ = ((frobeniusRingHomInv (Λ := Λ) (A := A)) r) •
                (frobeniusRingHomInv (Λ := Λ) (A := B)) b := rfl
        exact h
    }
  let F_fwd : (RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M →ₛₗ[φ_A] (RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M :=
    TensorProduct.map φ_B_sl (M.F_M : M.M →ₛₗ[φ_A] M.M)
  let F_bwd : (RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M →ₛₗ[φ_A_inv] (RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M :=
    TensorProduct.map φ_B_inv_sl (M.F_M.symm : M.M →ₛₗ[φ_A_inv] M.M)
  have h_F_tmul (b m) : F_fwd (b ⊗ₜ[RealNovikovSeries A] m) = φ_B b ⊗ₜ[RealNovikovSeries A] M.F_M m :=
    TensorProduct.map_tmul φ_B_sl (M.F_M : M.M →ₛₗ[φ_A] M.M) b m
  have h_G_tmul (b m) : F_bwd (b ⊗ₜ[RealNovikovSeries A] m) =
      φ_B_inv b ⊗ₜ[RealNovikovSeries A] M.F_M.symm m :=
    TensorProduct.map_tmul φ_B_inv_sl (M.F_M.symm : M.M →ₛₗ[φ_A_inv] M.M) b m
  have h_FG (x : (RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M) : F_bwd (F_fwd x) = x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      simp [h_F_tmul, h_G_tmul, M.F_M.symm_apply_apply]
    | add x y hx hy => simp [hx, hy]
  have h_GF (x : (RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M) : F_fwd (F_bwd x) = x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      simp [h_F_tmul, h_G_tmul, M.F_M.apply_symm_apply]
    | add x y hx hy => simp [hx, hy]
  have h_F_semilinear (s : RealNovikovSeries B) (x : (RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M) :
      F_fwd (s • x) = φ_B s • F_fwd x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      simp [h_F_tmul, TensorProduct.smul_tmul', smul_eq_mul, RingHom.map_mul]
    | add x y hx hy =>
      simp [smul_add, map_add, hx, hy]
  { M := (RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M
    F_M :=
      { toFun := F_fwd
        invFun := F_bwd
        left_inv := h_FG
        right_inv := h_GF
        map_add' := map_add _
        map_smul' := h_F_semilinear
      }
  }

lemma baseChange_F_tmul (M : NovikovIsocrystal (Λ := Λ) A) (b : RealNovikovSeries B) (m : M.M) :
    letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) := realNovikovSeriesAlgebra f
    letI : Module (RealNovikovSeries A) (RealNovikovSeries B) := Algebra.toModule
    (baseChange f M).F_M (b ⊗ₜ[RealNovikovSeries A] m) =
    (frobeniusRingHom (Λ := Λ) (A := B)) b ⊗ₜ[RealNovikovSeries A] M.F_M m := by
  rfl

noncomputable def baseChangeMap {M N : NovikovIsocrystal (Λ := Λ) A} (φ : M ⟶ N) :
    baseChange f M ⟶ baseChange f N :=
  letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) := realNovikovSeriesAlgebra f
  letI : Module (RealNovikovSeries A) (RealNovikovSeries B) := Algebra.toModule
  { toLinearMap :=
      AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B)
        φ.toLinearMap
    commute_frobenius := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero =>
        have h1 : (baseChange f N).F_M ((AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) 0) = (baseChange f N).F_M 0 := congrArg (baseChange f N).F_M (map_zero (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap))
        have h2 : (baseChange f N).F_M 0 = 0 := map_zero (baseChange f N).F_M
        have h3 : (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) ((baseChange f M).F_M 0) = (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) 0 := congrArg (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) (map_zero (baseChange f M).F_M)
        have h4 : (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) 0 = 0 := map_zero (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap)
        exact h1.trans (h2.trans (h4.symm.trans h3.symm))
      | tmul b m =>
        change (baseChange f N).F_M (b ⊗ₜ[RealNovikovSeries A] (φ.toLinearMap m)) =
          (frobeniusRingHom (Λ := Λ) (A := B)) b ⊗ₜ[RealNovikovSeries A] (φ.toLinearMap (M.F_M m))
        rw [baseChange_F_tmul, φ.commute_frobenius]
      | add x y hx hy =>
        have h1 : (baseChange f N).F_M ((AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) (x + y)) = (baseChange f N).F_M ((AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) x + (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) y) := congrArg (baseChange f N).F_M (map_add (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) x y)
        have h2 : (baseChange f N).F_M ((AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) x + (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) y) = (baseChange f N).F_M ((AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) x) + (baseChange f N).F_M ((AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) y) := map_add (baseChange f N).F_M _ _
        have h3 : (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) ((baseChange f M).F_M (x + y)) = (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) ((baseChange f M).F_M x + (baseChange f M).F_M y) := congrArg (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) (map_add (baseChange f M).F_M x y)
        have h4 : (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) ((baseChange f M).F_M x + (baseChange f M).F_M y) = (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) ((baseChange f M).F_M x) + (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) ((baseChange f M).F_M y) := map_add (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) _ _
        have h_mid : (baseChange f N).F_M ((AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) x) + (baseChange f N).F_M ((AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) y) = (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) ((baseChange f M).F_M x) + (AlgebraTensorModule.map (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B) φ.toLinearMap) ((baseChange f M).F_M y) := by erw [hx, hy]; rfl
        exact h1.trans (h2.trans (h_mid.trans (h4.symm.trans h3.symm)))
  }

lemma baseChange_toLinearMap_tmul (M N : NovikovIsocrystal (Λ := Λ) A) (φ : M ⟶ N)
    (b : RealNovikovSeries B) (m : M.M) :
    letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) := realNovikovSeriesAlgebra f
    letI : Module (RealNovikovSeries A) (RealNovikovSeries B) := Algebra.toModule
    (baseChangeMap f φ).toLinearMap (b ⊗ₜ[RealNovikovSeries A] m) =
    b ⊗ₜ[RealNovikovSeries A] (φ.toLinearMap m) := by
  rfl

noncomputable def baseChangeFunctor : NovikovIsocrystal (Λ := Λ) A ⥤ NovikovIsocrystal (Λ := Λ) B where
  obj := baseChange f
  map := baseChangeMap f
  map_id M := by
    apply NovikovIsocrystal.hom_ext
    ext x
    letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) := realNovikovSeriesAlgebra f
    letI : Module (RealNovikovSeries A) (RealNovikovSeries B) := Algebra.toModule
    induction x using TensorProduct.induction_on with
    | zero =>
      have h1 : (baseChangeMap f (𝟙 M)).toLinearMap 0 = 0 := map_zero _
      have h2 : (NovikovIsocrystal.Hom.toLinearMap (𝟙 (baseChange f M))) 0 = 0 := map_zero _
      exact h1.trans h2.symm
    | tmul b m => rfl
    | add x y hx hy =>
      have h1 : (baseChangeMap f (𝟙 M)).toLinearMap (x + y) = (baseChangeMap f (𝟙 M)).toLinearMap x + (baseChangeMap f (𝟙 M)).toLinearMap y := map_add _ x y
      have h2 : (NovikovIsocrystal.Hom.toLinearMap (𝟙 (baseChange f M))) (x + y) = (NovikovIsocrystal.Hom.toLinearMap (𝟙 (baseChange f M))) x + (NovikovIsocrystal.Hom.toLinearMap (𝟙 (baseChange f M))) y := map_add _ x y
      have h_mid : (baseChangeMap f (𝟙 M)).toLinearMap x + (baseChangeMap f (𝟙 M)).toLinearMap y = (NovikovIsocrystal.Hom.toLinearMap (𝟙 (baseChange f M))) x + (NovikovIsocrystal.Hom.toLinearMap (𝟙 (baseChange f M))) y := by rw [hx, hy]
      exact h1.trans (h_mid.trans h2.symm)
  map_comp {M N P} φ ψ := by
    apply NovikovIsocrystal.hom_ext
    ext x
    letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) := realNovikovSeriesAlgebra f
    letI : Module (RealNovikovSeries A) (RealNovikovSeries B) := Algebra.toModule
    induction x using TensorProduct.induction_on with
    | zero =>
      have h1 : (baseChangeMap f (φ ≫ ψ)).toLinearMap 0 = 0 := map_zero _
      have h2 : (NovikovIsocrystal.Hom.toLinearMap (baseChangeMap f φ ≫ baseChangeMap f ψ)) 0 = 0 := map_zero _
      exact h1.trans h2.symm
    | tmul b m =>
      change (baseChangeMap f (φ ≫ ψ)).toLinearMap (b ⊗ₜ[RealNovikovSeries A] m) =
        (baseChangeMap f ψ).toLinearMap ((baseChangeMap f φ).toLinearMap (b ⊗ₜ[RealNovikovSeries A] m))
      rw [baseChange_toLinearMap_tmul, baseChange_toLinearMap_tmul, baseChange_toLinearMap_tmul]
      rfl
    | add x y hx hy =>
      have h1 : (baseChangeMap f (φ ≫ ψ)).toLinearMap (x + y) = (baseChangeMap f (φ ≫ ψ)).toLinearMap x + (baseChangeMap f (φ ≫ ψ)).toLinearMap y := map_add _ x y
      have h2 : (NovikovIsocrystal.Hom.toLinearMap (baseChangeMap f φ ≫ baseChangeMap f ψ)) (x + y) = (NovikovIsocrystal.Hom.toLinearMap (baseChangeMap f φ ≫ baseChangeMap f ψ)) x + (NovikovIsocrystal.Hom.toLinearMap (baseChangeMap f φ ≫ baseChangeMap f ψ)) y := map_add _ x y
      have h_mid : (baseChangeMap f (φ ≫ ψ)).toLinearMap x + (baseChangeMap f (φ ≫ ψ)).toLinearMap y = (NovikovIsocrystal.Hom.toLinearMap (baseChangeMap f φ ≫ baseChangeMap f ψ)) x + (NovikovIsocrystal.Hom.toLinearMap (baseChangeMap f φ ≫ baseChangeMap f ψ)) y := by rw [hx, hy]
      exact h1.trans (h_mid.trans h2.symm)

end BaseChangeFunctor

end Novikov
