import Novikov.Isocrystal.Basic
import Novikov.Miscellany.Semilinear
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
  simp [mapRingHom_apply]

/-- The image of `mapRingHom` on real Novikov series is closed when `B` has
discrete topology. -/
lemma realNovikovSeriesRingHom_closed_range [TopologicalSpace B] [DiscreteTopology B] :
    IsClosed (Set.range (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) f) :
      Set (RealNovikovSeries B)) :=
  map_range_closed (Γ := (⊤ : AddSubgroup ℝ)) f.toAddMonoidHom

end BaseChange

section BaseChangeFunctor

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)

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
    Novikov.Miscellany.baseChange_projective M.M
  have h_comm : φ_B.comp rnghom = rnghom.comp φ_A := frobeniusRingHom_comp_baseChange (Λ := Λ) f
  have h_comm_inv : φ_B_inv.comp rnghom = rnghom.comp φ_A_inv := by
    apply RingHom.ext; intro s; ext d
    dsimp [φ_A_inv, φ_B_inv, frobeniusRingHomInv, frobeniusRingHom, rnghom]
    simp [mapRingHom_apply]
  { M := (RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M
    F_M := Novikov.Miscellany.baseChangeSemilinearMap rnghom φ_A φ_A_inv φ_B φ_B_inv
      h_comm h_comm_inv M.M M.M M.F_M }

lemma baseChange_F_tmul (M : NovikovIsocrystal (Λ := Λ) A) (b : RealNovikovSeries B) (m : M.M) :
    letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) := realNovikovSeriesAlgebra f
    letI : Module (RealNovikovSeries A) (RealNovikovSeries B) := Algebra.toModule
    (baseChange f M).F_M (b ⊗ₜ[RealNovikovSeries A] m) =
    (frobeniusRingHom (Λ := Λ) (A := B)) b ⊗ₜ[RealNovikovSeries A] M.F_M m := by
  unfold baseChange
  rw [Novikov.Miscellany.baseChangeSemilinearMap_tmul]

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
        calc
          (baseChange f N).F_M
              ((AlgebraTensorModule.map
                (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B)
                φ.toLinearMap) (b ⊗ₜ[RealNovikovSeries A] m))
              = (baseChange f N).F_M (b ⊗ₜ[RealNovikovSeries A] φ.toLinearMap m) := by
                rfl
          _ = (frobeniusRingHom (Λ := Λ) (A := B)) b ⊗ₜ[RealNovikovSeries A]
                N.F_M (φ.toLinearMap m) := by
                rw [baseChange_F_tmul]
          _ = (frobeniusRingHom (Λ := Λ) (A := B)) b ⊗ₜ[RealNovikovSeries A]
                φ.toLinearMap (M.F_M m) := by
                rw [φ.commute_frobenius]
          _ = (AlgebraTensorModule.map
                (LinearMap.id : RealNovikovSeries B →ₗ[RealNovikovSeries B] RealNovikovSeries B)
                φ.toLinearMap) ((baseChange f M).F_M (b ⊗ₜ[RealNovikovSeries A] m)) := by
                rw [baseChange_F_tmul]
                rfl
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
