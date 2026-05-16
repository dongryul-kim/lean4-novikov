import Novikov.Isocrystal.Basic
import Novikov.Isocrystal.Constant
import Novikov.Isocrystal.BaseChange
import Novikov.Isocrystal.Injective.Submodule
import Novikov.Series.Module
import Novikov.Series.Projective
import Novikov.Miscellany.Topology
import Novikov.Miscellany.Projective
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# Injectivity of Novikov Isocrystals (Proposition 3.7)

Formalizes paper.tex:744-781. A Novikov isocrystal `M` over `A` whose base
change to `B` is constant is itself constant, given `A ↪ B` injective.
The Frobenius-limit submodule input (Lemma 3.6) is in `Injective/Submodule.lean`.
-/

open CategoryTheory
open TensorProduct
open Novikov.Miscellany

namespace Novikov
variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]

section NovIsocInjective

universe u

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- For a finite projective `R`-module `N₀`, the underlying module of `ConstIsocrystal N₀`
is `R_R`-linearly isomorphic to `RealNovikovSeries N₀.M`. -/
noncomputable def constIsocrystal_to_realSeries {R : Type u} [CommRing R]
    (N₀ : FiniteProjectiveModule R) :
    (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) (A := R) N₀).M ≃ₗ[RealNovikovSeries R]
    RealNovikovSeries N₀.M := by
  haveI : Module.FinitePresentation R N₀.M :=
    Module.finitePresentation_of_projective R N₀.M
  exact novikovModule_base_change_equiv (⊤ : AddSubgroup ℝ)

/-- The map `m ↦ 1 ⊗ m` from `M.M` to `R_B ⊗_{R_A} M.M` is injective when `f : A → B`
is injective (hence `realNovikovSeriesRingHom f` is injective) and `M.M` is flat
over `R_A` (automatic when it is finite projective). -/
lemma one_tensor_injective (M : NovikovIsocrystal (Λ := Λ) A) (hf : Function.Injective f) :
    letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) := realNovikovSeriesAlgebra f
    letI : Module (RealNovikovSeries A) (RealNovikovSeries B) := Algebra.toModule
    Function.Injective (fun m : M.M =>
      ((1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] m
        : (RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M)) := by
  letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) := realNovikovSeriesAlgebra f
  letI : Module (RealNovikovSeries A) (RealNovikovSeries B) := Algebra.toModule
  haveI : Module.Flat (RealNovikovSeries A) M.M := inferInstance
  let φ_lin : (RealNovikovSeries A) →ₗ[RealNovikovSeries A] (RealNovikovSeries B) :=
    Algebra.linearMap _ _
  have hφ_inj : Function.Injective φ_lin := by
    change Function.Injective (algebraMap (RealNovikovSeries A) (RealNovikovSeries B))
    exact map_injective f.toAddMonoidHom hf
  have h_rTensor_inj :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := M.M) φ_lin hφ_inj
  intro m1 m2 h
  -- Apply `rTensor M.M φ_lin` to `(1 : R_A) ⊗ₜ m`, getting `(1 : R_B) ⊗ₜ m`.
  have h_aux : ∀ m : M.M,
      LinearMap.rTensor M.M φ_lin
        ((1 : RealNovikovSeries A) ⊗ₜ[RealNovikovSeries A] m) =
        ((1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] m
          : (RealNovikovSeries B) ⊗[RealNovikovSeries A] M.M) := by
    intro m
    rw [LinearMap.rTensor_tmul]
    have h1 : φ_lin (1 : RealNovikovSeries A) = (1 : RealNovikovSeries B) := by
      change (algebraMap _ _) (1 : RealNovikovSeries A) = (1 : RealNovikovSeries B)
      exact map_one _
    rw [h1]
  have h_eq : LinearMap.rTensor M.M φ_lin
      ((1 : RealNovikovSeries A) ⊗ₜ[RealNovikovSeries A] m1) =
      LinearMap.rTensor M.M φ_lin
        ((1 : RealNovikovSeries A) ⊗ₜ[RealNovikovSeries A] m2) := by
    rw [h_aux m1, h_aux m2]; exact h
  have h_one_tensor_eq : ((1 : RealNovikovSeries A) ⊗ₜ[RealNovikovSeries A] m1
      : (RealNovikovSeries A) ⊗[RealNovikovSeries A] M.M) =
      ((1 : RealNovikovSeries A) ⊗ₜ[RealNovikovSeries A] m2
        : (RealNovikovSeries A) ⊗[RealNovikovSeries A] M.M) :=
    h_rTensor_inj h_eq
  -- Use `(TensorProduct.lid R M.M).symm m = 1 ⊗ m` plus injectivity of `.symm`.
  have h_sym : ∀ m : M.M,
      ((TensorProduct.lid (RealNovikovSeries A) M.M).symm m : _ ⊗[_] M.M) =
        (1 : RealNovikovSeries A) ⊗ₜ[RealNovikovSeries A] m :=
    fun m => TensorProduct.lid_symm_apply m
  have h_via_symm : (TensorProduct.lid (RealNovikovSeries A) M.M).symm m1 =
      (TensorProduct.lid (RealNovikovSeries A) M.M).symm m2 := by
    rw [h_sym m1, h_sym m2]; exact h_one_tensor_eq
  exact (TensorProduct.lid (RealNovikovSeries A) M.M).symm.injective h_via_symm

/-- `constIsocrystal_to_realSeries` intertwines `(ConstIsocrystal N₀).F_M` and
`frobenius Λ`. Proved by tensor-product induction on the underlying element. -/
lemma constIsocrystal_to_realSeries_commutes_frobenius {R : Type u} [CommRing R]
    (N₀ : FiniteProjectiveModule R) (x : (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) N₀).M) :
    (constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap
      ((NovikovIsocrystal.ConstIsocrystal (Λ := Λ) N₀).F_M x) =
    frobenius Λ ((constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap x) := by
  let φ := constIsocrystal_to_realSeries (Λ := Λ) N₀
  let F := (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) N₀).F_M
  induction x using TensorProduct.induction_on with
  | zero =>
    change φ (F 0) = frobenius Λ (φ 0)
    simp
  | tmul s n =>
    -- `F (s ⊗ n) = (frobeniusAlgHom s) ⊗ n`, then both sides reduce to a smul of `novikovMonomial n 0`.
    have h_F_tmul : F (s ⊗ₜ[R] n) = (frobeniusAlgHom (Λ := Λ) (A := R) s) ⊗ₜ[R] n := rfl
    rw [h_F_tmul]
    change novikovBaseChangeMap (⊤ : AddSubgroup ℝ)
        ((frobeniusAlgHom (Λ := Λ) (A := R) s) ⊗ₜ[R] n) =
      frobenius Λ (novikovBaseChangeMap (⊤ : AddSubgroup ℝ) (s ⊗ₜ[R] n))
    rw [novikovBaseChangeMap_tmul, novikovBaseChangeMap_tmul]
    ext d
    have aux : ∀ (g : NovikovSeries (⊤ : AddSubgroup ℝ) Unit R)
        (e : Unit → (⊤ : AddSubgroup ℝ)),
        (g • (novikovMonomial n 0 :
            NovikovSeries (⊤ : AddSubgroup ℝ) Unit N₀.M)).val e = g.val e • n := by
      intro g e
      have h := Novikov.novikovSeriesMul_right_monomial
        (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
        (f := g) (b := n) (α := Novikov.smulAddHom (A := R) (M := N₀.M))
        (d := (0 : Unit → (⊤ : AddSubgroup ℝ))) (e := e)
      simp only [add_zero] at h
      change (novikovSeriesMul g (novikovMonomial n 0)
          (Novikov.smulAddHom (A := R) (M := N₀.M))).val e = _
      rw [h]
      simp [Novikov.smulAddHom, _root_.smulAddHom_apply]
    rw [aux (frobeniusAlgHom (Λ := Λ) (A := R) s) d, frobenius_apply_val, aux s _]
    rfl
  | add x y hx hy =>
    -- Re-cast hx, hy so the form matches the calc form (no `.toLinearMap`).
    have hx' : φ (F x) = (frobenius Λ) (φ x) := hx
    have hy' : φ (F y) = (frobenius Λ) (φ y) := hy
    have hF : F (x + y) = F x + F y := map_add _ x y
    have hE : φ (F x + F y) = φ (F x) + φ (F y) := map_add _ _ _
    have hE2 : φ (x + y) = φ x + φ y := map_add _ x y
    have hFr : (frobenius Λ) (φ x + φ y) = (frobenius Λ) (φ x) + (frobenius Λ) (φ y) :=
      map_add _ _ _
    calc φ (F (x + y))
        = φ (F x) + φ (F y) := by rw [hF]; exact hE
      _ = (frobenius Λ) (φ x) + (frobenius Λ) (φ y) := by rw [hx', hy']
      _ = (frobenius Λ) (φ x + φ y) := hFr.symm
      _ = (frobenius Λ) (φ (x + y)) := by rw [hE2]

/--
Proposition 3.7 (`Prop:NovIsocInjective`): If `f : A → B` is an injective
ring homomorphism and the base change of a Novikov isocrystal `M` to `B`
is the constant isocrystal of a finite projective `B`-module `N₀`,
then `M` is itself a constant isocrystal of some finite projective `A`-module.
-/
lemma nov_isoc_injective (hf : Function.Injective f) (M : NovikovIsocrystal (Λ := Λ) A)
    (N₀ : FiniteProjectiveModule B)
    (iso : baseChange f M ≅ NovikovIsocrystal.ConstIsocrystal N₀) :
    ∃ (M₀ : FiniteProjectiveModule A), Nonempty (M ≅ NovikovIsocrystal.ConstIsocrystal M₀) := by
  -- Shared helper: the algebra map R_A → R_B is a closed embedding.
  -- (Needs `DiscreteTopology B` which is set locally.)
  have h_alg_closed_emb_lemma : Topology.IsClosedEmbedding
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) f : RealNovikovSeries A → RealNovikovSeries B) := by
    letI : TopologicalSpace B := ⊥
    haveI : DiscreteTopology B := ⟨rfl⟩
    have h_emb : Topology.IsEmbedding (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) f) :=
      lmap_isEmbedding (Γ := (⊤ : AddSubgroup ℝ)) (R := ℤ)
        (f.toAddMonoidHom.toIntLinearMap) hf
    have h_cl : IsClosed (Set.range (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) f)) :=
      realNovikovSeriesRingHom_closed_range f
    exact Topology.IsClosedEmbedding.mk h_emb h_cl
  -- Now the main proof.
  letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) := realNovikovSeriesAlgebra f
  letI : Module (RealNovikovSeries A) (RealNovikovSeries B) := Algebra.toModule
  letI : Module A N₀.M := Module.compHom N₀.M f
  letI : Module (RealNovikovSeries A) (baseChange f M).M :=
    Module.compHom _ (algebraMap (RealNovikovSeries A) (RealNovikovSeries B))
  letI : Module (RealNovikovSeries A) (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) (A := B) N₀).M :=
    Module.compHom _ (algebraMap (RealNovikovSeries A) (RealNovikovSeries B))
  -- Key lemma: (algebraMap R_A R_B a) • s = a • s on RealNovikovSeries N₀.M
  have h_smul_algebraMap (a : RealNovikovSeries A) (s : RealNovikovSeries N₀.M) :
      (algebraMap (RealNovikovSeries A) (RealNovikovSeries B) a) • s = a • s := by
    ext d
    have h := novikovSeriesMul_map (A := A) (B := N₀.M) (C := N₀.M)
      (A' := B) (B' := N₀.M) (C' := N₀.M)
      (φa := f.toAddMonoidHom) (φb := AddMonoidHom.id N₀.M) (φc := AddMonoidHom.id N₀.M)
      (α := Novikov.smulAddHom (A := A) (M := N₀.M))
      (α' := Novikov.smulAddHom (A := B) (M := N₀.M))
      (hcompat := by intro a' x; rfl)
      (f := a) (s := s)
      (f' := algebraMap (RealNovikovSeries A) (RealNovikovSeries B) a) (s' := s)
      (hf := fun d' => mapRingHom_apply f a d')
      (hs := fun _ => rfl)
      (d := d)
    simpa [Novikov.novikovSMul_val] using h.symm
  -- (1) Embedding ψ : M.M → RealNovikovSeries N₀.M via flat base change + iso composition.
  have h_embed : ∃ ψ : M.M →ₗ[RealNovikovSeries A] RealNovikovSeries N₀.M,
      Function.Injective ψ ∧
      (∀ m, (frobenius Λ : RealNovikovSeries N₀.M →+ RealNovikovSeries N₀.M) (ψ m) =
        ψ (M.F_M m)) ∧
      (∀ m, ψ m = (constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap
        (iso.hom.toLinearMap
          ((1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] m))) := by
    -- ι : M.M ↪ (baseChange f M).M via 1 ⊗ -
    let ι (m : M.M) : (baseChange f M).M := (1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] m
    haveI : IsScalarTower (RealNovikovSeries A) (RealNovikovSeries A) (RealNovikovSeries B) := by
      refine ⟨fun x y z => ?_⟩
      calc
        ((x * y) • z) = (algebraMap (RealNovikovSeries A) (RealNovikovSeries B) (x * y)) * z := rfl
        _ = ((algebraMap _ _ x * algebraMap _ _ y)) * z := by rw [map_mul _]
        _ = (algebraMap _ _ x) * ((algebraMap _ _ y) * z) := by rw [mul_assoc]
        _ = x • ((algebraMap _ _ y) * z) := by rw [← Algebra.smul_def]
        _ = x • (y • z) := by rw [← Algebra.smul_def]
    haveI : IsScalarTower (RealNovikovSeries A) (RealNovikovSeries A) M.M :=
      ⟨fun x y z => (smul_smul x y z).symm⟩
    haveI : CompatibleSMul (RealNovikovSeries A) (RealNovikovSeries A) (RealNovikovSeries B) M.M :=
      TensorProduct.CompatibleSMul.isScalarTower (R := RealNovikovSeries A)
        (R' := RealNovikovSeries A) (M := RealNovikovSeries B) (N := M.M)
    have h_ι_smul (a : RealNovikovSeries A) (m : M.M) : ι (a • m) = a • ι m := by
      dsimp [ι]
      calc
        (1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] (a • m) =
            (a • (1 : RealNovikovSeries B)) ⊗ₜ[RealNovikovSeries A] m := by
          rw [← TensorProduct.smul_tmul (r := a) (m := (1 : RealNovikovSeries B)) (n := m)]
        _ = a • ((1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] m) := by
          rw [← TensorProduct.smul_tmul' (r := a) (m := (1 : RealNovikovSeries B)) (n := m)]
    have h_ι_add (x y : M.M) : ι (x + y) = ι x + ι y := by
      dsimp [ι]; exact TensorProduct.tmul_add (R := RealNovikovSeries A) (M := RealNovikovSeries B) (N := M.M) (m := 1) (n₁ := x) (n₂ := y)
    -- ψ as function: ι → iso.hom → constIsocrystal_to_realSeries
    let ψ_fun (m : M.M) : RealNovikovSeries N₀.M :=
      (constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap (iso.hom.toLinearMap (ι m))
    have h_ψ_smul (a : RealNovikovSeries A) (m : M.M) : ψ_fun (a • m) = a • ψ_fun m := by
      dsimp [ψ_fun]
      rw [h_ι_smul]
      have h1 : iso.hom.toLinearMap (a • ι m) = a • iso.hom.toLinearMap (ι m) := by
        calc
          iso.hom.toLinearMap (a • ι m) =
              iso.hom.toLinearMap ((algebraMap (RealNovikovSeries A) (RealNovikovSeries B) a) • ι m) :=
            rfl
          _ = (algebraMap (RealNovikovSeries A) (RealNovikovSeries B) a) •
              iso.hom.toLinearMap (ι m) := by
            rw [iso.hom.toLinearMap.map_smul]
          _ = a • iso.hom.toLinearMap (ι m) := rfl
      rw [h1]
      calc
        (constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap
          (a • iso.hom.toLinearMap (ι m)) =
          (constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap
            ((algebraMap (RealNovikovSeries A) (RealNovikovSeries B) a) •
              iso.hom.toLinearMap (ι m)) :=
          rfl
        _ = (algebraMap (RealNovikovSeries A) (RealNovikovSeries B) a) •
            (constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap
              (iso.hom.toLinearMap (ι m)) := by
          rw [(constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap.map_smul]
        _ = a • (constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap
              (iso.hom.toLinearMap (ι m)) := by
          rw [h_smul_algebraMap]
    let ψ : M.M →ₗ[RealNovikovSeries A] RealNovikovSeries N₀.M :=
    { toFun := ψ_fun
      map_add' := by
        intro x y
        dsimp [ψ_fun]
        rw [h_ι_add]
        simp [map_add]
      map_smul' := h_ψ_smul
    }
    refine ⟨ψ, ?_, ?_, fun _ => rfl⟩
    · -- Injectivity: composition of injective maps.
      have hι_inj : Function.Injective ι := by
        -- ι = TensorProduct.mk R_A R_B M.M 1, which is injective by one_tensor_injective
        intro x y h
        apply one_tensor_injective f M hf
        simpa [ι] using h
      have hiso_inj : Function.Injective iso.hom.toLinearMap := by
        -- iso.hom is an isomorphism, so iso.inv is a left inverse
        have h_left_inv : ∀ z, iso.inv.toLinearMap (iso.hom.toLinearMap z) = z := by
          intro z
          calc
            iso.inv.toLinearMap (iso.hom.toLinearMap z) =
                (iso.inv.toLinearMap.comp iso.hom.toLinearMap) z := rfl
            _ = (iso.hom ≫ iso.inv).toLinearMap z := rfl
            _ = (CategoryStruct.id (baseChange f M)).toLinearMap z := by
              rw [iso.hom_inv_id]
            _ = z := rfl
        intro x y h
        calc
          x = iso.inv.toLinearMap (iso.hom.toLinearMap x) := (h_left_inv x).symm
          _ = iso.inv.toLinearMap (iso.hom.toLinearMap y) := by rw [h]
          _ = y := h_left_inv y
      have hconst_inj : Function.Injective
          (constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap :=
        (constIsocrystal_to_realSeries (Λ := Λ) N₀).injective
      -- ψ_fun = constIsocrystal_to_realSeries.toLinearMap ∘ iso.hom.toLinearMap ∘ ι
      have hψ_inj : Function.Injective ψ_fun :=
        hconst_inj.comp (hiso_inj.comp hι_inj)
      exact hψ_inj
    · -- Frobenius commutativity:
      --   ψ (M.F_M m) = equiv (iso.hom (1 ⊗ M.F_M m))
      --              = equiv (iso.hom (φ_B 1 ⊗ M.F_M m))    -- φ_B 1 = 1
      --              = equiv (iso.hom ((baseChange f M).F_M (1 ⊗ m)))
      --              = equiv ((ConstIsocrystal N₀).F_M (iso.hom (1 ⊗ m)))
      --              = frobenius Λ (equiv (iso.hom (1 ⊗ m)))
      --              = frobenius Λ (ψ m).
      intro m
      -- Step: 1 ⊗ M.F_M m = (baseChange f M).F_M (1 ⊗ m).
      have h_ι_F : ((1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] (M.F_M m)
          : (baseChange f M).M) =
          (baseChange f M).F_M ((1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] m) := by
        rw [baseChange_F_tmul]
        congr 1
        exact (map_one (frobeniusRingHom (Λ := Λ) (A := B))).symm
      -- Step: iso.hom intertwines F_M.
      have h_iso_F := iso.hom.commute_frobenius
        ((1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] m)
      -- Assemble.
      change frobenius Λ ((constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap
          (iso.hom.toLinearMap ((1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] m))) =
        (constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap
          (iso.hom.toLinearMap ((1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] (M.F_M m)))
      rw [h_ι_F, ← h_iso_F, ← constIsocrystal_to_realSeries_commutes_frobenius (Λ := Λ)]
  obtain ⟨ψ, hψ_inj, hψ_frob, hψ_char⟩ := h_embed
  -- (2) The image of `ψ` as an `A`-submodule of `RealNovikovSeries N₀.M`.
  let M_img_A : Submodule A (RealNovikovSeries N₀.M) :=
    (LinearMap.range ψ).restrictScalars A
  -- (3) The image satisfies the Frobenius-limit hypothesis (closed + F-stable + shift-stable).
  have h_hyp : FrobeniusLimitHyp (Λ := Λ) M_img_A := {
    closed := by
      -- Step 1: `algebraMap R_A R_B` is a closed embedding (factored into lemma above).
      have h_alg_closed_emb := h_alg_closed_emb_lemma
      haveI hR_A := is_topological_ring (Γ := (⊤ : AddSubgroup ℝ)) (A := A)
      haveI hR_B := is_topological_ring (Γ := (⊤ : AddSubgroup ℝ)) (A := B)
      -- Step 2: `isClosedEmbedding_baseChange` → `m ↦ 1 ⊗ m : M.M → R_B ⊗ M.M`
      -- is a closed embedding (canonical R_A on M.M, canonical R_B on R_B ⊗ M.M).
      have h_ι_cl_emb_raw := Novikov.Miscellany.isClosedEmbedding_baseChange
        h_alg_closed_emb M.M
      -- Activate the canonical topologies needed.
      letI tM_M : TopologicalSpace M.M :=
        Novikov.Miscellany.canonicalTopology (RealNovikovSeries A) M.M
      letI tRB_M : TopologicalSpace ((baseChange f M).M) :=
        Novikov.Miscellany.canonicalTopology (RealNovikovSeries B) _
      have h_ι_cl_emb : @Topology.IsClosedEmbedding M.M ((baseChange f M).M) tM_M tRB_M
          (TensorProduct.mk (RealNovikovSeries A) (RealNovikovSeries B) M.M
            (1 : RealNovikovSeries B)) := h_ι_cl_emb_raw
      letI tCI_M : TopologicalSpace ((NovikovIsocrystal.ConstIsocrystal (Λ := Λ) N₀).M) :=
        Novikov.Miscellany.canonicalTopology (RealNovikovSeries B) _
      -- Step 3: iso.hom is canonical-R_B continuous (both directions).
      have h_iso_hom_cont : @Continuous _ _ tRB_M tCI_M iso.hom.toLinearMap :=
        Novikov.Miscellany.canonicalTopology.continuous_linearMap
          (RealNovikovSeries B) _ _ iso.hom.toLinearMap
      have h_iso_inv_cont : @Continuous _ _ tCI_M tRB_M iso.inv.toLinearMap :=
        Novikov.Miscellany.canonicalTopology.continuous_linearMap
          (RealNovikovSeries B) _ _ iso.inv.toLinearMap
      -- Step 4: `constIsocrystal_to_realSeries N₀` is R_B-linear iso (CI N₀).M ≃ R(N₀.M);
      -- canonical R_B on R(N₀.M) = t-adic (`canonicalTopology_realNovikovSeries_eq`).
      have h_canon_eq : Novikov.Miscellany.canonicalTopology
          (RealNovikovSeries B) (RealNovikovSeries N₀.M) =
          (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M)) :=
        canonicalTopology_realNovikovSeries_eq (A := B) (M := N₀.M)
      have h_ε_cont :
          @Continuous _ _ tCI_M (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M))
            (constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap := by
        rw [← h_canon_eq]
        exact Novikov.Miscellany.canonicalTopology.continuous_linearMap
          (RealNovikovSeries B) _ _ (constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap
      have h_ε_inv_cont :
          @Continuous _ _ (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M)) tCI_M
            (constIsocrystal_to_realSeries (Λ := Λ) N₀).symm.toLinearMap := by
        rw [← h_canon_eq]
        exact Novikov.Miscellany.canonicalTopology.continuous_linearMap
          (RealNovikovSeries B) _ _ (constIsocrystal_to_realSeries (Λ := Λ) N₀).symm.toLinearMap
      -- Build the homeomorphism `R_B ⊗ M.M ≃ₕ R(N₀.M)` (composing iso.hom ∘ ε).
      let h_homeo :
          @Homeomorph _ _ tRB_M (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M)) :=
        { toFun := fun x => (constIsocrystal_to_realSeries (Λ := Λ) N₀).toLinearMap
            (iso.hom.toLinearMap x)
          invFun := fun y => iso.inv.toLinearMap
            ((constIsocrystal_to_realSeries (Λ := Λ) N₀).symm.toLinearMap y)
          left_inv := by
            intro x
            change iso.inv.toLinearMap ((constIsocrystal_to_realSeries (Λ := Λ) N₀).symm
                ((constIsocrystal_to_realSeries (Λ := Λ) N₀) (iso.hom.toLinearMap x))) = x
            rw [LinearEquiv.symm_apply_apply]
            change (iso.inv.toLinearMap.comp iso.hom.toLinearMap) x = x
            change (iso.hom ≫ iso.inv).toLinearMap x = x
            rw [iso.hom_inv_id]; rfl
          right_inv := by
            intro y
            change (constIsocrystal_to_realSeries (Λ := Λ) N₀)
              (iso.hom.toLinearMap (iso.inv.toLinearMap
                ((constIsocrystal_to_realSeries (Λ := Λ) N₀).symm.toLinearMap y))) = y
            have h : iso.hom.toLinearMap (iso.inv.toLinearMap
                ((constIsocrystal_to_realSeries (Λ := Λ) N₀).symm.toLinearMap y)) =
                (constIsocrystal_to_realSeries (Λ := Λ) N₀).symm.toLinearMap y := by
              change (iso.hom.toLinearMap.comp iso.inv.toLinearMap) _ = _
              change (iso.inv ≫ iso.hom).toLinearMap _ = _
              rw [iso.inv_hom_id]; rfl
            rw [h]
            exact (constIsocrystal_to_realSeries (Λ := Λ) N₀).apply_symm_apply y
          continuous_toFun := h_ε_cont.comp h_iso_hom_cont
          continuous_invFun := h_iso_inv_cont.comp h_ε_inv_cont }
      -- Range ψ = image of range ι under `h_homeo`.
      have h_range_eq : (M_img_A : Set (RealNovikovSeries N₀.M)) =
          h_homeo '' (Set.range (TensorProduct.mk (RealNovikovSeries A) (RealNovikovSeries B) M.M
            (1 : RealNovikovSeries B))) := by
        change (↑ψ.range : Set (RealNovikovSeries N₀.M)) = _
        ext y
        constructor
        · rintro ⟨m, rfl⟩
          exact ⟨(1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] m, ⟨m, rfl⟩, (hψ_char m).symm⟩
        · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
          exact ⟨m, hψ_char m⟩
      rw [h_range_eq]
      have h_closed_src : @IsClosed ((baseChange f M).M) tRB_M
          (Set.range (TensorProduct.mk (RealNovikovSeries A) (RealNovikovSeries B) M.M
            (1 : RealNovikovSeries B)) : Set ((baseChange f M).M)) := by
        exact h_ι_cl_emb.isClosed_range
      exact (Homeomorph.isClosed_image h_homeo).mpr h_closed_src
    stable_F := by
      -- For `s = ψ m`, `F s = F (ψ m) = ψ (F_M m) ∈ image`.
      rintro s ⟨m, hm⟩
      exact ⟨M.F_M m, by rw [← hψ_frob m, hm]⟩
    stable_shift := by
      -- For `s = ψ m`, `t^d • s = t^d • ψ m = ψ (t^d • m) ∈ image`.
      rintro d s ⟨m, hm⟩
      exact ⟨(novikovMonomial (1 : A)
        (fun _ : Unit => ⟨d, AddSubgroup.mem_top _⟩) : RealNovikovSeries A) • m,
        by rw [ψ.map_smul, hm]⟩
  }
  -- (4) Apply `frobenius_limit` to get `M_img_A = submoduleSeries (S_zero_submodule M_img_A)`.
  have h_decomp : M_img_A = submoduleSeries (S_zero_submodule M_img_A) :=
    frobenius_limit (Λ := Λ) M_img_A h_hyp
  -- (5) `M_zero := S_zero_submodule M_img_A` is a finite projective `A`-submodule of `N₀.M`.
  let M_zero : Submodule A N₀.M := S_zero_submodule M_img_A
  -- (5a) The `R_A`-linear lift `RealNovikovSeries M_zero → RealNovikovSeries N₀.M`
  -- induced by the inclusion `M_zero ↪ N₀.M`.
  let liftMap : RealNovikovSeries M_zero →ₗ[RealNovikovSeries A] RealNovikovSeries N₀.M :=
    lmapNovikov (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) M_zero.subtype
  have h_liftMap_inj : Function.Injective liftMap :=
    lmap_injective (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) M_zero.subtype
      M_zero.injective_subtype
  -- (5b) `range ψ = range liftMap` as `R_A`-submodules of `RealNovikovSeries N₀.M`.
  have h_ranges_eq : LinearMap.range ψ = LinearMap.range liftMap := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      have h_mem : ψ m ∈ submoduleSeries M_zero := by
        have h_ψm : ψ m ∈ M_img_A := by
          change ψ m ∈ (LinearMap.range ψ).restrictScalars A
          exact ⟨m, rfl⟩
        rw [h_decomp] at h_ψm
        exact h_ψm
      let t_val : (Unit → (⊤ : AddSubgroup ℝ)) → M_zero :=
        fun d => ⟨(ψ m).val d, h_mem d⟩
      have h_t_nov : isNovikovSeries t_val :=
        is_novikov_series_of_subset (ψ m).prop
          (fun d hd_lift => fun h_orig => hd_lift (Subtype.ext h_orig))
      refine ⟨⟨t_val, h_t_nov⟩, ?_⟩
      ext d
      rfl
    · rintro _ ⟨t, rfl⟩
      have h_mem_sub : liftMap t ∈ submoduleSeries M_zero :=
        fun d => (t.val d).property
      have h_mem_M_img : liftMap t ∈ M_img_A := by
        rw [h_decomp]; exact h_mem_sub
      exact h_mem_M_img
  -- (5c) Build iso `M.M ≃ₗ[R_A] RealNovikovSeries M_zero` via `range ψ = range liftMap`.
  let φ : M.M ≃ₗ[RealNovikovSeries A] RealNovikovSeries M_zero :=
    (LinearEquiv.ofInjective ψ hψ_inj).trans
      ((LinearEquiv.ofEq _ _ h_ranges_eq).trans
        (LinearEquiv.ofInjective liftMap h_liftMap_inj).symm)
  -- Key identity: liftMap ∘ φ = ψ, by construction of φ.
  have h_liftMap_phi : ∀ m : M.M, liftMap (φ m) = ψ m := by
    intro m
    have h1 : (LinearEquiv.ofInjective liftMap h_liftMap_inj) (φ m) =
        ⟨ψ m, by rw [← h_ranges_eq]; exact ⟨m, rfl⟩⟩ := by
      apply (LinearEquiv.ofInjective liftMap h_liftMap_inj).symm.injective
      simp [φ]; rfl
    have h2 : liftMap (φ m) =
        ((LinearEquiv.ofInjective liftMap h_liftMap_inj) (φ m) : RealNovikovSeries N₀.M) := rfl
    rw [h2, h1]
  -- (5d) Transport finiteness and projectivity through `φ`.
  haveI : Module.Finite (RealNovikovSeries A) (RealNovikovSeries M_zero) :=
    Module.Finite.equiv φ
  haveI : Module.Projective (RealNovikovSeries A) (RealNovikovSeries M_zero) :=
    Module.Projective.of_equiv φ
  -- (5e) Prove that canonical R_A-topology on R(M_zero) equals the t-adic topology.
  -- Step (II): t-adic topology = subspace topology induced by `liftMap`.
  have h_liftMap_ind_top :
      TopologicalSpace.induced (liftMap : RealNovikovSeries M_zero → RealNovikovSeries N₀.M)
        (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M)) =
      (inferInstance : TopologicalSpace (RealNovikovSeries M_zero)) := by
    have h_emb : Topology.IsEmbedding (liftMap : RealNovikovSeries M_zero → RealNovikovSeries N₀.M) :=
      lmap_isEmbedding (Γ := (⊤ : AddSubgroup ℝ)) (M_zero.subtype) M_zero.injective_subtype
    exact ((Topology.isInducing_iff (f := liftMap)).mp h_emb.isInducing).symm
  -- Step (I): canonical R_A-topology on M.M = subspace topology induced by ψ from R(N₀.M).
  -- This follows because ψ is a closed embedding (composition of ι : closed embedding,
  -- iso.hom : homeomorphism in canonical R_B, and constIsocrystal_to_realSeries : homeomorphism
  -- canonical R_B → t-adic via `canonicalTopology_realNovikovSeries_eq` for N₀).
  haveI : IsTopologicalRing (RealNovikovSeries A) := is_topological_ring
  haveI : IsTopologicalRing (RealNovikovSeries B) := is_topological_ring
  haveI : IsTopologicalAddGroup (RealNovikovSeries A) := is_topological_add_group
  haveI : IsTopologicalAddGroup (RealNovikovSeries B) := is_topological_add_group
  haveI : IsTopologicalAddGroup (RealNovikovSeries N₀.M) := is_topological_add_group
  -- (a) algebraMap R_A → R_B is a closed embedding (factored into lemma above).
  have h_alg_closed_emb := h_alg_closed_emb_lemma
  -- (b) ι : m ↦ 1 ⊗ m is a closed embedding M.M (canonical R_A) → (baseChange f M).M (canonical R_B).
  have h_ι_cl_emb := Novikov.Miscellany.isClosedEmbedding_baseChange
    h_alg_closed_emb M.M
  letI tM_M : TopologicalSpace M.M :=
    Novikov.Miscellany.canonicalTopology (RealNovikovSeries A) M.M
  letI tRB_M : TopologicalSpace ((baseChange f M).M) :=
    Novikov.Miscellany.canonicalTopology (RealNovikovSeries B) _
  have h_ι_cl_emb' : @Topology.IsClosedEmbedding M.M ((baseChange f M).M) tM_M tRB_M
      (TensorProduct.mk (RealNovikovSeries A) (RealNovikovSeries B) M.M
        (1 : RealNovikovSeries B)) := h_ι_cl_emb
  -- Build R_B-linear equiv from iso
  let iso_equiv : (baseChange f M).M ≃ₗ[RealNovikovSeries B]
      (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) N₀).M :=
    { toFun := iso.hom.toLinearMap
      invFun := iso.inv.toLinearMap
      left_inv := by
        intro x
        change (iso.inv.toLinearMap ∘ iso.hom.toLinearMap) x = x
        change (iso.hom ≫ iso.inv).toLinearMap x = x
        rw [iso.hom_inv_id]; rfl
      right_inv := by
        intro y
        change (iso.hom.toLinearMap ∘ iso.inv.toLinearMap) y = y
        change (iso.inv ≫ iso.hom).toLinearMap y = y
        rw [iso.inv_hom_id]; rfl
      map_add' := iso.hom.toLinearMap.map_add
      map_smul' := iso.hom.toLinearMap.map_smul
    }
  -- (d) constIsocrystal_to_realSeries : homeomorphism canonical R_B → t-adic on R(N₀.M).
  have h_canon_eq_N : Novikov.Miscellany.canonicalTopology
      (RealNovikovSeries B) (RealNovikovSeries N₀.M) =
      (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M)) :=
    canonicalTopology_realNovikovSeries_eq (A := B) (M := N₀.M)
  -- Step (I): canonical R_A-topology on M.M = subspace topology induced by ψ from R(N₀.M).
  -- Prove via chain of topology equalities using canonicalTopology_linearEquiv.
  let ι_map : M.M →ₗ[RealNovikovSeries A] (baseChange f M).M :=
    TensorProduct.mk (RealNovikovSeries A) (RealNovikovSeries B) M.M
      (1 : RealNovikovSeries B)
  -- Compose iso_equiv and constIsocrystal_to_realSeries into a single R_B-linear equiv.
  let total_equiv : (baseChange f M).M ≃ₗ[RealNovikovSeries B] RealNovikovSeries N₀.M :=
    iso_equiv.trans (constIsocrystal_to_realSeries (Λ := Λ) N₀)
  have h_total_equiv : Novikov.Miscellany.canonicalTopology
      (RealNovikovSeries B) ((baseChange f M).M) =
      TopologicalSpace.induced (total_equiv : (baseChange f M).M → RealNovikovSeries N₀.M)
        (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M)) := by
    rw [Novikov.Miscellany.canonicalTopology_linearEquiv total_equiv, h_canon_eq_N]
  have h_canon_M_eq_induced_ψ : tM_M =
      TopologicalSpace.induced (ψ : M.M → RealNovikovSeries N₀.M)
        (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M)) := by
    calc
      tM_M = @TopologicalSpace.induced M.M ((baseChange f M).M) ι_map
          (canonicalTopology (RealNovikovSeries B) ((baseChange f M).M)) :=
        (Topology.isInducing_iff (f := ι_map)).mp
          h_ι_cl_emb'.isEmbedding.isInducing
      _ = @TopologicalSpace.induced M.M (RealNovikovSeries N₀.M)
          (total_equiv ∘ ι_map)
          (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M)) := by
        rw [h_total_equiv, induced_compose]
      _ = TopologicalSpace.induced (ψ : M.M → RealNovikovSeries N₀.M)
          (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M)) := by
        congr 1
        ext x d
        unfold total_equiv iso_equiv ι_map
        rw [hψ_char x]
        rfl
  -- (I-a) Transfer through φ: canonical R_A on R(M_zero) = induced liftMap (t-adic).
  --   canonical R_A R(M_zero) = induced φ.symm (canonical R_A M.M)   [by canonicalTopology_linearEquiv]
  --                         = induced φ.symm (induced ψ τ)            [by h_tM_M_eq_induced_ψ]
  --                         = induced (ψ ∘ φ.symm) τ                  [induced_compose]
  --   ψ ∘ φ.symm = liftMap  (since ψ = liftMap ∘ φ, and φ.symm inverts φ).
  --   So canonical R_A R(M_zero) = induced liftMap τ = t-adic on R(M_zero) [by h_liftMap_ind_top].
  have h_canon_RMzero_eq_induced_liftMap :
      Novikov.Miscellany.canonicalTopology (RealNovikovSeries A) (RealNovikovSeries M_zero) =
      TopologicalSpace.induced (liftMap : RealNovikovSeries M_zero → RealNovikovSeries N₀.M)
        (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M)) := by
    calc
      Novikov.Miscellany.canonicalTopology (RealNovikovSeries A) (RealNovikovSeries M_zero) =
          TopologicalSpace.induced (φ.symm : RealNovikovSeries M_zero → M.M)
            (Novikov.Miscellany.canonicalTopology (RealNovikovSeries A) M.M) :=
        (Novikov.Miscellany.canonicalTopology_linearEquiv φ.symm)
      _ = TopologicalSpace.induced (φ.symm : RealNovikovSeries M_zero → M.M)
          (tM_M) := rfl
      _ = TopologicalSpace.induced (φ.symm : RealNovikovSeries M_zero → M.M)
          (TopologicalSpace.induced (ψ : M.M → RealNovikovSeries N₀.M)
            (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M))) := by rw [h_canon_M_eq_induced_ψ]
      _ = TopologicalSpace.induced (ψ ∘ (φ.symm : RealNovikovSeries M_zero → M.M))
          (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M)) := by rw [induced_compose]
      _ = TopologicalSpace.induced (liftMap : RealNovikovSeries M_zero → RealNovikovSeries N₀.M)
          (inferInstance : TopologicalSpace (RealNovikovSeries N₀.M)) := by
        congr 1
        funext z
        calc
          (ψ ∘ (φ.symm : RealNovikovSeries M_zero → M.M)) z = ψ (φ.symm z) := rfl
          _ = liftMap (φ (φ.symm z)) := (h_liftMap_phi (φ.symm z)).symm
          _ = liftMap z := by rw [φ.apply_symm_apply z]
  -- Combine (I-a) and (II): canonical R_A = t-adic on R(M_zero).
  have h_canon_eq_tadic :
      Novikov.Miscellany.canonicalTopology (RealNovikovSeries A) (RealNovikovSeries M_zero) =
      (inferInstance : TopologicalSpace (RealNovikovSeries M_zero)) := by
    rw [h_canon_RMzero_eq_induced_liftMap, h_liftMap_ind_top]
  -- Final step: for any R_A-linear functional g, it is continuous in the canonical topology
  -- (by definition of canonical topology), hence in the t-adic topology (by equality).
  have h_canonical : ∀ (g : RealNovikovSeries M_zero →ₗ[RealNovikovSeries A]
      RealNovikovSeries A), Continuous g := by
    intro g
    have h_canon_cont : @Continuous _ _
        (Novikov.Miscellany.canonicalTopology (RealNovikovSeries A) (RealNovikovSeries M_zero))
        (Novikov.Miscellany.canonicalTopology (RealNovikovSeries A) (RealNovikovSeries A))
        g :=
      Novikov.Miscellany.canonicalTopology.continuous_linearMap (RealNovikovSeries A)
        (RealNovikovSeries M_zero) (RealNovikovSeries A) g
    have h_canon_self : Novikov.Miscellany.canonicalTopology (RealNovikovSeries A)
        (RealNovikovSeries A) = (inferInstance : TopologicalSpace (RealNovikovSeries A)) :=
      Novikov.Miscellany.canonicalTopology_self_eq (A := RealNovikovSeries A)
    rw [h_canon_eq_tadic, h_canon_self] at h_canon_cont
    exact h_canon_cont
  obtain ⟨h_M_zero_fin, h_M_zero_proj⟩ := projective_of_realNovikovSeries h_canonical
  haveI := h_M_zero_fin
  haveI := h_M_zero_proj
  let M₀ : FiniteProjectiveModule A := ⟨M_zero⟩
  refine ⟨M₀, ⟨?_⟩⟩
  -- (6) Construct iso `M ≅ ConstIsocrystal M₀`.
  haveI : Module.FinitePresentation A M_zero :=
    Module.finitePresentation_of_projective A M_zero
  -- (6a) R_A-linear iso `(ConstIsocrystal M₀).M = R_A ⊗[A] M_zero ≃ R(M_zero)`.
  let ε : (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) (A := A) M₀).M
      ≃ₗ[RealNovikovSeries A] RealNovikovSeries M_zero :=
    constIsocrystal_to_realSeries (Λ := Λ) M₀
  -- (6b) Compose to get `Φ : M.M ≃ₗ[R_A] (ConstIsocrystal M₀).M`.
  let Φ : M.M ≃ₗ[RealNovikovSeries A]
      (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) (A := A) M₀).M :=
    φ.trans ε.symm
  -- (6c) `liftMap` commutes with `frobenius`: both act coefficient-wise.
  have h_liftMap_frob : ∀ x : RealNovikovSeries M_zero,
      liftMap (frobenius Λ x) = frobenius Λ (liftMap x) := by
    intro x; ext d
    change (M_zero.subtype) ((frobenius Λ x).val d) =
      (M_zero.subtype) (x.val (fun _ : Unit => ⟨(d () : ℝ) / Λ, AddSubgroup.mem_top _⟩))
    rw [frobenius_apply_val]
  -- (6d) See `h_liftMap_phi` above.
  -- (6e) `φ` commutes with Frobenius via `liftMap` injectivity.
  have h_phi_frob : ∀ m : M.M, φ (M.F_M m) = frobenius Λ (φ m) := by
    intro m
    apply h_liftMap_inj
    rw [h_liftMap_frob, h_liftMap_phi, h_liftMap_phi, hψ_frob]
  -- (6f) `Φ` commutes with `F_M`.
  have h_Φ_frob : ∀ m : M.M,
      (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) (A := A) M₀).F_M (Φ m) = Φ (M.F_M m) := by
    intro m
    apply ε.injective
    change (constIsocrystal_to_realSeries (Λ := Λ) M₀).toLinearMap _ = _
    rw [constIsocrystal_to_realSeries_commutes_frobenius]
    change frobenius Λ (ε (ε.symm (φ m))) = ε (ε.symm (φ (M.F_M m)))
    rw [ε.apply_symm_apply, ε.apply_symm_apply, h_phi_frob]
  -- (6g) Assemble the categorical iso.
  let homMap : NovikovIsocrystal.Hom M (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) M₀) :=
    { toLinearMap := Φ.toLinearMap
      commute_frobenius := h_Φ_frob }
  let invMap : NovikovIsocrystal.Hom (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) M₀) M :=
    { toLinearMap := Φ.symm.toLinearMap
      commute_frobenius := by
        intro y
        apply Φ.injective
        have h := h_Φ_frob (Φ.symm y)
        rw [Φ.apply_symm_apply] at h
        simp [h] }
  exact {
    hom := homMap
    inv := invMap
    hom_inv_id := by
      apply NovikovIsocrystal.hom_ext
      ext x; change Φ.symm (Φ x) = x; rw [Φ.symm_apply_apply]
    inv_hom_id := by
      apply NovikovIsocrystal.hom_ext
      ext y; change Φ (Φ.symm y) = y; rw [Φ.apply_symm_apply]
  }

end NovIsocInjective

end Novikov
