import Novikov.Descent.Isocrystal
import Novikov.Isocrystal.Constant

/-!
# Constant descent data recover constant isocrystals

This file works towards the compatibility between the constant Novikov descent
datum and the constant Novikov isocrystal: applying `descentToIsocrystal` to a
constant descent datum `vectToNovikovDescent.obj P` should reproduce the constant
isocrystal `vectToNovIsoc.obj P`.

## Key obstacle (the algebra-instance diamond)

The underlying module of `(descentToIsocrystal A).obj ((vectToNovikovDescent ⊤ A).obj P)`
is `RealNovikovSeries A ⊗[A] P.M` where the `A`-algebra on `RealNovikovSeries A` is
`algebraMapNovikov.toAlgebra` (call it `i1`), frozen inside the descent-datum
structure.  The underlying module of `vectToNovIsoc.obj P = ConstIsocrystal P` is
the *same* tensor product but elaborated with the global `novikovAlgebra` instance
(`i2`).  The two `Algebra A (RealNovikovSeries A)` instances share the same
`algebraMap` but differ in their `smul` data, so the two tensor types are *not*
definitionally equal.

The bridge between them is `algebraMapNovikov_toAlgebra_eq` (the two algebras are
propositionally equal).  `cmpMod` records the `i1` module structure as a plain,
non-instance abbreviation: this matters because **any class-typed local binder
(`let`/`have`/`letI`) is treated as a local instance and would shadow the global
`novikovAlgebra`**, breaking the codomain `ConstIsocrystal` tensor.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract

namespace Novikov.Descent

variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]
variable {A : Type*} [CommRing A]

open NovikovIsocrystal

/-- The base-change `algebraMapNovikov` algebra agrees with the global
`novikovAlgebra` on `RealNovikovSeries A`. -/
lemma algebraMapNovikov_toAlgebra_eq :
    (Novikov.algebraMapNovikov
        (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (A := A)).toAlgebra
      = (Novikov.novikovAlgebra : Algebra A (RealNovikovSeries A)) :=
  Algebra.algebra_ext _ _ (fun _ => rfl)

/-- The `Module A (RealNovikovSeries A)` coming from `algebraMapNovikov`, i.e. the
module structure used inside the constant descent datum.  Kept as a plain
(non-instance, reducible) abbreviation so that it does not shadow the global
`novikovAlgebra` instance when it appears in a proof context. -/
@[reducible] noncomputable def cmpMod : Module A (RealNovikovSeries A) :=
  (Novikov.algebraMapNovikov
    (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (A := A)).toAlgebra.toModule

/-- The `i1` module structure equals the global `novikovAlgebra` module structure. -/
lemma cmpMod_eq :
    (cmpMod : Module A (RealNovikovSeries A)) = Novikov.novikovAlgebra.toModule :=
  congrArg (fun a => @Algebra.toModule A (RealNovikovSeries A) _ _ a)
    algebraMapNovikov_toAlgebra_eq

/-- The `A`-linear identity equivalence between the two tensor products of
`RealNovikovSeries A` and `P.M` taken with propositionally equal `A`-module
structures `m1`, `m2` on `RealNovikovSeries A`.

This is *`A`-linear* on purpose: the analogous `RealNovikovSeries A`-linear
statement is not directly expressible, because synthesizing the left
`RealNovikovSeries A`-module structure on the `m1`-tensor clashes with the global
`novikovAlgebra` instance (the algebra-instance diamond).  The base-ring `A`-module
structure on the tensor, by contrast, synthesizes with no diamond. -/
noncomputable def idTensorAEquiv (P : FiniteProjectiveModule A)
    (m1 m2 : Module A (RealNovikovSeries A)) (h : m1 = m2) :
    (@TensorProduct A _ (RealNovikovSeries A) P.M _ _ m1 _) ≃ₗ[A]
      (@TensorProduct A _ (RealNovikovSeries A) P.M _ _ m2 _) := by
  subst h; exact LinearEquiv.refl _ _

@[simp] lemma idTensorAEquiv_tmul (P : FiniteProjectiveModule A)
    (m1 m2 : Module A (RealNovikovSeries A)) (h : m1 = m2)
    (r : RealNovikovSeries A) (p : P.M) :
    idTensorAEquiv P m1 m2 h
        (@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ m1 _ r p) =
      (@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ m2 _ r p) := by
  subst h; rfl

@[simp] lemma idTensorAEquiv_symm_tmul (P : FiniteProjectiveModule A)
    (m1 m2 : Module A (RealNovikovSeries A)) (h : m1 = m2)
    (r : RealNovikovSeries A) (p : P.M) :
    (idTensorAEquiv P m1 m2 h).symm
        (@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ m2 _ r p) =
      (@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ m1 _ r p) := by
  subst h; rfl

/-- The underlying `RealNovikovSeries A`-linear equivalence between the module of
`descentToIsocrystal` applied to the constant descent datum and the module of the
constant isocrystal.

The `RealNovikovSeries A`-semilinearity (`map_smul'`) is proved by tensor
induction.  Because the relevant left-module instances live on the two
*different* tensor products (over `cmpMod` and over `novikovAlgebra.toModule`),
the per-generator `smul` rewrites have to go through `erw` (matching up to
definitional equality) and `show … from smul_zero/smul_add` (which restate the
`smul` facts at the right module instance). -/
noncomputable def cmpEquiv (P : FiniteProjectiveModule A) :
    ((descentToIsocrystal (Λ := Λ) A).obj
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).M ≃ₗ[RealNovikovSeries A]
      ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).M := by
  refine
    { toFun := fun x =>
        idTensorAEquiv P cmpMod Novikov.novikovAlgebra.toModule cmpMod_eq x
      map_add' := fun x y => map_add _ x y
      map_smul' := ?_
      invFun := fun y =>
        (idTensorAEquiv P cmpMod Novikov.novikovAlgebra.toModule cmpMod_eq).symm y
      left_inv := ?_
      right_inv := ?_ }
  · intro r x
    induction x using TensorProduct.induction_on with
    | zero =>
        rw [RingHom.id_apply]
        erw [show (r • (0 : ((descentToIsocrystal (Λ := Λ) A).obj
          ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).M)) = 0 from smul_zero r,
          map_zero,
          show (r • (0 : ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).M)) = 0
            from smul_zero r]
        rfl
    | tmul s p =>
        erw [idTensorAEquiv_tmul, idTensorAEquiv_tmul, RingHom.id_apply,
          TensorProduct.smul_tmul']
        rfl
    | add x y hx hy =>
        erw [smul_add, map_add, hx, hy, map_add, smul_add]
        rfl
  · intro x
    simp only [LinearEquiv.symm_apply_apply]
  · intro y
    simp only [LinearEquiv.apply_symm_apply]

/-- Generic computation: for a constant descent datum, the conjugated Frobenius on
`π₂^* (R₁ ⊗[R₀] M)` fixes the generator `1 ⊗ (1 ⊗ m)` whenever the semilinear
ring endomorphism fixes the `π₁`-base. -/
lemma constantDescent_FM2_generic
    (E : ExtendedCosimplicialRing)
    (σ σinv : E.R₂ →+* E.R₂) [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hσπ₁ : σ.comp E.π₁ = E.π₁) (hσinvπ₁ : σinv.comp E.π₁ = E.π₁)
    (M : Type*) [AddCommGroup M] [Module E.R₀ M]
    [Module.Finite E.R₀ M] [Module.Projective E.R₀ M]
    (m : M) :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    let Mdd : DescentDatum E.toCosimplicialRing := constantDescentDatum E M
    (((Mdd.φ.symm.trans
      (baseChangeSemilinearSelf E.π₁ σ σinv hσπ₁ hσinvπ₁ Mdd.M)).trans Mdd.φ)
      (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
       (1 : E.R₂) ⊗ₜ[E.R₁] ((1 : E.R₁) ⊗ₜ[E.R₀] m))) =
    (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
     (1 : E.R₂) ⊗ₜ[E.R₁] ((1 : E.R₁) ⊗ₜ[E.R₀] m)) := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  intro Mdd
  let m0 : Mdd.M := (1 : E.R₁) ⊗ₜ[E.R₀] m
  let x₂ : (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra; E.R₂ ⊗[E.R₁] Mdd.M) :=
    (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra; (1 : E.R₂) ⊗ₜ[E.R₁] m0)
  let x₁ : (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra; E.R₂ ⊗[E.R₁] Mdd.M) :=
    (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra; (1 : E.R₂) ⊗ₜ[E.R₁] m0)
  let T : (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra; E.R₂ ⊗[E.R₁] Mdd.M) ≃ₛₗ[σ]
      (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra; E.R₂ ⊗[E.R₁] Mdd.M) :=
    baseChangeSemilinearSelf E.π₁ σ σinv hσπ₁ hσinvπ₁ Mdd.M
  change Mdd.φ (T (Mdd.φ.symm x₂)) = x₂
  have hφ : Mdd.φ x₁ = x₂ := by
    subst Mdd
    dsimp [x₁, x₂, m0]
    have h := constantDescentDatum_φ_tmul
      (E := E) (M := M) (r := (1 : E.R₂)) (s := (1 : E.R₁)) (m := m)
    exact h.trans (by rw [map_one, one_mul]; rfl)
  have hφsymm : Mdd.φ.symm x₂ = x₁ := (LinearEquiv.symm_apply_eq _).mpr hφ.symm
  have hT : T x₁ = x₁ := by
    dsimp [T, x₁]
    rw [baseChangeSemilinearSelf_tmul, map_one]
  rw [hφsymm, hT, hφ]

-- Keep the semilinear tensor construction opaque while matching the generic
-- computation against the concrete real-Novikov one.
attribute [local irreducible] baseChangeSemilinearSelf

/-- The descended Frobenius fixes the generator `1 ⊗ p` of the constant descent
datum.

The whole chain (`descentFrobeniusToFun → FM2 → generic computation`) is proved in
a single declaration on purpose.  Each step here (`oneTmulπ₂_injective`,
`descentFrobeniusToFun_spec`, `FM2_apply`, and the final concrete↔generic match of
`constantDescent_FM2_generic`) forces the **kernel** to evaluate the heavy concrete
Novikov descent machinery (`constantDescentDatum (novikovExtendedCosimplicialRing ⊤ A)`
and the algebra-instance diamond).  The kernel ignores the `local irreducible` fence
above (that only speeds up the elaborator), so splitting the chain into separate
lemmas makes the kernel re-evaluate that machinery once per lemma.  Fusing them lets
the single kernel pass share its `whnf` cache across all the steps, which is far
cheaper than the sum of the separate checks. -/
lemma descentFrobeniusToFun_constant_one_tmul
    (P : FiniteProjectiveModule A) (p : P.M) :
    let Mdd := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
    descentFrobeniusToFun (Λ := Λ) A Mdd
      ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
        (1 : RealNovikovSeries A) p) : Mdd.M) =
    ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
      (1 : RealNovikovSeries A) p) : Mdd.M) := by
  intro Mdd
  apply oneTmulπ₂_injective (A := A) Mdd.M
  rw [← descentFrobeniusToFun_spec, FM2_apply]
  exact @constantDescent_FM2_generic
    (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A)
    (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
    (coordinateFrobeniusRingHom_invPair (Λ := Λ) (R := A) (ι := Fin 2) (1 : Fin 2))
    (coordinateFrobeniusRingHom_invPair_symm (Λ := Λ) (R := A) (ι := Fin 2) (1 : Fin 2))
    (F2_comp_π₁_eq (Λ := Λ) A) (F2Inv_comp_π₁_eq (Λ := Λ) A)
    P.M inferInstance P.instModule P.instFinite P.instProjective p

lemma descentFrobeniusToFun_constant_tmul
    (P : FiniteProjectiveModule A) (r : RealNovikovSeries A) (p : P.M) :
    let Mdd := (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P
    descentFrobeniusToFun (Λ := Λ) A Mdd
      ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _ r p) : Mdd.M) =
    ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
      (frobeniusRingHom (Λ := Λ) (A := A) r) p) : Mdd.M) := by
  intro Mdd
  letI : Module (RealNovikovSeries A) Mdd.M := by
    dsimp [RealNovikovSeries, OneVarNovikovSeries, realC]
    exact Mdd.instModule
  let m1 : Mdd.M :=
    ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
      (1 : RealNovikovSeries A) p) : Mdd.M)
  have htmul :
      ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _ r p) : Mdd.M) =
        r • m1 := by
    change ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _ r p) : Mdd.M) =
      ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _ (r * 1) p) : Mdd.M)
    rw [mul_one]
  rw [htmul]
  change (descentFrobenius (Λ := Λ) A Mdd) (r • m1) =
    ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
      (frobeniusRingHom (Λ := Λ) (A := A) r) p) : Mdd.M)
  rw [map_smulₛₗ]
  change frobeniusRingHom (Λ := Λ) (A := A) r •
      descentFrobeniusToFun (Λ := Λ) A Mdd m1 = _
  rw [descentFrobeniusToFun_constant_one_tmul]
  change ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
      (frobeniusRingHom (Λ := Λ) (A := A) r * 1) p) : Mdd.M) = _
  rw [mul_one]

lemma ConstIsocrystal_F_tmul
    (P : FiniteProjectiveModule A) (r : RealNovikovSeries A) (p : P.M) :
    ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).F_M (r ⊗ₜ[A] p) =
      (frobeniusRingHom (Λ := Λ) (A := A) r) ⊗ₜ[A] p := by
  dsimp [NovikovIsocrystal.vectToNovIsoc, NovikovIsocrystal.ConstIsocrystal]
  change TensorProduct.map (frobeniusAlgHom (Λ := Λ) (A := A)).toLinearMap LinearMap.id
      (r ⊗ₜ[A] p) = _
  rw [TensorProduct.map_tmul]
  rfl

lemma cmpEquiv_commute_frobenius (P : FiniteProjectiveModule A)
    (x : ((descentToIsocrystal (Λ := Λ) A).obj
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).M) :
      ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).F_M
        ((cmpEquiv (Λ := Λ) P).toLinearMap x) =
      (cmpEquiv (Λ := Λ) P).toLinearMap
        (((descentToIsocrystal (Λ := Λ) A).obj
          ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).F_M x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      let e := cmpEquiv (Λ := Λ) P
      change ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).F_M
          (e.toLinearMap 0) =
        e.toLinearMap
          (((descentToIsocrystal (Λ := Λ) A).obj
            ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).F_M 0)
      rw [e.toLinearMap.map_zero]
      rw [map_zero]
      rw [map_zero]
      rw [e.toLinearMap.map_zero]
  | tmul r p =>
      change ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).F_M
          ((cmpEquiv (Λ := Λ) P).toLinearMap
            ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
              (r : RealNovikovSeries A) p) :
              ((descentToIsocrystal (Λ := Λ) A).obj
                ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).M)) =
        (cmpEquiv (Λ := Λ) P).toLinearMap
          (descentFrobeniusToFun (Λ := Λ) A
            ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)
            ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
              (r : RealNovikovSeries A) p) :
              ((descentToIsocrystal (Λ := Λ) A).obj
                ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).M))
      rw [descentFrobeniusToFun_constant_tmul]
      rw [show (cmpEquiv (Λ := Λ) P).toLinearMap
            ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
              (r : RealNovikovSeries A) p) :
              ((descentToIsocrystal (Λ := Λ) A).obj
                ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).M) =
          ((r : RealNovikovSeries A) ⊗ₜ[A] p :
            ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).M) by
        simp [cmpEquiv]]
      rw [show (cmpEquiv (Λ := Λ) P).toLinearMap
            ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
              (frobeniusRingHom (Λ := Λ) (A := A) (r : RealNovikovSeries A)) p) :
              ((descentToIsocrystal (Λ := Λ) A).obj
                ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).M) =
          (frobeniusRingHom (Λ := Λ) (A := A) (r : RealNovikovSeries A) ⊗ₜ[A] p :
            ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).M) by
        simp [cmpEquiv]]
      rw [ConstIsocrystal_F_tmul]
  | add x y hx hy =>
      let e := cmpEquiv (Λ := Λ) P
      change ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).F_M
          (e.toLinearMap (x + y)) =
        e.toLinearMap
          (((descentToIsocrystal (Λ := Λ) A).obj
            ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).F_M (x + y))
      erw [e.toLinearMap.map_add]
      rw [map_add]
      rw [show (((descentToIsocrystal (Λ := Λ) A).obj
            ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).F_M (x + y)) =
          (((descentToIsocrystal (Λ := Λ) A).obj
            ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).F_M x) +
          (((descentToIsocrystal (Λ := Λ) A).obj
            ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).F_M y) from
        map_add _ x y]
      erw [e.toLinearMap.map_add]
      rw [hx, hy]

/-- Objectwise compatibility iso: `descentToIsocrystal` of the constant descent
datum is the constant isocrystal. -/
noncomputable def descentToIsocrystal_vectToNovikovDescent_obj_iso
    (P : FiniteProjectiveModule A) :
    (descentToIsocrystal (Λ := Λ) A).obj
        ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P) ≅
      (NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P where
  hom :=
    { toLinearMap := (cmpEquiv P).toLinearMap
      commute_frobenius := cmpEquiv_commute_frobenius P }
  inv :=
    { toLinearMap := (cmpEquiv P).symm.toLinearMap
      commute_frobenius := by
        intro y
        let e := cmpEquiv (Λ := Λ) P
        apply e.injective
        change e.toLinearMap
            ((((descentToIsocrystal (Λ := Λ) A).obj
              ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).F_M
              (e.symm.toLinearMap y))) =
          e.toLinearMap (e.symm.toLinearMap
            (((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).F_M y))
        rw [← cmpEquiv_commute_frobenius (Λ := Λ) P (e.symm.toLinearMap y)]
        change ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).F_M
            (e.toLinearMap (e.symm.toLinearMap y)) =
          e.toLinearMap (e.symm.toLinearMap
            (((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).F_M y))
        erw [e.apply_symm_apply, e.apply_symm_apply] }
  hom_inv_id := by
    apply NovikovIsocrystal.hom_ext
    ext x
    exact (cmpEquiv P).symm_apply_apply x
  inv_hom_id := by
    apply NovikovIsocrystal.hom_ext
    ext x
    exact (cmpEquiv P).apply_symm_apply x

lemma descentToIsocrystal_vectToNovikovDescent_obj_iso_naturality
    (P Q : FiniteProjectiveModule A) (f : P ⟶ Q) :
    (descentToIsocrystal_vectToNovikovDescent_obj_iso (Λ := Λ) P).hom ≫
        (NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).map f =
      (((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A) ⋙
          (descentToIsocrystal (Λ := Λ) A)).map f ≫
        (descentToIsocrystal_vectToNovikovDescent_obj_iso (Λ := Λ) Q).hom) := by
  apply NovikovIsocrystal.hom_ext
  ext x
  change ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).map f).toLinearMap
      ((cmpEquiv (Λ := Λ) P).toLinearMap x) =
    (cmpEquiv (Λ := Λ) Q).toLinearMap
      ((((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A) ⋙
          (descentToIsocrystal (Λ := Λ) A)).map f).toLinearMap x)
  induction x using TensorProduct.induction_on with
  | zero =>
      let eP := cmpEquiv (Λ := Λ) P
      let eQ := cmpEquiv (Λ := Λ) Q
      change ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).map f).toLinearMap
          (eP.toLinearMap 0) =
        eQ.toLinearMap
          ((((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A) ⋙
            (descentToIsocrystal (Λ := Λ) A)).map f).toLinearMap 0)
      rw [eP.toLinearMap.map_zero, map_zero, map_zero]
      exact (eQ.toLinearMap.map_zero).symm
  | tmul r p =>
      change ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).map f).toLinearMap
          ((cmpEquiv (Λ := Λ) P).toLinearMap
            ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
              (r : RealNovikovSeries A) p) :
              ((descentToIsocrystal (Λ := Λ) A).obj
                ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).M)) =
        (cmpEquiv (Λ := Λ) Q).toLinearMap
          (((descentToIsocrystal (Λ := Λ) A).map
            ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).map f)).toLinearMap
            ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
              (r : RealNovikovSeries A) p) :
              ((descentToIsocrystal (Λ := Λ) A).obj
                ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).M))
      rw [show (cmpEquiv (Λ := Λ) P).toLinearMap
            ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
              (r : RealNovikovSeries A) p) :
              ((descentToIsocrystal (Λ := Λ) A).obj
                ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).M) =
          ((r : RealNovikovSeries A) ⊗ₜ[A] p :
            ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj P).M) by
        simp [cmpEquiv]]
      dsimp [NovikovIsocrystal.vectToNovIsoc]
      erw [LinearMap.baseChange_tmul]
      change ((@TensorProduct.tmul A _ (RealNovikovSeries A) Q.M _ _
          Novikov.novikovAlgebra.toModule _ (r : RealNovikovSeries A) (f.toFun p)) :
          ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj Q).M) =
        (cmpEquiv (Λ := Λ) Q).toLinearMap
          (((descentToIsocrystal (Λ := Λ) A).map
            ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).map f)).toLinearMap
            ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
              (r : RealNovikovSeries A) p) :
              ((descentToIsocrystal (Λ := Λ) A).obj
                ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).M))
      rw [show (((descentToIsocrystal (Λ := Λ) A).map
            ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).map f)).toLinearMap
            ((@TensorProduct.tmul A _ (RealNovikovSeries A) P.M _ _ cmpMod _
              (r : RealNovikovSeries A) p) :
              ((descentToIsocrystal (Λ := Λ) A).obj
                ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj P)).M)) =
          ((@TensorProduct.tmul A _ (RealNovikovSeries A) Q.M _ _ cmpMod _
              (r : RealNovikovSeries A) (f.toFun p)) :
              ((descentToIsocrystal (Λ := Λ) A).obj
                ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj Q)).M) by
        dsimp [descentToIsocrystal, descentToIsocrystalMap, vectToNovikovDescent,
          constantDescentDatumFunctor]
        let E := novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A
        letI : Algebra A E.R₁ := E.π₀.toAlgebra
        exact LinearMap.baseChange_tmul (A := E.R₁) f r p]
      rw [show (cmpEquiv (Λ := Λ) Q).toLinearMap
            ((@TensorProduct.tmul A _ (RealNovikovSeries A) Q.M _ _ cmpMod _
              (r : RealNovikovSeries A) (f.toFun p)) :
              ((descentToIsocrystal (Λ := Λ) A).obj
                ((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A).obj Q)).M) =
          ((@TensorProduct.tmul A _ (RealNovikovSeries A) Q.M _ _
            Novikov.novikovAlgebra.toModule _ (r : RealNovikovSeries A) (f.toFun p)) :
            ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).obj Q).M) by
        simp [cmpEquiv]]
  | add x y hx hy =>
      let eP := cmpEquiv (Λ := Λ) P
      let eQ := cmpEquiv (Λ := Λ) Q
      change ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A)).map f).toLinearMap
          (eP.toLinearMap (x + y)) =
        eQ.toLinearMap
          ((((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A) ⋙
            (descentToIsocrystal (Λ := Λ) A)).map f).toLinearMap (x + y))
      erw [eP.toLinearMap.map_add]
      rw [map_add]
      rw [show ((((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A) ⋙
            (descentToIsocrystal (Λ := Λ) A)).map f).toLinearMap (x + y)) =
          ((((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A) ⋙
            (descentToIsocrystal (Λ := Λ) A)).map f).toLinearMap x) +
          ((((vectToNovikovDescent (⊤ : AddSubgroup ℝ) A) ⋙
            (descentToIsocrystal (Λ := Λ) A)).map f).toLinearMap y) from
        map_add _ x y]
      erw [eQ.toLinearMap.map_add]
      rw [hx, hy]

noncomputable def descentToIsocrystal_comp_vectToNovikovDescent_iso :
    (vectToNovikovDescent (⊤ : AddSubgroup ℝ) A) ⋙
        (descentToIsocrystal (Λ := Λ) A) ≅
      NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := A) :=
  NatIso.ofComponents
    (fun P => descentToIsocrystal_vectToNovikovDescent_obj_iso (Λ := Λ) P)
    (by
      intro P Q f
      exact (descentToIsocrystal_vectToNovikovDescent_obj_iso_naturality
        (Λ := Λ) P Q f).symm)

end Novikov.Descent
