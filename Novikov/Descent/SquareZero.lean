import Novikov.Descent.Abstract.Transport
import Novikov.Descent.Basic
import Novikov.Descent.CoefficientMap
import Novikov.Descent.Normalization
import Novikov.Miscellany.BaseChange
import Novikov.Miscellany.SquareZero
import Novikov.Series.Module
import Novikov.Series.SquareZero
import Mathlib.Algebra.Algebra.Equiv

/-!
# Square-zero deformations of Novikov descent data

This file develops the additive Čech calculation and the deformation
infrastructure used to lift constant Novikov descent data across square-zero
extensions.
-/

namespace Novikov.Descent

open Novikov Novikov.Miscellany TensorProduct

variable {H K : Type*} [AddCommGroup H] [AddCommGroup K]

/-- Restrict a two-variable real-exponent Novikov series to the first coordinate
axis. -/
def firstAxis
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) H) :
    NovikovSeries (⊤ : AddSubgroup ℝ) Unit H := by
  let yFun : (Unit → ↥(⊤ : AddSubgroup ℝ)) → H :=
    fun d => x.val (fun i : Fin 2 => if i = 0 then d () else 0)
  have hy : isNovikovSeries yFun := by
    intro s hs C
    let s₂ : Fin 2 → ℝ := fun i => if i = 0 then s () else 1
    have hs₂ : ∀ i, 0 < s₂ i := by
      intro i
      by_cases hi : i = 0
      · simp [s₂, hi, hs ()]
      · simp [s₂, hi]
    let emb : (Unit → ↥(⊤ : AddSubgroup ℝ)) →
        (Fin 2 → ↥(⊤ : AddSubgroup ℝ)) :=
      fun d i => if i = 0 then d () else 0
    have hemb_inj : Function.Injective emb := by
      intro d₁ d₂ hEmb
      funext u
      have h0 := congr_fun hEmb 0
      simpa [emb] using h0
    have hfin := Set.Finite.preimage (fun _ _ _ _ hEmb => hemb_inj hEmb)
      (x.prop s₂ hs₂ C)
    refine hfin.subset ?_
    intro d hd
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    simp only [Set.mem_setOf_eq] at hd
    refine ⟨hd.1, ?_⟩
    have hsum : ∑ i, s₂ i * (emb d i : ℝ) = ∑ i, s i * (d i : ℝ) := by
      simp [s₂, emb, Fin.sum_univ_two]
    rw [hsum]
    exact hd.2
  exact ⟨yFun, hy⟩

@[simp]
lemma firstAxis_apply
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) H)
    (d : Unit → ↥(⊤ : AddSubgroup ℝ)) :
    (firstAxis x).val d =
      x.val (fun i : Fin 2 => if i = 0 then d () else 0) := rfl

/-- Restriction to the first axis commutes with additive maps on coefficients. -/
lemma firstAxis_map (f : H →+ K)
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) H) :
    firstAxis (Novikov.map f x) = Novikov.map f (firstAxis x) := by
  ext d
  simp only [firstAxis_apply, Novikov.map_apply]

private lemma substitute_π₁_apply
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) Unit H)
    (d : Fin 2 → ↥(⊤ : AddSubgroup ℝ)) :
    (substitute (fun _ : Unit => (0 : Fin 2)) x).val d =
      if d 1 = 0 then x.val (fun _ : Unit => d 0) else 0 := by
  rw [substitute_const_apply]
  have hcond : (∀ j : Fin 2, j ≠ 0 → d j = 0) ↔ d 1 = 0 := by
    constructor
    · intro h
      exact h 1 (by decide)
    · intro h j hj
      fin_cases j
      · exact (hj rfl).elim
      · exact h
  simp only [hcond]

private lemma substitute_π₂_apply
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) Unit H)
    (d : Fin 2 → ↥(⊤ : AddSubgroup ℝ)) :
    (substitute (fun _ : Unit => (1 : Fin 2)) x).val d =
      if d 0 = 0 then x.val (fun _ : Unit => d 1) else 0 := by
  rw [substitute_const_apply]
  have hcond : (∀ j : Fin 2, j ≠ 1 → d j = 0) ↔ d 0 = 0 := by
    constructor
    · intro h
      exact h 0 (by decide)
    · intro h j hj
      fin_cases j
      · exact h
      · exact (hj rfl).elim
  simp only [hcond]

private lemma substitute_π₁₂_apply
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) H)
    (d : Fin 3 → ↥(⊤ : AddSubgroup ℝ)) :
    (substitute Fin.castSucc x).val d =
      if d 2 = 0 then x.val (fun i : Fin 2 => d (Fin.castSucc i)) else 0 := by
  rw [substitute_apply_singleton_compl (Fin.castSucc_injective 2) 2 (by decide) x d]

private lemma substitute_π₁₃_apply
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) H)
    (d : Fin 3 → ↥(⊤ : AddSubgroup ℝ)) :
    (substitute (Fin.succAbove 1) x).val d =
      if d 1 = 0 then x.val (fun i : Fin 2 => if i = 0 then d 0 else d 2) else 0 := by
  rw [substitute_apply_singleton_compl Fin.succAbove_right_injective 1 (by decide) x d,
    show (fun i : Fin 2 => d (Fin.succAbove 1 i)) =
      (fun i : Fin 2 => if i = 0 then d 0 else d 2) by ext i; fin_cases i <;> rfl]

private lemma substitute_π₂₃_apply
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) H)
    (d : Fin 3 → ↥(⊤ : AddSubgroup ℝ)) :
    (substitute Fin.succ x).val d =
      if d 0 = 0 then x.val (fun i : Fin 2 => if i = 0 then d 1 else d 2) else 0 := by
  rw [substitute_apply_singleton_compl (fun _ _ h => Fin.succ_injective _ h) 0 (by decide) x d,
    show (fun i : Fin 2 => d (Fin.succ i)) =
      (fun i : Fin 2 => if i = 0 then d 1 else d 2) by ext i; fin_cases i <;> rfl]

/-- Every additive Čech one-cocycle for the real Novikov cover is a
coboundary. -/
theorem additive_cocycle_eq_coboundary
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) H)
    (hx : substitute (Fin.succAbove 1) x =
      substitute Fin.succ x + substitute Fin.castSucc x) :
    x =
      substitute (fun _ : Unit => (0 : Fin 2)) (firstAxis x) -
        substitute (fun _ : Unit => (1 : Fin 2)) (firstAxis x) := by
  have hcoeff (d₃ : Fin 3 → ↥(⊤ : AddSubgroup ℝ)) :
      (substitute (Fin.succAbove 1) x).val d₃ =
        (substitute Fin.succ x).val d₃ + (substitute Fin.castSucc x).val d₃ := by
    have h := congrArg (fun y => y.val d₃) hx
    exact h
  have h_off_axis (a b : ↥(⊤ : AddSubgroup ℝ)) (ha : a ≠ 0) (hb : b ≠ 0) :
      x.val (fun i : Fin 2 => if i = 0 then a else b) = 0 := by
    let d₃ : Fin 3 → ↥(⊤ : AddSubgroup ℝ) :=
      fun i => if i = 0 then a else if i = 1 then 0 else b
    have h := hcoeff d₃
    rw [substitute_π₁₃_apply, substitute_π₂₃_apply, substitute_π₁₂_apply] at h
    simpa [d₃, ha, hb] using h
  have h_origin : x.val (0 : Fin 2 → ↥(⊤ : AddSubgroup ℝ)) = 0 := by
    let d₃ : Fin 3 → ↥(⊤ : AddSubgroup ℝ) := 0
    have h := hcoeff d₃
    rw [substitute_π₁₃_apply, substitute_π₂₃_apply, substitute_π₁₂_apply] at h
    have h' : x.val (0 : Fin 2 → ↥(⊤ : AddSubgroup ℝ)) =
        x.val 0 + x.val 0 := by
      simpa [d₃] using h
    apply add_left_cancel (a := x.val (0 : Fin 2 → ↥(⊤ : AddSubgroup ℝ)))
    simpa using h'.symm
  have h_axes (d : ↥(⊤ : AddSubgroup ℝ)) (hd : d ≠ 0) :
      x.val (fun i : Fin 2 => if i = 0 then 0 else d) =
        -x.val (fun i : Fin 2 => if i = 0 then d else 0) := by
    let d₃ : Fin 3 → ↥(⊤ : AddSubgroup ℝ) :=
      fun i => if i = 0 then 0 else if i = 1 then d else 0
    have h := hcoeff d₃
    rw [substitute_π₁₃_apply, substitute_π₂₃_apply, substitute_π₁₂_apply] at h
    have hcast :
        (fun i : Fin 2 =>
          if i = 0 then 0 else if (Fin.castSucc i : Fin 3) = 1 then d else 0) =
          (fun i : Fin 2 => if i = 0 then 0 else d) := by
      ext i
      fin_cases i <;> simp
    have h' : 0 =
        x.val (fun i : Fin 2 => if i = 0 then d else 0) +
          x.val (fun i : Fin 2 => if i = 0 then 0 else d) := by
      simpa [d₃, hd, hcast] using h
    exact eq_neg_of_add_eq_zero_right h'.symm
  ext e
  change x.val e =
    (substitute (fun _ : Unit => (0 : Fin 2)) (firstAxis x)).val e -
      (substitute (fun _ : Unit => (1 : Fin 2)) (firstAxis x)).val e
  rw [substitute_π₁_apply, substitute_π₂_apply]
  simp only [firstAxis_apply]
  by_cases he0 : e 0 = 0
  · by_cases he1 : e 1 = 0
    · rw [if_pos he1, if_pos he0]
      have he : e = 0 := by
        funext i
        fin_cases i
        · exact he0
        · exact he1
      rw [he, h_origin]
      simp
    · rw [if_neg he1, if_pos he0, zero_sub]
      have he : e = (fun i : Fin 2 => if i = 0 then 0 else e 1) := by
        funext i
        fin_cases i
        · exact he0
        · simp
      rw [he]
      exact h_axes (e 1) he1
  · by_cases he1 : e 1 = 0
    · rw [if_pos he1, if_neg he0, sub_zero]
      have he : e = (fun i : Fin 2 => if i = 0 then e 0 else 0) := by
        funext i
        fin_cases i
        · simp
        · exact he1
      rw [he]
      simp
    · rw [if_neg he1, if_neg he0, sub_zero]
      have he : e = (fun i : Fin 2 => if i = 0 then e 0 else e 1) := by
        funext i
        fin_cases i <;> simp
      rw [he]
      exact h_off_axis (e 0) (e 1) he0 he1

private lemma novikov_smul_monomial_eq_map
    {T : Type*} [SetLike T ℝ] [AddSubmonoidClass T ℝ] {Γ : T}
    {ι C M : Type*} [Fintype ι] [CommRing C]
    [AddCommGroup M] [Module C M]
    (x : NovikovSeries Γ ι C) (m : M) :
    x • novikovMonomial m 0 =
      Novikov.map
        ({ toFun := fun c : C => c • m
           map_zero' := zero_smul C m
           map_add' := fun c d => add_smul c d m } : C →+ M) x := by
  ext d
  rw [Novikov.map_apply]
  change (novikovSeriesMul x (novikovMonomial m 0) smulAddHom).val d = _
  have h := novikovSeriesMul_right_monomial x m smulAddHom 0 d
  simpa only [add_zero, smulAddHom, _root_.smulAddHom_apply] using h

variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
variable [Algebra A R] [Algebra A S]

/-- Extend the ring factor of a tensor product along an algebra homomorphism. -/
def algebraTensorMap (f : R →ₐ[A] S)
    (M : Type*) [AddCommGroup M] [Module A M] :
    (R ⊗[A] M) →ₗ[A] (S ⊗[A] M) :=
  TensorProduct.map f.toLinearMap LinearMap.id

@[simp]
lemma algebraTensorMap_tmul (f : R →ₐ[A] S)
    (M : Type*) [AddCommGroup M] [Module A M] (r : R) (m : M) :
    algebraTensorMap f M (r ⊗ₜ[A] m) = f r ⊗ₜ[A] m := by
  simp [algebraTensorMap]

/-- The Novikov module base-change equivalence intertwines extension of the
ring factor with substitution of variables. -/
theorem novikovModule_base_change_equiv_substitute
    {T : Type*} [SetLike T ℝ] [AddSubmonoidClass T ℝ] {Γ : T}
    {ι ι' C M : Type*} [Fintype ι] [Fintype ι'] [CommRing C]
    [AddCommGroup M] [Module C M] [Module.FinitePresentation C M]
    (φ : ι → ι') (x : NovikovSeries Γ ι C ⊗[C] M) :
    novikovModule_base_change_equiv (Γ := Γ) (ι := ι')
        (algebraTensorMap (substituteAlgHom φ) M x) =
      substitute φ (novikovModule_base_change_equiv (Γ := Γ) (ι := ι) x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero]
      exact (substitute_zero φ).symm
  | add x y hx hy =>
      simp only [map_add, hx, hy]
      exact (substitute_add φ _ _).symm
  | tmul r m =>
      simp only [algebraTensorMap_tmul]
      change novikovBaseChangeMap Γ (substitute φ r ⊗ₜ[C] m) =
        substitute φ (novikovBaseChangeMap Γ (r ⊗ₜ[C] m))
      rw [novikovBaseChangeMap_tmul, novikovBaseChangeMap_tmul]
      rw [novikov_smul_monomial_eq_map,
        novikov_smul_monomial_eq_map]
      exact map_substitute _ φ r

/-- The tensor-Hom base-change equivalence intertwines extension of the ring
factor with normalized endomorphism base change. -/
theorem homBaseChangeEquiv_normalizedEndBaseChange
    (f : R →ₐ[A] S) (P : FiniteProjectiveModule A)
    (x : R ⊗[A] Module.End A P.M) :
    homBaseChangeEquiv (R := A) (M := P.M) (N := P.M) S
        (algebraTensorMap f (Module.End A P.M) x) =
      normalizedEndBaseChange f P
        (homBaseChangeEquiv (R := A) (M := P.M) (N := P.M) R x) := by
  letI : Algebra R S := f.toRingHom.toAlgebra
  letI : IsScalarTower A R S :=
    IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r u =>
      simp only [algebraTensorMap_tmul, homBaseChangeEquiv_tmul]
      rw [normalizedEndBaseChange]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
      apply LinearMap.ext
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w₁ w₂ hw₁ hw₂ => simp only [map_add, hw₁, hw₂]
      | tmul s z =>
          change (f r • LinearMap.baseChange S u) (s ⊗ₜ[A] z) =
            ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S P.M).conjRingEquiv
              (LinearMap.baseChange S (r • LinearMap.baseChange R u))) (s ⊗ₜ[A] z)
          rw [LinearEquiv.conjRingEquiv_apply_apply]
          rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
          change f r • (s ⊗ₜ[A] u z) =
            (TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S P.M)
              (LinearMap.baseChange S (r • LinearMap.baseChange R u)
                (s ⊗ₜ[R] (1 ⊗ₜ[A] z)))
          rw [LinearMap.baseChange_tmul, LinearMap.smul_apply,
            LinearMap.baseChange_tmul]
          simp only [TensorProduct.smul_tmul']
          rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
          simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
            RingHom.id_apply, AlgHom.toRingHom_eq_coe, mul_one]
          rfl

/-- The canonical comparison between the two iterated tensor presentations
arising from coefficient base change. -/
noncomputable def coefficientModuleBaseChangeEquiv
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C) :
    let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι C
    let S := NovikovSeries (⊤ : AddSubgroup ℝ) ι D
    letI : Algebra R S :=
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) q).toAlgebra
    S ⊗[R] (R ⊗[C] P.M) ≃ₗ[S] S ⊗[D] (P.baseChange q).M := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι C
  let S := NovikovSeries (⊤ : AddSubgroup ℝ) ι D
  let qR := mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) q
  let cRAlg : Algebra C R := inferInstance
  let dSAlg : Algebra D S := inferInstance
  letI : Algebra C D := q.toAlgebra
  letI : Algebra C R := cRAlg
  letI : SMul C R := cRAlg.toSMul
  letI : Module C R := cRAlg.toModule
  letI : Algebra D S := dSAlg
  letI : SMul D S := dSAlg.toSMul
  letI : Module D S := dSAlg.toModule
  let rSAlg : Algebra R S := qR.toAlgebra
  letI : Algebra R S := rSAlg
  letI : SMul R S := rSAlg.toSMul
  letI : Module R S := rSAlg.toModule
  let cSAlg : Algebra C S := ((algebraMap D S).comp q).toAlgebra
  letI : Algebra C S := cSAlg
  letI : SMul C S := cSAlg.toSMul
  letI : Module C S := cSAlg.toModule
  letI : IsScalarTower C D S :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower C R S :=
    IsScalarTower.of_algebraMap_eq (fun c => by
      change (algebraMap D S) (q c) = qR ((algebraMap C R) c)
      exact (RingHom.congr_fun (Novikov.mapRingHom_comp_algebraMapNovikov q) c).symm)
  let eL : S ⊗[R] (R ⊗[C] P.M) ≃ₗ[S] S ⊗[C] P.M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange C R S S P.M
  let eR : S ⊗[D] (D ⊗[C] P.M) ≃ₗ[S] S ⊗[C] P.M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange C D S S P.M
  exact eL.trans eR.symm

private noncomputable def novikovMapSemilinear
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) :
    NovikovSeries (⊤ : AddSubgroup ℝ) ι C →ₛₗ[q]
      NovikovSeries (⊤ : AddSubgroup ℝ) ι D where
  toFun := mapRingHom q
  map_add' x y := by
    ext d
    simp only [mapRingHom_apply, map_add, AddSubgroup.coe_add, Pi.add_apply]
  map_smul' c x := by
    ext d
    simp only [mapRingHom_apply]
    change q (c * x.val d) = q c * q (x.val d)
    exact map_mul q c (x.val d)

/-- Base change of coefficient-linear endomorphisms as a semilinear map. -/
noncomputable def endBaseChangeSemilinear
    {C D : Type*} [CommRing C] [CommRing D]
    (q : C →+* D) (P : FiniteProjectiveModule C) :
    Module.End C P.M →ₛₗ[q] Module.End D (P.baseChange q).M := by
  letI : Algebra C D := q.toAlgebra
  exact
    { toFun := fun u => LinearMap.baseChange D u
      map_add' := LinearMap.baseChange_add
      map_smul' := fun c u => by
        rw [LinearMap.baseChange_smul]
        apply LinearMap.ext
        intro z
        change q c • LinearMap.baseChange D u z =
          q c • LinearMap.baseChange D u z
        rfl }

/-- Apply coefficient base change simultaneously to a Novikov-series factor and
an endomorphism factor. -/
noncomputable def coefficientTensorMap
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C) :
    (NovikovSeries (⊤ : AddSubgroup ℝ) ι C ⊗[C] Module.End C P.M) →ₛₗ[q]
      (NovikovSeries (⊤ : AddSubgroup ℝ) ι D ⊗[D]
        Module.End D (P.baseChange q).M) :=
  TensorProduct.map (novikovMapSemilinear q)
    (endBaseChangeSemilinear q P)

@[simp]
lemma coefficientTensorMap_tmul
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (r : NovikovSeries (⊤ : AddSubgroup ℝ) ι C) (u : Module.End C P.M) :
    coefficientTensorMap q P (r ⊗ₜ[C] u) =
      mapRingHom q r ⊗ₜ[D] endBaseChangeSemilinear q P u := by
  simp [coefficientTensorMap, novikovMapSemilinear,
    endBaseChangeSemilinear]

/-- Coefficient base change for normalized endomorphisms, expressed in the
coefficient-normalized tensor presentation. -/
noncomputable def coefficientEndBaseChange
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C) :
    let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι C
    let S := NovikovSeries (⊤ : AddSubgroup ℝ) ι D
    letI : Algebra R S :=
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) q).toAlgebra
    Module.End R (R ⊗[C] P.M) →+*
      Module.End S (S ⊗[D] (P.baseChange q).M) := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι C
  let S := NovikovSeries (⊤ : AddSubgroup ℝ) ι D
  let qR := mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) q
  letI : Algebra R S := qR.toAlgebra
  let e : S ⊗[R] (R ⊗[C] P.M) ≃ₗ[S] S ⊗[D] (P.baseChange q).M :=
    coefficientModuleBaseChangeEquiv q P
  exact e.conjRingEquiv.toRingHom.comp
    (Module.End.baseChangeHom R S (R ⊗[C] P.M)).toRingHom

private noncomputable def coefficientSourceElem
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (s : NovikovSeries (⊤ : AddSubgroup ℝ) ι D)
    (r : NovikovSeries (⊤ : AddSubgroup ℝ) ι C) (p : P.M) :
    let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι C
    let S := NovikovSeries (⊤ : AddSubgroup ℝ) ι D
    letI : Algebra R S :=
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) q).toAlgebra
    S ⊗[R] (R ⊗[C] P.M) := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι C
  let S := NovikovSeries (⊤ : AddSubgroup ℝ) ι D
  letI : Algebra R S :=
    (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) q).toAlgebra
  exact s ⊗ₜ[R] (r ⊗ₜ[C] p)

private noncomputable def baseChangeElem
    {C D : Type*} [CommRing C] [CommRing D]
    (q : C →+* D) (P : FiniteProjectiveModule C) (d : D) (p : P.M) :
    (P.baseChange q).M := by
  letI : Algebra C D := q.toAlgebra
  exact d ⊗ₜ[C] p

@[simp]
private lemma endBaseChangeSemilinear_baseChangeElem
    {C D : Type*} [CommRing C] [CommRing D]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (u : Module.End C P.M) (d : D) (p : P.M) :
    endBaseChangeSemilinear q P u (baseChangeElem q P d p) =
      baseChangeElem q P d (u p) := by
  dsimp [endBaseChangeSemilinear, baseChangeElem]
  rfl

private noncomputable def coefficientTargetElem
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (s : NovikovSeries (⊤ : AddSubgroup ℝ) ι D) (d : D) (p : P.M) :
    NovikovSeries (⊤ : AddSubgroup ℝ) ι D ⊗[D] (P.baseChange q).M := by
  exact s ⊗ₜ[D] baseChangeElem q P d p

private lemma coefficientModuleBaseChangeEquiv_sourceElem
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (s : NovikovSeries (⊤ : AddSubgroup ℝ) ι D)
    (r : NovikovSeries (⊤ : AddSubgroup ℝ) ι C) (p : P.M) :
    coefficientModuleBaseChangeEquiv q P
        (coefficientSourceElem q P s r p) =
      coefficientTargetElem q P (mapRingHom q r * s) 1 p := by
  letI : Algebra C D := q.toAlgebra
  dsimp [coefficientModuleBaseChangeEquiv, coefficientSourceElem,
    coefficientTargetElem]
  change ((mapRingHom q) r * s) ⊗ₜ[D] ((1 : D) ⊗ₜ[C] p) =
    ((mapRingHom q) r * s) ⊗ₜ[D] ((1 : D) ⊗ₜ[C] p)
  rfl

private lemma coefficientTargetElem_normalize
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (s : NovikovSeries (⊤ : AddSubgroup ℝ) ι D) (d : D) (p : P.M) :
    coefficientTargetElem q P s d p =
      coefficientTargetElem q P ((algebraMap D _ d) * s) 1 p := by
  letI : Algebra C D := q.toAlgebra
  dsimp [coefficientTargetElem]
  have hinner : d ⊗ₜ[C] p = d • ((1 : D) ⊗ₜ[C] p) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  calc
    s ⊗ₜ[D] (d ⊗ₜ[C] p) =
        s ⊗ₜ[D] (d • ((1 : D) ⊗ₜ[C] p)) :=
      congrArg (fun z : D ⊗[C] P.M => s ⊗ₜ[D] z) hinner
    _ = (d • s) ⊗ₜ[D] ((1 : D) ⊗ₜ[C] p) :=
      TensorProduct.tmul_smul d s ((1 : D) ⊗ₜ[C] p)
    _ = ((algebraMap D _ d) * s) ⊗ₜ[D] ((1 : D) ⊗ₜ[C] p) := by
      rw [Algebra.smul_def]

private lemma coefficientModuleBaseChangeEquiv_symm_targetElem
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (s : NovikovSeries (⊤ : AddSubgroup ℝ) ι D) (d : D) (p : P.M) :
    (coefficientModuleBaseChangeEquiv q P).symm
        (coefficientTargetElem q P s d p) =
      coefficientSourceElem q P ((algebraMap D _ d) * s) 1 p := by
  letI : Algebra C D := q.toAlgebra
  apply (coefficientModuleBaseChangeEquiv q P).injective
  rw [LinearEquiv.apply_symm_apply]
  rw [coefficientModuleBaseChangeEquiv_sourceElem]
  simp only [map_one, one_mul]
  exact coefficientTargetElem_normalize q P s d p

private lemma coefficientSourceElem_baseChange_apply
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (s : NovikovSeries (⊤ : AddSubgroup ℝ) ι D)
    (r a : NovikovSeries (⊤ : AddSubgroup ℝ) ι C)
    (u : Module.End C P.M) (p : P.M) :
    let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι C
    let S := NovikovSeries (⊤ : AddSubgroup ℝ) ι D
    letI : Algebra R S :=
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) q).toAlgebra
    LinearMap.baseChange S (r • LinearMap.baseChange R u)
        (coefficientSourceElem q P s a p) =
      coefficientSourceElem q P s (r * a) (u p) := by
  dsimp [coefficientSourceElem]
  simp only [TensorProduct.smul_tmul', Algebra.smul_def,
    RingHom.algebraMap_toAlgebra, RingHom.id_apply]

private lemma coefficientTargetElem_baseChange_apply
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (c s : NovikovSeries (⊤ : AddSubgroup ℝ) ι D)
    (d : D) (u : Module.End C P.M) (p : P.M) :
    (c • LinearMap.baseChange (NovikovSeries (⊤ : AddSubgroup ℝ) ι D)
        (endBaseChangeSemilinear q P u))
        (coefficientTargetElem q P s d p) =
      coefficientTargetElem q P (c * s) d (u p) := by
  dsimp [coefficientTargetElem]
  simp only [endBaseChangeSemilinear_baseChangeElem,
    TensorProduct.smul_tmul', Algebra.smul_def,
    RingHom.algebraMap_toAlgebra, RingHom.id_apply]

/-- The tensor-Hom base-change equivalence commutes with coefficient base
change. -/
theorem homBaseChangeEquiv_coefficient_naturality
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) ι C ⊗[C] Module.End C P.M) :
    homBaseChangeEquiv (R := D) (M := (P.baseChange q).M)
        (N := (P.baseChange q).M)
        (NovikovSeries (⊤ : AddSubgroup ℝ) ι D)
        (coefficientTensorMap q P x) =
      coefficientEndBaseChange (ι := ι) q P
        (homBaseChangeEquiv (R := C) (M := P.M) (N := P.M)
          (NovikovSeries (⊤ : AddSubgroup ℝ) ι C) x) := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι C
  let S := NovikovSeries (⊤ : AddSubgroup ℝ) ι D
  let qR := mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) q
  letI : Algebra C D := q.toAlgebra
  letI : Algebra R S := qR.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r u =>
      simp only [coefficientTensorMap_tmul, homBaseChangeEquiv_tmul]
      rw [coefficientEndBaseChange]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
      ext z
      induction z using TensorProduct.induction_on with
      | zero =>
          exact (map_zero _).trans (map_zero _).symm
      | add z₁ z₂ hz₁ hz₂ =>
          calc
            _ = _ + _ := map_add _ z₁ z₂
            _ = _ + _ := congrArg₂ (· + ·) hz₁ hz₂
            _ = _ := (map_add _ z₁ z₂).symm
      | tmul d p =>
          change (qR r • LinearMap.baseChange S
                (endBaseChangeSemilinear q P u))
              (coefficientTargetElem q P 1 d p) =
            ((coefficientModuleBaseChangeEquiv q P).conjRingEquiv
              (LinearMap.baseChange S (r • LinearMap.baseChange R u)))
                (coefficientTargetElem q P 1 d p)
          rw [coefficientTargetElem_baseChange_apply]
          rw [LinearEquiv.conjRingEquiv_apply_apply]
          rw [coefficientModuleBaseChangeEquiv_symm_targetElem]
          rw [coefficientSourceElem_baseChange_apply]
          rw [coefficientModuleBaseChangeEquiv_sourceElem]
          rw [coefficientTargetElem_normalize]
          simp only [mul_one]
          congr 1
          ring

/-- The Novikov module base-change equivalence commutes with coefficient base
change on endomorphism coefficients. -/
theorem novikovModule_base_change_equiv_coefficient_naturality
    {C D ι : Type*} [CommRing C] [CommRing D] [Fintype ι]
    (q : C →+* D) (P : FiniteProjectiveModule C)
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) ι C ⊗[C] Module.End C P.M) :
    letI : Module.FinitePresentation C (Module.End C P.M) :=
      Module.finitePresentation_of_projective C (Module.End C P.M)
    letI : Module.FinitePresentation D (Module.End D (P.baseChange q).M) :=
      Module.finitePresentation_of_projective D (Module.End D (P.baseChange q).M)
    novikovModule_base_change_equiv
        (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) (A := D)
        (M := Module.End D (P.baseChange q).M)
        (coefficientTensorMap q P x) =
      Novikov.map (endBaseChangeSemilinear q P).toAddMonoidHom
        (novikovModule_base_change_equiv
          (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) (A := C)
          (M := Module.End C P.M) x) := by
  let E := Module.End C P.M
  let F := Module.End D (P.baseChange q).M
  letI : Module.FinitePresentation C E :=
    Module.finitePresentation_of_projective C E
  letI : Module.FinitePresentation D F :=
    Module.finitePresentation_of_projective D F
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r u =>
      simp only [coefficientTensorMap_tmul]
      change novikovBaseChangeMap (⊤ : AddSubgroup ℝ)
          (mapRingHom q r ⊗ₜ[D] endBaseChangeSemilinear q P u) =
        Novikov.map (endBaseChangeSemilinear q P).toAddMonoidHom
          (novikovBaseChangeMap (⊤ : AddSubgroup ℝ) (r ⊗ₜ[C] u))
      rw [novikovBaseChangeMap_tmul, novikovBaseChangeMap_tmul]
      rw [novikov_smul_monomial_eq_map,
        novikov_smul_monomial_eq_map]
      ext d p
      simp only [Novikov.map_apply, mapRingHom_apply]
      exact congrArg (fun v : Module.End D (P.baseChange q).M => v p)
        ((endBaseChangeSemilinear q P).map_smul' (r.val d) u).symm

/-- Coefficient base change of tensor representatives commutes with substitution
of variables. -/
theorem coefficientTensorMap_algebraTensorMap
    {C D ι κ : Type*} [CommRing C] [CommRing D] [Fintype ι] [Fintype κ]
    (q : C →+* D) (P : FiniteProjectiveModule C) (f : ι → κ)
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) ι C ⊗[C] Module.End C P.M) :
    coefficientTensorMap q P
        (algebraTensorMap (substituteAlgHom f) (Module.End C P.M) x) =
      algebraTensorMap (substituteAlgHom f)
        (Module.End D (P.baseChange q).M) (coefficientTensorMap q P x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r u =>
      simp only [algebraTensorMap_tmul, coefficientTensorMap_tmul]
      change mapRingHom q (substitute f r) ⊗ₜ[D] _ =
        substitute f (mapRingHom q r) ⊗ₜ[D] _
      rw [mapRingHom_substitute]

/-- Normalized endomorphism pullback along a substitution commutes with
coefficient base change. -/
theorem normalizedEndBaseChange_coefficient_naturality
    {C D ι κ : Type*} [CommRing C] [CommRing D] [Fintype ι] [Fintype κ]
    (q : C →+* D) (P : FiniteProjectiveModule C) (f : ι → κ)
    (δ : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) ι C)
      (NovikovSeries (⊤ : AddSubgroup ℝ) ι C ⊗[C] P.M)) :
    coefficientEndBaseChange (ι := κ) q P
        (normalizedEndBaseChange (substituteAlgHom f) P δ) =
      normalizedEndBaseChange (substituteAlgHom f) (P.baseChange q)
        (coefficientEndBaseChange (ι := ι) q P δ) := by
  let R := NovikovSeries (⊤ : AddSubgroup ℝ) ι C
  let x := (homBaseChangeEquiv (R := C) (M := P.M) (N := P.M) R).symm δ
  have hx : homBaseChangeEquiv (R := C) (M := P.M) (N := P.M) R x = δ :=
    LinearEquiv.apply_symm_apply _ δ
  rw [← hx]
  rw [← homBaseChangeEquiv_normalizedEndBaseChange]
  rw [← homBaseChangeEquiv_coefficient_naturality]
  rw [coefficientTensorMap_algebraTensorMap]
  rw [homBaseChangeEquiv_normalizedEndBaseChange]
  rw [homBaseChangeEquiv_coefficient_naturality]

/-- Coefficient base change on normalized level-one endomorphisms. -/
noncomputable def q₁End {C D : Type*} [CommRing C] [CommRing D]
    (q : C →+* D) (P : FiniteProjectiveModule C) :
    Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit C ⊗[C] P.M) →+*
      Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit D)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit D ⊗[D] (P.baseChange q).M) :=
  coefficientEndBaseChange (ι := Unit) q P

/-- Coefficient base change on normalized level-two endomorphisms. -/
noncomputable def q₂End {C D : Type*} [CommRing C] [CommRing D]
    (q : C →+* D) (P : FiniteProjectiveModule C) :
    Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C ⊗[C] P.M) →+*
      Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) D)
        (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) D ⊗[D] (P.baseChange q).M) :=
  coefficientEndBaseChange (ι := Fin 2) q P

/-- Coefficient base change on normalized level-three endomorphisms. -/
noncomputable def q₃End {C D : Type*} [CommRing C] [CommRing D]
    (q : C →+* D) (P : FiniteProjectiveModule C) :
    Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) C ⊗[C] P.M) →+*
      Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) D)
        (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) D ⊗[D] (P.baseChange q).M) :=
  coefficientEndBaseChange (ι := Fin 3) q P

private lemma end_cocycle_to_series {C : Type*} [CommRing C]
    (P : FiniteProjectiveModule C)
    (δ : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C ⊗[C] P.M))
    (hδ : π₁₃End P δ = π₂₃End P δ + π₁₂End P δ) :
    let E := Module.End C P.M
    letI : Module.FinitePresentation C E :=
      Module.finitePresentation_of_projective C E
    let H₂ := homBaseChangeEquiv (R := C) (M := P.M) (N := P.M)
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
    let N₂ := novikovModule_base_change_equiv
      (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) (A := C) (M := E)
    let x := N₂ (H₂.symm δ)
    substitute (Fin.succAbove 1) x =
      substitute Fin.succ x + substitute Fin.castSucc x := by
  let E := Module.End C P.M
  letI : Module.FinitePresentation C E :=
    Module.finitePresentation_of_projective C E
  let H₂ := homBaseChangeEquiv (R := C) (M := P.M) (N := P.M)
    (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
  let H₃ := homBaseChangeEquiv (R := C) (M := P.M) (N := P.M)
    (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 3) C)
  let N₂ := novikovModule_base_change_equiv
    (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) (A := C) (M := E)
  let N₃ := novikovModule_base_change_equiv
    (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 3) (A := C) (M := E)
  let t := H₂.symm δ
  let x := N₂ t
  have ht :
      algebraTensorMap (substituteAlgHom (Fin.succAbove 1)) E t =
        algebraTensorMap (substituteAlgHom Fin.succ) E t +
          algebraTensorMap (substituteAlgHom Fin.castSucc) E t := by
    apply H₃.injective
    rw [map_add]
    rw [homBaseChangeEquiv_normalizedEndBaseChange,
      homBaseChangeEquiv_normalizedEndBaseChange,
      homBaseChangeEquiv_normalizedEndBaseChange]
    change π₁₃End P (H₂ t) = π₂₃End P (H₂ t) + π₁₂End P (H₂ t)
    rw [show H₂ t = δ from H₂.apply_symm_apply δ]
    exact hδ
  have hs := congrArg N₃ ht
  rw [map_add, novikovModule_base_change_equiv_substitute,
    novikovModule_base_change_equiv_substitute,
    novikovModule_base_change_equiv_substitute] at hs
  exact hs

/-- Every normalized additive endomorphism cocycle is a normalized
endomorphism coboundary. -/
theorem exists_end_eq_sub_of_is_add_cocycle {C : Type*} [CommRing C]
    (P : FiniteProjectiveModule C)
    (δ : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C ⊗[C] P.M))
    (hδ : π₁₃End P δ = π₂₃End P δ + π₁₂End P δ) :
    ∃ η : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit C ⊗[C] P.M),
      δ = π₁End P η - π₂End P η := by
  let E := Module.End C P.M
  letI : Module.FinitePresentation C E :=
    Module.finitePresentation_of_projective C E
  let H₁ := homBaseChangeEquiv (R := C) (M := P.M) (N := P.M)
    (NovikovSeries (⊤ : AddSubgroup ℝ) Unit C)
  let H₂ := homBaseChangeEquiv (R := C) (M := P.M) (N := P.M)
    (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
  let N₁ := novikovModule_base_change_equiv
    (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (A := C) (M := E)
  let N₂ := novikovModule_base_change_equiv
    (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) (A := C) (M := E)
  let t := H₂.symm δ
  let x := N₂ t
  have hx : substitute (Fin.succAbove 1) x =
      substitute Fin.succ x + substitute Fin.castSucc x :=
    end_cocycle_to_series P δ hδ
  have hcob := additive_cocycle_eq_coboundary x hx
  let s := N₁.symm (firstAxis x)
  let η := H₁ s
  refine ⟨η, ?_⟩
  have ht : t =
      algebraTensorMap (substituteAlgHom (fun _ : Unit => (0 : Fin 2))) E s -
        algebraTensorMap (substituteAlgHom (fun _ : Unit => (1 : Fin 2))) E s := by
    apply N₂.injective
    rw [map_sub, novikovModule_base_change_equiv_substitute,
      novikovModule_base_change_equiv_substitute]
    change x =
      substitute (fun _ : Unit => (0 : Fin 2)) (N₁ s) -
        substitute (fun _ : Unit => (1 : Fin 2)) (N₁ s)
    rw [show N₁ s = firstAxis x from N₁.apply_symm_apply (firstAxis x)]
    exact hcob
  calc
    δ = H₂ t := (H₂.apply_symm_apply δ).symm
    _ = H₂
        (algebraTensorMap (substituteAlgHom (fun _ : Unit => (0 : Fin 2))) E s -
          algebraTensorMap (substituteAlgHom (fun _ : Unit => (1 : Fin 2))) E s) :=
      congrArg H₂ ht
    _ = H₂ (algebraTensorMap
          (substituteAlgHom (fun _ : Unit => (0 : Fin 2))) E s) -
        H₂ (algebraTensorMap
          (substituteAlgHom (fun _ : Unit => (1 : Fin 2))) E s) := map_sub H₂ _ _
    _ = π₁End P η - π₂End P η := by
      rw [homBaseChangeEquiv_normalizedEndBaseChange,
        homBaseChangeEquiv_normalizedEndBaseChange]
      rfl

/-- An additive endomorphism cocycle that vanishes after coefficient base
change admits a coboundary primitive that also vanishes after base change. -/
theorem exists_end_eq_sub_of_is_add_cocycle_of_map_eq_zero
    {C D : Type*} [CommRing C] [CommRing D] (q : C →+* D)
    (P : FiniteProjectiveModule C)
    (δ : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
      (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C ⊗[C] P.M))
    (hδ : π₁₃End P δ = π₂₃End P δ + π₁₂End P δ)
    (hδq : q₂End q P δ = 0) :
    ∃ η : Module.End (NovikovSeries (⊤ : AddSubgroup ℝ) Unit C)
        (NovikovSeries (⊤ : AddSubgroup ℝ) Unit C ⊗[C] P.M),
      δ = π₁End P η - π₂End P η ∧ q₁End q P η = 0 := by
  let E := Module.End C P.M
  let F := Module.End D (P.baseChange q).M
  letI : Module.FinitePresentation C E :=
    Module.finitePresentation_of_projective C E
  letI : Module.FinitePresentation D F :=
    Module.finitePresentation_of_projective D F
  let H₁ := homBaseChangeEquiv (R := C) (M := P.M) (N := P.M)
    (NovikovSeries (⊤ : AddSubgroup ℝ) Unit C)
  let H₂ := homBaseChangeEquiv (R := C) (M := P.M) (N := P.M)
    (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) C)
  let H₂D := homBaseChangeEquiv (R := D) (M := (P.baseChange q).M)
    (N := (P.baseChange q).M)
    (NovikovSeries (⊤ : AddSubgroup ℝ) (Fin 2) D)
  let N₁ := novikovModule_base_change_equiv
    (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (A := C) (M := E)
  let N₂ := novikovModule_base_change_equiv
    (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) (A := C) (M := E)
  let N₁D := novikovModule_base_change_equiv
    (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (A := D) (M := F)
  let t := H₂.symm δ
  let x := N₂ t
  have hx : substitute (Fin.succAbove 1) x =
      substitute Fin.succ x + substitute Fin.castSucc x :=
    end_cocycle_to_series P δ hδ
  have hcob := additive_cocycle_eq_coboundary x hx
  let s := N₁.symm (firstAxis x)
  let η := H₁ s
  have ht : t =
      algebraTensorMap (substituteAlgHom (fun _ : Unit => (0 : Fin 2))) E s -
        algebraTensorMap (substituteAlgHom (fun _ : Unit => (1 : Fin 2))) E s := by
    apply N₂.injective
    rw [map_sub, novikovModule_base_change_equiv_substitute,
      novikovModule_base_change_equiv_substitute]
    change x =
      substitute (fun _ : Unit => (0 : Fin 2)) (N₁ s) -
        substitute (fun _ : Unit => (1 : Fin 2)) (N₁ s)
    rw [show N₁ s = firstAxis x from N₁.apply_symm_apply (firstAxis x)]
    exact hcob
  have hη : δ = π₁End P η - π₂End P η := by
    calc
      δ = H₂ t := (H₂.apply_symm_apply δ).symm
      _ = H₂
          (algebraTensorMap
              (substituteAlgHom (fun _ : Unit => (0 : Fin 2))) E s -
            algebraTensorMap
              (substituteAlgHom (fun _ : Unit => (1 : Fin 2))) E s) :=
        congrArg H₂ ht
      _ = H₂ (algebraTensorMap
            (substituteAlgHom (fun _ : Unit => (0 : Fin 2))) E s) -
          H₂ (algebraTensorMap
            (substituteAlgHom (fun _ : Unit => (1 : Fin 2))) E s) :=
        map_sub H₂ _ _
      _ = π₁End P η - π₂End P η := by
        rw [homBaseChangeEquiv_normalizedEndBaseChange,
          homBaseChangeEquiv_normalizedEndBaseChange]
        rfl
  refine ⟨η, hη, ?_⟩
  have htq : coefficientTensorMap q P t = 0 := by
    apply H₂D.injective
    rw [homBaseChangeEquiv_coefficient_naturality]
    rw [show H₂ t = δ from H₂.apply_symm_apply δ]
    simpa only [map_zero] using hδq
  have hxq : Novikov.map (endBaseChangeSemilinear q P).toAddMonoidHom x = 0 := by
    change Novikov.map (endBaseChangeSemilinear q P).toAddMonoidHom (N₂ t) = 0
    rw [← novikovModule_base_change_equiv_coefficient_naturality]
    rw [htq, map_zero]
  have hsq : coefficientTensorMap q P s = 0 := by
    apply N₁D.injective
    rw [novikovModule_base_change_equiv_coefficient_naturality]
    rw [show N₁ s = firstAxis x from N₁.apply_symm_apply (firstAxis x)]
    rw [← firstAxis_map, hxq]
    simp only [map_zero]
    ext d
    rfl
  change coefficientEndBaseChange (ι := Unit) q P (H₁ s) = 0
  rw [← homBaseChangeEquiv_coefficient_naturality]
  rw [hsq, map_zero]

end Novikov.Descent
