import Novikov.Descent.Isocrystal

/-!
# Equalizer lemma for recovering descent data from an isocrystal

This file begins the formalization of `paper.tex`, Lemma `RecoverDDFromIsoc`.
It sets up the basic maps appearing in the two-row diagram; the equalizer
universal properties will be added in subsequent steps.
-/

open TensorProduct
open Novikov.Miscellany Novikov.Descent.Abstract

namespace Novikov.Descent

section AbstractMaps

variable (C : CosimplicialRing)

/-- Generic bottom-row inclusion `π₂^* M → ρ₃^* M`, namely
`π₂₃^* φ ∘ π₁₂^*`.  Keeping this generic avoids unfolding the concrete
Novikov face maps when the real-exponent specialization is checked. -/
noncomputable def recoverBottomMapGeneric (M : DescentDatum C)
    (x : π₂s C M.M) : ρ₃s C M.M :=
  pullbackMap_23 C M.M M.φ
    (natExt C.π₂ C.π₁₂ C.ρ₂_eq_π₁₂_π₂.symm M.M x)

/-- Generic universal-property core for the bottom row: if `e.symm y` is in the
image of the natural extension along `π₁₂`, and that natural extension is
injective, then `y` has a unique preimage under `recoverBottomMapGeneric`. -/
lemma recoverBottomMapGeneric_equalizer_of_natExt (M : DescentDatum C) (y : ρ₃s C M.M)
    (hexists : ∃ x : π₂s C M.M,
      (pullbackMap_23 C M.M M.φ).symm y =
        natExt C.π₂ C.π₁₂ C.ρ₂_eq_π₁₂_π₂.symm M.M x)
    (hinj : Function.Injective (natExt C.π₂ C.π₁₂ C.ρ₂_eq_π₁₂_π₂.symm M.M)) :
    ∃! x : π₂s C M.M, recoverBottomMapGeneric C M x = y := by
  rcases hexists with ⟨x, hx⟩
  have hxy : recoverBottomMapGeneric C M x = y := by
    unfold recoverBottomMapGeneric
    rw [← hx, LinearEquiv.apply_symm_apply]
  refine ⟨x, hxy, ?_⟩
  intro x' hx'
  apply hinj
  have hmaps : recoverBottomMapGeneric C M x' = recoverBottomMapGeneric C M x := by
    rw [hx', hxy]
  unfold recoverBottomMapGeneric at hmaps
  exact (pullbackMap_23 C M.M M.φ).injective hmaps

/-- Generic left-square commutativity core for the recovery diagram.  The only
input beyond the cocycle is that the chosen element of `π₁^* M` has the same
extension to `ρ₁^* M` through `π₁₂` and `π₁₃`. -/
lemma recoverLeftSquareGeneric (M : DescentDatum C) (p : π₁s C M.M)
    (hp : natExt C.π₁ C.π₁₃ C.ρ₁_eq_π₁₃_π₁.symm M.M p =
      natExt C.π₁ C.π₁₂ C.ρ₁_eq_π₁₂_π₁.symm M.M p) :
    natExt C.π₂ C.π₁₃ C.ρ₃_eq_π₁₃_π₂.symm M.M (M.φ p) =
      recoverBottomMapGeneric C M (M.φ p) := by
  calc
    natExt C.π₂ C.π₁₃ C.ρ₃_eq_π₁₃_π₂.symm M.M (M.φ p)
        = pullbackMap_13 C M.M M.φ
            (natExt C.π₁ C.π₁₃ C.ρ₁_eq_π₁₃_π₁.symm M.M p) := by
            exact (pullbackMap_natExt C.π₁ C.π₂ C.π₁₃
              C.ρ₁_eq_π₁₃_π₁.symm C.ρ₃_eq_π₁₃_π₂.symm M.M M.φ p).symm
    _ = pullbackMap_13 C M.M M.φ
            (natExt C.π₁ C.π₁₂ C.ρ₁_eq_π₁₂_π₁.symm M.M p) := by
            rw [hp]
    _ = pullbackMap_23 C M.M M.φ
          (pullbackMap_12 C M.M M.φ
            (natExt C.π₁ C.π₁₂ C.ρ₁_eq_π₁₂_π₁.symm M.M p)) := by
            have hc := congrFun M.cocycle
              (natExt C.π₁ C.π₁₂ C.ρ₁_eq_π₁₂_π₁.symm M.M p)
            simpa only [Function.comp_apply, LinearEquiv.coe_coe] using hc.symm
    _ = pullbackMap_23 C M.M M.φ
          (natExt C.π₂ C.π₁₂ C.ρ₂_eq_π₁₂_π₂.symm M.M (M.φ p)) := by
            exact congrArg (pullbackMap_23 C M.M M.φ)
              (pullbackMap_natExt C.π₁ C.π₂ C.π₁₂
                C.ρ₁_eq_π₁₂_π₁.symm C.ρ₂_eq_π₁₂_π₂.symm M.M M.φ p)
    _ = recoverBottomMapGeneric C M (M.φ p) := rfl

end AbstractMaps

section ModuleEqualizerGeneric

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Generic module-level fixed-point equalizer.  If the ring-level equalizer is
exact — `Algebra.linearMap R S` followed by `id - F` — and `N` is a flat
`R`-module, then any element of `S ⊗[R] N` fixed by `F ⊗ id` is of the form
`1 ⊗ n`.  This is the flat-base-change reduction shared by both rows of the
`RecoverDDFromIsoc` diagram. -/
theorem module_frobenius_equalizer_oneTmul
    (F : S →ₗ[R] S)
    (hexact : Function.Exact (Algebra.linearMap R S) ((LinearMap.id : S →ₗ[R] S) - F))
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Flat R N]
    (x : S ⊗[R] N) (h : F.rTensor N x = x) :
    ∃ n : N, x = (1 : S) ⊗ₜ[R] n := by
  have hExact := Module.Flat.rTensor_exact (R := R) N hexact
  have hdelta : ((LinearMap.id - F).rTensor N) x = 0 := by
    rw [LinearMap.rTensor_sub, LinearMap.sub_apply, LinearMap.rTensor_id,
      LinearMap.id_coe, id_eq, h, sub_self]
  rcases (hExact x).mp hdelta with ⟨z, hz⟩
  refine ⟨(TensorProduct.lid R N) z, ?_⟩
  rw [← hz]
  clear hz hdelta
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r n =>
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      change (algebraMap R S r) ⊗ₜ[R] n = (1 : S) ⊗ₜ[R] (r • n)
      rw [TensorProduct.tmul_smul]
      congr 1
      rw [Algebra.smul_def, mul_one]
  | add a b ha hb =>
      simp only [map_add, ha, hb, TensorProduct.tmul_add]

/-- Package a ring-level fixed-point equalizer as exactness.  If a linear
endomorphism `F` of `S` fixes the image of `Algebra.linearMap R S` and every
`F`-fixed element of `S` lies in that image, then `Algebra.linearMap R S`
followed by `id - F` is exact.  Both rows of the `RecoverDDFromIsoc` diagram use
this to feed `module_frobenius_equalizer_oneTmul`. -/
lemma algebraMap_exact_id_sub (F : S →ₗ[R] S)
    (hF : ∀ y : R, F (algebraMap R S y) = algebraMap R S y)
    (hfix : ∀ x : S, F x = x → ∃ y : R, x = algebraMap R S y) :
    Function.Exact (Algebra.linearMap R S) ((LinearMap.id : S →ₗ[R] S) - F) := by
  intro x
  rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hfix x hx.symm
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    exact (hF y).symm

end ModuleEqualizerGeneric

section RingFrobeniusEqualizer

variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

noncomputable local instance : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra

/-- Ring-level fixed-point equalizer: a Frobenius-fixed element of `R₂` lies in
the image of `π₁`.  This is the equalizer of `id` and `F2` for the
`R₁`-algebra `R₂` (via `π₁`), and the heart of the top-row equalizer in
`RecoverDDFromIsoc`.  The proof mirrors `frobenius_fixed_points`: a nonzero
coefficient at an exponent with nonzero second coordinate generates an infinite
orbit under dividing by `Λ`, contradicting Novikov finiteness. -/
lemma novikovCosimplicialRing_frobenius_equalizer_π₁ (x : (realC A).R₂)
    (h : F2 (Λ := Λ) A x = x) :
    ∃ y : (realC A).R₁, x = (realC A).π₁ y := by
  -- The fixed-point relation, written on coefficients.
  have hrel : ∀ d : Fin 2 → ↥(⊤ : AddSubgroup ℝ),
      x.val (scaleCoordinate (Λ := Λ) (1 : Fin 2) d) = x.val d := by
    intro d
    have hd := congr_fun (congr_arg Subtype.val h) d
    change x.val (scaleCoordinate (Λ := Λ) (1 : Fin 2) d) = x.val d at hd
    exact hd
  -- Coefficients vanish off the equalizer (`d 1 ≠ 0`), by the orbit argument.
  have hvanish : ∀ d : Fin 2 → ↥(⊤ : AddSubgroup ℝ), d 1 ≠ 0 → x.val d = 0 :=
    fun d hd1 => coordinateFrobenius_fixed_vanish (1 : Fin 2) x.prop hrel hd1
  -- Build the preimage by deleting the second coordinate.
  let yFun : (Unit → ↥(⊤ : AddSubgroup ℝ)) → A :=
    fun d => x.val (fun i : Fin 2 => if i = 0 then d () else 0)
  have hy : isNovikovSeries yFun := by
    intro s hs C
    let s₂ : Fin 2 → ℝ := fun i => if i = 0 then s () else 1
    have hs₂ : ∀ i, 0 < s₂ i := by
      intro i; by_cases hi : i = 0
      · simp [s₂, hi, hs ()]
      · simp [s₂, hi]
    let emb : (Unit → ↥(⊤ : AddSubgroup ℝ)) → (Fin 2 → ↥(⊤ : AddSubgroup ℝ)) :=
      fun d i => if i = 0 then d () else 0
    have hemb_inj : Function.Injective emb := by
      intro d₁ d₂ hEmb
      funext u
      have h0 := congr_fun hEmb 0
      simpa [emb] using h0
    have hfin := Set.Finite.preimage (fun _ _ _ _ hEmb => hemb_inj hEmb) (x.prop s₂ hs₂ C)
    refine hfin.subset ?_
    intro d hd
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    simp only [Set.mem_setOf_eq] at hd
    refine ⟨hd.1, ?_⟩
    have hsum : ∑ i, s₂ i * (emb d i : ℝ) = ∑ i, s i * (d i : ℝ) := by
      simp [s₂, emb, Fin.sum_univ_two]
    rw [hsum]
    exact hd.2
  refine ⟨⟨yFun, hy⟩, ?_⟩
  apply NovikovSeries.ext
  intro d
  rw [novikovCosimplicialRing_π₁_apply]
  by_cases hd1 : d 1 = 0
  · rw [if_pos hd1]
    change x.val d = x.val (fun i : Fin 2 => if i = 0 then d 0 else 0)
    have he : (fun i : Fin 2 => if i = 0 then d 0 else 0) = d := by
      funext i
      fin_cases i
      · simp
      · simp [hd1]
    rw [he]
  · rw [if_neg hd1]
    exact hvanish d hd1

/-- The first face map `π₁ : R₁ → R₂` as an `R₁`-linear map, where `R₂` is an
`R₁`-module via `π₁`. -/
noncomputable def π₁Linear :=
  Algebra.linearMap (realC A).R₁ (realC A).R₂

/-- `F2` as an `R₁`-linear endomorphism of `R₂` (using `π₁`), since `F2` fixes
the image of `π₁`. -/
noncomputable def F2Linear :=
  AlgHom.toLinearMap
    ({ F2 (Λ := Λ) A with
        commutes' := fun r =>
          congr_fun (congr_arg DFunLike.coe (F2_comp_π₁_eq (Λ := Λ) (A := A))) r } :
      (realC A).R₂ →ₐ[(realC A).R₁] (realC A).R₂)

@[simp]
lemma π₁Linear_apply (y : (realC A).R₁) :
    π₁Linear (A := A) y = (realC A).π₁ y := rfl

@[simp]
lemma F2Linear_apply (x : (realC A).R₂) :
    F2Linear (Λ := Λ) (A := A) x = F2 (Λ := Λ) A x := rfl

/-- The difference `id - F2`, whose kernel is the top-row equalizer. -/
noncomputable def idSubF2Linear :=
  (LinearMap.id : (realC A).R₂ →ₗ[(realC A).R₁] (realC A).R₂) - F2Linear (Λ := Λ) (A := A)

@[simp]
lemma idSubF2Linear_apply (x : (realC A).R₂) :
    idSubF2Linear (Λ := Λ) (A := A) x = x - F2 (Λ := Λ) A x := rfl

/-- The first row's ring-level equalizer, packaged as exactness:
`π₁` followed by `id - F2` is exact. -/
lemma π₁Linear_exact_idSubF2Linear :
    Function.Exact (π₁Linear (A := A)) (idSubF2Linear (Λ := Λ) (A := A)) :=
  algebraMap_exact_id_sub (F2Linear (Λ := Λ) (A := A))
    (fun y => congr_fun (congr_arg DFunLike.coe (F2_comp_π₁_eq (Λ := Λ) (A := A))) y)
    (fun x hx => novikovCosimplicialRing_frobenius_equalizer_π₁ A x hx)

/-- Coefficient formula for the face map `π₁₂ : R₂ → R₃` (substitution along
`Fin.castSucc`): it keeps the first two coordinates and forces the third to
vanish. -/
lemma realC_π₁₂_apply (f : (realC A).R₂) (d : Fin 3 → ↥(⊤ : AddSubgroup ℝ)) :
    ((realC A).π₁₂ f).val d =
      if d 2 = 0 then f.val (fun i : Fin 2 => d (Fin.castSucc i)) else 0 := by
  change (substitute Fin.castSucc f).val d = _
  rw [substitute_apply_singleton_compl (Fin.castSucc_injective 2) 2 (by decide) f d]

/-- Ring-level fixed-point equalizer for the bottom row: a Frobenius-fixed
(`F3`) element of `R₃` lies in the image of `π₁₂`.  The proof mirrors
`novikovCosimplicialRing_frobenius_equalizer_π₁`, with the orbit dividing the
third coordinate by `Λ`. -/
lemma novikovCosimplicialRing_frobenius_equalizer_π₁₂ (x : (realC A).R₃)
    (h : F3 (Λ := Λ) A x = x) :
    ∃ y : (realC A).R₂, x = (realC A).π₁₂ y := by
  have hrel : ∀ d : Fin 3 → ↥(⊤ : AddSubgroup ℝ),
      x.val (scaleCoordinate (Λ := Λ) (2 : Fin 3) d) = x.val d := by
    intro d
    have hd := congr_fun (congr_arg Subtype.val h) d
    change x.val (scaleCoordinate (Λ := Λ) (2 : Fin 3) d) = x.val d at hd
    exact hd
  have hvanish : ∀ d : Fin 3 → ↥(⊤ : AddSubgroup ℝ), d 2 ≠ 0 → x.val d = 0 :=
    fun d hd2 => coordinateFrobenius_fixed_vanish (2 : Fin 3) x.prop hrel hd2
  -- Build the preimage by deleting the third coordinate.
  let yFun : (Fin 2 → ↥(⊤ : AddSubgroup ℝ)) → A :=
    fun e => x.val (Fin.snoc e (0 : ↥(⊤ : AddSubgroup ℝ)))
  have hemb_inj : Function.Injective
      (fun e : Fin 2 → ↥(⊤ : AddSubgroup ℝ) =>
        (Fin.snoc e (0 : ↥(⊤ : AddSubgroup ℝ)) : Fin 3 → ↥(⊤ : AddSubgroup ℝ))) := by
    intro e1 e2 hE
    funext i
    have hci := congr_fun hE (Fin.castSucc i)
    simpa [Fin.snoc_castSucc] using hci
  have hy : isNovikovSeries yFun := by
    intro s hs C
    have hs₃ : ∀ i, 0 < (Fin.snoc s (1 : ℝ) : Fin 3 → ℝ) i := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last]; exact one_pos
      · intro j; rw [Fin.snoc_castSucc]; exact hs j
    have hfin := Set.Finite.preimage (fun _ _ _ _ hE => hemb_inj hE)
      (x.prop (Fin.snoc s (1 : ℝ) : Fin 3 → ℝ) hs₃ C)
    refine hfin.subset ?_
    intro e he
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    simp only [Set.mem_setOf_eq] at he
    refine ⟨he.1, ?_⟩
    have hsum : ∑ i, (Fin.snoc s (1 : ℝ) : Fin 3 → ℝ) i *
          ((Fin.snoc e (0 : ↥(⊤ : AddSubgroup ℝ)) : Fin 3 → ↥(⊤ : AddSubgroup ℝ)) i : ℝ) =
            ∑ i, s i * (e i : ℝ) := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, ZeroMemClass.coe_zero, mul_zero, add_zero]
    rw [hsum]
    exact he.2
  refine ⟨⟨yFun, hy⟩, ?_⟩
  apply NovikovSeries.ext
  intro d
  rw [realC_π₁₂_apply]
  by_cases hd2 : d 2 = 0
  · rw [if_pos hd2]
    change x.val d =
      x.val (Fin.snoc (fun i : Fin 2 => d (Fin.castSucc i)) (0 : ↥(⊤ : AddSubgroup ℝ)))
    have hlast : d (Fin.last 2) = 0 := by
      have h2eq : (Fin.last 2 : Fin 3) = 2 := by decide
      rw [h2eq]; exact hd2
    have key : Fin.snoc (fun i : Fin 2 => d (Fin.castSucc i))
        (0 : ↥(⊤ : AddSubgroup ℝ)) = d := by
      rw [← hlast]; exact Fin.snoc_init_self d
    rw [key]
  · rw [if_neg hd2]
    exact hvanish d hd2

noncomputable local instance : Algebra (realC A).R₂ (realC A).R₃ := (realC A).π₁₂.toAlgebra

/-- The face map `π₁₂ : R₂ → R₃` as an `R₂`-linear map (with `R₃` an `R₂`-module
via `π₁₂`). -/
noncomputable def π₁₂Linear :=
  Algebra.linearMap (realC A).R₂ (realC A).R₃

/-- `F3` as an `R₂`-linear endomorphism of `R₃` (using `π₁₂`), since `F3` fixes
the image of `π₁₂`. -/
noncomputable def F3Linear :=
  AlgHom.toLinearMap
    ({ F3 (Λ := Λ) A with
        commutes' := fun r =>
          congr_fun (congr_arg DFunLike.coe (F3_comp_π₁₂_eq (Λ := Λ) (A := A))) r } :
      (realC A).R₃ →ₐ[(realC A).R₂] (realC A).R₃)

@[simp]
lemma π₁₂Linear_apply (y : (realC A).R₂) :
    π₁₂Linear (A := A) y = (realC A).π₁₂ y := rfl

@[simp]
lemma F3Linear_apply (x : (realC A).R₃) :
    F3Linear (Λ := Λ) (A := A) x = F3 (Λ := Λ) A x := rfl

/-- The difference `id - F3`, whose kernel is the bottom-row equalizer. -/
noncomputable def idSubF3Linear :=
  (LinearMap.id : (realC A).R₃ →ₗ[(realC A).R₂] (realC A).R₃) - F3Linear (Λ := Λ) (A := A)

@[simp]
lemma idSubF3Linear_apply (x : (realC A).R₃) :
    idSubF3Linear (Λ := Λ) (A := A) x = x - F3 (Λ := Λ) A x := rfl

/-- The bottom row's ring-level equalizer, packaged as exactness:
`π₁₂` followed by `id - F3` is exact. -/
lemma π₁₂Linear_exact_idSubF3Linear :
    Function.Exact (π₁₂Linear (A := A)) (idSubF3Linear (Λ := Λ) (A := A)) :=
  algebraMap_exact_id_sub (F3Linear (Λ := Λ) (A := A))
    (fun y => congr_fun (congr_arg DFunLike.coe (F3_comp_π₁₂_eq (Λ := Λ) (A := A))) y)
    (fun x hx => novikovCosimplicialRing_frobenius_equalizer_π₁₂ A x hx)

end RingFrobeniusEqualizer

section RecoverDDFromIsoc

variable {Λ : ℝ} [Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

/-- The map `m ↦ 1 ⊗ m` into pullback along `π₁`. -/
noncomputable def oneTmulπ₁ (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] :
    M →ₗ[(realC A).R₁] π₁s (realC A) M := by
  change M →ₗ[(realC A).R₁]
    (letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
     (realC A).R₂ ⊗[(realC A).R₁] M)
  letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
  exact TensorProduct.mk (realC A).R₁ (realC A).R₂ M 1

@[simp]
lemma oneTmulπ₁_apply (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] (m : M) :
    oneTmulπ₁ A M m =
      (letI : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra
       (1 : (realC A).R₂) ⊗ₜ[(realC A).R₁] m) :=
  rfl

/-- The top-row inclusion `M → π₂^* M`, namely `φ ∘ π₁^*`. -/
noncomputable def recoverTopMap (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (m : M.M) : π₂s (realC A) M.M :=
  M.φ (oneTmulπ₁ A M.M m)

@[simp]
lemma recoverTopMap_apply (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (m : M.M) :
    recoverTopMap A M m = M.φ (oneTmulπ₁ A M.M m) :=
  rfl

/-- The concrete bottom-row inclusion `π₂^* M → ρ₃^* M`, namely
`π₂₃^* φ ∘ π₁₂^*`. -/
noncomputable def recoverBottomMap (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (x : π₂s (realC A) M.M) : ρ₃s (realC A) M.M :=
  recoverBottomMapGeneric (realC A) M x

lemma recoverBottomMap_apply (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (x : π₂s (realC A) M.M) :
    recoverBottomMap A M x = recoverBottomMapGeneric (realC A) M x :=
  rfl

end RecoverDDFromIsoc

section ModuleFrobeniusEqualizer

variable {Λ : ℝ} [Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

noncomputable local instance : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₁.toAlgebra

/-- Top-row module-level equalizer: an element of `π₁^* M` fixed by `F2 ⊗ id`
is `1 ⊗ m`.  Specialises the generic equalizer at `π₁`/`F2`, using flatness of
`M`. -/
theorem pi1_module_frobenius_equalizer_oneTmul
    (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] [Module.Flat (realC A).R₁ M]
    (x : π₁s (realC A) M)
    (h : (F2Linear (Λ := Λ) (A := A)).rTensor M x = x) :
    ∃ m : M, x = oneTmulπ₁ A M m := by
  obtain ⟨m, hm⟩ := module_frobenius_equalizer_oneTmul
    (F2Linear (Λ := Λ) (A := A)) (π₁Linear_exact_idSubF2Linear (Λ := Λ) (A := A)) M x h
  exact ⟨m, hm⟩

/-- The substitution `A((t,u)) → A((t))` merging both variables also retracts
`π₁`. -/
lemma π₂Retract_comp_π₁ :
    (π₂Retract (A := A)).comp (realC A).π₁ = RingHom.id (realC A).R₁ := by
  apply RingHom.ext
  intro f
  change substitute (fun _ : Fin 2 => ()) (substitute (fun _ : Unit => (0 : Fin 2)) f) = f
  rw [← substitute_comp]
  simpa using substitute_id (Γ := (⊤ : AddSubgroup ℝ)) f

/-- The retraction of `π₁` as an `R₁`-linear map (with `R₂` an `R₁`-module via
`π₁`). -/
noncomputable def π₁RetractLinear : (realC A).R₂ →ₗ[(realC A).R₁] (realC A).R₁ :=
  AlgHom.toLinearMap
    ({ π₂Retract (A := A) with
        commutes' := fun r =>
          congr_fun (congr_arg DFunLike.coe (π₂Retract_comp_π₁ (A := A))) r } :
      (realC A).R₂ →ₐ[(realC A).R₁] (realC A).R₁)

@[simp]
lemma π₁RetractLinear_rTensor_oneTmulπ₁ (M : Type*) [AddCommGroup M]
    [Module (realC A).R₁ M] (m : M) :
    (TensorProduct.lid (realC A).R₁ M)
      ((π₁RetractLinear A).rTensor M (oneTmulπ₁ A M m)) = m := by
  rw [oneTmulπ₁_apply, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  have h1 : π₁RetractLinear A (1 : (realC A).R₂) = 1 := (π₂Retract (A := A)).map_one
  rw [h1, one_smul]

lemma oneTmulπ₁_injective (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] :
    Function.Injective (oneTmulπ₁ A M) := by
  intro m n hmn
  have hm := π₁RetractLinear_rTensor_oneTmulπ₁ (A := A) M m
  have hn := π₁RetractLinear_rTensor_oneTmulπ₁ (A := A) M n
  rw [← hm, ← hn, hmn]

/-- The top-row inclusion lands in the equalizer: `recoverTopMap m` is fixed by
the Frobenius `FM2`. -/
lemma recoverTopMap_mem_equalizer (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) (m : M.M) :
    FM2 (Λ := Λ) A M (recoverTopMap A M m) = recoverTopMap A M m := by
  rw [recoverTopMap_apply, FM2_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, oneTmulπ₁_apply, baseChangeSemilinearSelf_tmul, map_one]

/-- Top-row equalizer universal property: every `FM2`-fixed element of `π₂^* M`
is `recoverTopMap m` for a unique `m`. -/
theorem recoverTopMap_equalizer (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (x : π₂s (realC A) M.M) (hx : FM2 (Λ := Λ) A M x = x) :
    ∃! m : M.M, recoverTopMap A M m = x := by
  -- `F2`-semilinear self-map agrees with `F2 ⊗ id` on `π₁^* M`.
  have hbridge : ∀ w : π₁s (realC A) M.M,
      baseChangeSemilinearSelf (realC A).π₁ (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
        (F2_comp_π₁_eq (Λ := Λ) A) (F2Inv_comp_π₁_eq (Λ := Λ) A) M.M w =
        (F2Linear (Λ := Λ) (A := A)).rTensor M.M w :=
    fun w => baseChangeSemilinearSelf_eq_rTensor (realC A).π₁ (F2 (Λ := Λ) A)
      (F2Inv (Λ := Λ) A) (F2_comp_π₁_eq (Λ := Λ) A) (F2Inv_comp_π₁_eq (Λ := Λ) A) M.M
      (F2Linear (Λ := Λ) (A := A)) (fun _ => rfl) w
  -- `M.φ.symm x` is fixed by the `F2`-semilinear self-map.
  have hfix : baseChangeSemilinearSelf (realC A).π₁ (F2 (Λ := Λ) A) (F2Inv (Λ := Λ) A)
      (F2_comp_π₁_eq (Λ := Λ) A) (F2Inv_comp_π₁_eq (Λ := Λ) A) M.M (M.φ.symm x) =
        M.φ.symm x := by
    have h1 := hx
    rw [FM2_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply] at h1
    have h2 := congrArg M.φ.symm h1
    rwa [LinearEquiv.symm_apply_apply] at h2
  have hfix' : (F2Linear (Λ := Λ) (A := A)).rTensor M.M (M.φ.symm x) = M.φ.symm x := by
    rw [← hbridge (M.φ.symm x)]; exact hfix
  obtain ⟨m, hm⟩ := pi1_module_frobenius_equalizer_oneTmul A M.M (M.φ.symm x) hfix'
  have hmx : recoverTopMap A M m = x := by
    rw [recoverTopMap_apply, ← hm, LinearEquiv.apply_symm_apply]
  refine ⟨m, hmx, ?_⟩
  intro m' hm'
  have heq : recoverTopMap A M m' = recoverTopMap A M m := by rw [hm', hmx]
  rw [recoverTopMap_apply, recoverTopMap_apply] at heq
  exact oneTmulπ₁_injective A M.M (M.φ.injective heq)

end ModuleFrobeniusEqualizer

section ModuleFrobeniusEqualizerBottom

variable {Λ : ℝ} [Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

noncomputable local instance : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
noncomputable local instance : Algebra (realC A).R₁ (realC A).R₃ := (realC A).ρ₂.toAlgebra

/-- `π₁₂ : R₂ → R₃` as an `R₁`-linear map, with `R₂` an `R₁`-module via `π₂`
and `R₃` via `ρ₂`.  The underlying function is `π₁₂`, so it shares the
ring-level equalizer of `π₁₂Linear`. -/
noncomputable def π₁₂LinearR₁ : (realC A).R₂ →ₗ[(realC A).R₁] (realC A).R₃ :=
  AlgHom.toLinearMap
    ({ (realC A).π₁₂ with
        commutes' := fun r =>
          (congr_fun (congr_arg DFunLike.coe (realC A).ρ₂_eq_π₁₂_π₂) r).symm } :
      (realC A).R₂ →ₐ[(realC A).R₁] (realC A).R₃)

/-- `F3` as an `R₁`-linear endomorphism of `R₃` (with `R₃` an `R₁`-module via
`ρ₂`), since `F3` fixes the image of `ρ₂`. -/
noncomputable def F3LinearR₁ : (realC A).R₃ →ₗ[(realC A).R₁] (realC A).R₃ :=
  AlgHom.toLinearMap
    ({ F3 (Λ := Λ) A with
        commutes' := fun r =>
          congr_fun (congr_arg DFunLike.coe (F3_comp_ρ₂_eq (Λ := Λ) (A := A))) r } :
      (realC A).R₃ →ₐ[(realC A).R₁] (realC A).R₃)

/-- The difference `id - F3` over `R₁`. -/
noncomputable def idSubF3LinearR₁ :=
  (LinearMap.id : (realC A).R₃ →ₗ[(realC A).R₁] (realC A).R₃) - F3LinearR₁ (Λ := Λ) A

/-- Bottom-row module-level equalizer: an element of `ρ₂^* M` fixed by the
`F3`-semilinear self-map is in the image of `natExt π₂ π₁₂` (i.e. of
`π₁₂^* : π₂^* M → ρ₂^* M`).  Proved by transporting the ring-level equalizer
`π₁₂Linear_exact_idSubF3Linear` along flat base change by `M`. -/
theorem rho2_module_frobenius_equalizer_natExt
    (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] [Module.Flat (realC A).R₁ M]
    (y : ρ₂s (realC A) M)
    (h : baseChangeSemilinearSelf (realC A).ρ₂ (F3 (Λ := Λ) A) (F3Inv (Λ := Λ) A)
        (F3_comp_ρ₂_eq (Λ := Λ) (A := A)) (F3Inv_comp_ρ₂_eq (Λ := Λ) (A := A)) M y = y) :
    ∃ z : π₂s (realC A) M,
      y = natExt (realC A).π₂ (realC A).π₁₂ (realC A).ρ₂_eq_π₁₂_π₂.symm M z := by
  -- The ring-level equalizer, reused at the `R₁`-linear structure (same coes).
  have hexactR₁ : Function.Exact (π₁₂LinearR₁ A) (idSubF3LinearR₁ (Λ := Λ) A) := by
    intro b
    exact π₁₂Linear_exact_idSubF3Linear (Λ := Λ) (A := A) b
  have hExactT := Module.Flat.rTensor_exact M hexactR₁
  -- `F3LinearR₁ ⊗ id` agrees with the `F3`-semilinear self-map on `ρ₂^* M`.
  have hfrob : ∀ w : ρ₂s (realC A) M,
      (F3LinearR₁ (Λ := Λ) A).rTensor M w =
        baseChangeSemilinearSelf (realC A).ρ₂ (F3 (Λ := Λ) A) (F3Inv (Λ := Λ) A)
          (F3_comp_ρ₂_eq (Λ := Λ) (A := A)) (F3Inv_comp_ρ₂_eq (Λ := Λ) (A := A)) M w :=
    fun w => (baseChangeSemilinearSelf_eq_rTensor (realC A).ρ₂ (F3 (Λ := Λ) A)
      (F3Inv (Λ := Λ) A) (F3_comp_ρ₂_eq (Λ := Λ) (A := A))
      (F3Inv_comp_ρ₂_eq (Λ := Λ) (A := A)) M (F3LinearR₁ (Λ := Λ) A) (fun _ => rfl) w).symm
  -- `natExt` is exactly `π₁₂LinearR₁ ⊗ id`.
  have hnat : ∀ w : π₂s (realC A) M,
      natExt (realC A).π₂ (realC A).π₁₂ (realC A).ρ₂_eq_π₁₂_π₂.symm M w =
        (π₁₂LinearR₁ A).rTensor M w :=
    fun w => natExt_eq_rTensor (realC A).π₂ (realC A).π₁₂
      (realC A).ρ₂_eq_π₁₂_π₂.symm M (π₁₂LinearR₁ A) (fun _ => rfl) w
  have hdelta : (idSubF3LinearR₁ (Λ := Λ) A).rTensor M y = 0 := by
    have e : (idSubF3LinearR₁ (Λ := Λ) A).rTensor M y = y - (F3LinearR₁ (Λ := Λ) A).rTensor M y := by
      rw [show idSubF3LinearR₁ (Λ := Λ) A =
          (LinearMap.id : (realC A).R₃ →ₗ[(realC A).R₁] (realC A).R₃) - F3LinearR₁ (Λ := Λ) A
            from rfl,
        LinearMap.rTensor_sub, LinearMap.sub_apply, LinearMap.rTensor_id, LinearMap.id_coe,
        id_eq]
    rw [e, hfrob y, h, sub_self]
  obtain ⟨p, hp⟩ := (hExactT y).mp hdelta
  exact ⟨p, by rw [hnat p]; exact hp.symm⟩

end ModuleFrobeniusEqualizerBottom

section RecoverBottomEqualizer

/-- Generic form of the bottom-row "lands in the equalizer" fact.  For a
face-fixing semilinear `σ` on `R₃` (fixing `π₁₂` and `ρ₂`), the Frobenius on
`ρ₃^* M` conjugated through `pullbackMap_23` fixes every element in the image of
`recoverBottomMapGeneric`.  Proved over an abstract cosimplicial ring `C` so the
concrete `realC` machinery never enters the kernel reduction (which otherwise
triggers a deterministic timeout). -/
lemma recoverBottomMapGeneric_mem_equalizer_generic {C : CosimplicialRing}
    (σ σinv : C.R₃ →+* C.R₃) [RingHomInvPair σ σinv] [RingHomInvPair σinv σ]
    (hσπ₁₂ : σ.comp C.π₁₂ = C.π₁₂)
    (hσρ₂ : σ.comp C.ρ₂ = C.ρ₂) (hσρ₂i : σinv.comp C.ρ₂ = C.ρ₂)
    (M : DescentDatum C) (x : π₂s C M.M) :
    pullbackMap_23 C M.M M.φ
        (baseChangeSemilinearSelf C.ρ₂ σ σinv hσρ₂ hσρ₂i M.M
          ((pullbackMap_23 C M.M M.φ).symm (recoverBottomMapGeneric C M x))) =
      recoverBottomMapGeneric C M x := by
  -- `σ` fixes the image of `natExt π₂ π₁₂`, since `σ ∘ π₁₂ = π₁₂`.
  have hfix : baseChangeSemilinearSelf C.ρ₂ σ σinv hσρ₂ hσρ₂i M.M
        (natExt C.π₂ C.π₁₂ C.ρ₂_eq_π₁₂_π₂.symm M.M x) =
      natExt C.π₂ C.π₁₂ C.ρ₂_eq_π₁₂_π₂.symm M.M x := by
    let τ : C.R₂ →+* C.R₂ := RingHom.id C.R₂
    have hτπ₂ : τ.comp C.π₂ = C.π₂ := rfl
    have hcompat : σ.comp C.π₁₂ = C.π₁₂.comp τ := by
      simpa [τ] using hσπ₁₂
    letI : Algebra C.R₁ C.R₂ := C.π₂.toAlgebra
    have hid : baseChangeSemilinearSelf C.π₂ τ τ hτπ₂ hτπ₂ M.M x = x := by
      simpa [τ] using
        (baseChangeSemilinearSelf_eq_rTensor C.π₂ τ τ hτπ₂ hτπ₂ M.M
          (LinearMap.id : C.R₂ →ₗ[C.R₁] C.R₂) (fun _ => rfl) x)
    have hnat := natExt_baseChangeSemilinearSelf C.π₂ C.π₁₂ τ τ σ σinv
      C.ρ₂_eq_π₁₂_π₂.symm hτπ₂ hτπ₂ hσρ₂ hσρ₂i hcompat M.M x
    rw [hid] at hnat
    exact hnat.symm
  unfold recoverBottomMapGeneric
  rw [LinearEquiv.symm_apply_apply, hfix]

variable {Λ : ℝ} [Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

/-- The bottom-row inclusion lands in the equalizer: every `recoverBottomMap x`
is fixed by the Frobenius `FM3`. -/
lemma recoverBottomMap_mem_equalizer (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (x : π₂s (realC A) M.M) :
    FM3 (Λ := Λ) A M (recoverBottomMap A M x) = recoverBottomMap A M x := by
  rw [recoverBottomMap_apply]
  show FM3 (Λ := Λ) A M (recoverBottomMapGeneric (realC A) M x) =
    recoverBottomMapGeneric (realC A) M x
  simp only [FM3]
  rw [FM3_13_eq_FM3_23, FM3_23_apply]
  exact recoverBottomMapGeneric_mem_equalizer_generic (F3 (Λ := Λ) A) (F3Inv (Λ := Λ) A)
    (F3_comp_π₁₂_eq (Λ := Λ) A) (F3_comp_ρ₂_eq (Λ := Λ) A) (F3Inv_comp_ρ₂_eq (Λ := Λ) A) M x

end RecoverBottomEqualizer

section BottomRetract

variable (A : Type*) [CommRing A]

/-- The substitution `A((t,u,v)) → A((t,u))` merging the third variable into the
second retracts `π₁₂`.  The variable map `Fin 3 → Fin 2` keeps the first two
coordinates and sends the last one into the second. -/
noncomputable def π₁₂Retract : (realC A).R₃ →+* (realC A).R₂ :=
  substituteRingHom (Γ := (⊤ : AddSubgroup ℝ)) (A := A)
    (Fin.lastCases (0 : Fin 2) (fun i : Fin 2 => i))

@[simp]
lemma π₁₂Retract_comp_π₁₂ :
    (π₁₂Retract (A := A)).comp (realC A).π₁₂ = RingHom.id (realC A).R₂ := by
  apply RingHom.ext
  intro f
  change substitute (Fin.lastCases (0 : Fin 2) (fun i : Fin 2 => i))
      (substitute Fin.castSucc f) = f
  rw [← substitute_comp]
  have hmerge : (Fin.lastCases (0 : Fin 2) (fun i : Fin 2 => i)) ∘ Fin.castSucc
      = (id : Fin 2 → Fin 2) := by
    funext i
    simp only [Function.comp_apply, Fin.lastCases_castSucc, id_eq]
  rw [hmerge]
  exact substitute_id (Γ := (⊤ : AddSubgroup ℝ)) f

/-- The retraction also intertwines `ρ₂` and `π₂`, i.e. `π₁₂Retract ∘ ρ₂ = π₂`,
since `ρ₂ = π₁₂ ∘ π₂` and `π₁₂Retract ∘ π₁₂ = id`.  This makes `π₁₂Retract`
`R₁`-linear when `R₃`/`R₂` carry the module structures from `ρ₂`/`π₂`. -/
lemma π₁₂Retract_comp_ρ₂ :
    (π₁₂Retract (A := A)).comp (realC A).ρ₂ = (realC A).π₂ := by
  rw [(realC A).ρ₂_eq_π₁₂_π₂, ← RingHom.comp_assoc, π₁₂Retract_comp_π₁₂,
    RingHom.id_comp]

noncomputable local instance : Algebra (realC A).R₁ (realC A).R₂ := (realC A).π₂.toAlgebra
noncomputable local instance : Algebra (realC A).R₁ (realC A).R₃ := (realC A).ρ₂.toAlgebra

/-- The retraction `π₁₂Retract` as an `R₁`-linear map, where `R₂` is an
`R₁`-module via `π₂` and `R₃` via `ρ₂`. -/
noncomputable def π₁₂RetractLinearR₁ : (realC A).R₃ →ₗ[(realC A).R₁] (realC A).R₂ :=
  AlgHom.toLinearMap
    ({ π₁₂Retract (A := A) with
        commutes' := fun r =>
          congr_fun (congr_arg DFunLike.coe (π₁₂Retract_comp_ρ₂ (A := A))) r } :
      (realC A).R₃ →ₐ[(realC A).R₁] (realC A).R₂)

/-- After tensoring with a module, `π₁₂RetractLinearR₁` is a left inverse to the
natural extension map along `π₁₂`. -/
lemma π₁₂RetractLinearR₁_rTensor_natExt (M : Type*) [AddCommGroup M]
    [Module (realC A).R₁ M] (x : π₂s (realC A) M) :
    (π₁₂RetractLinearR₁ A).rTensor M
        (natExt (realC A).π₂ (realC A).π₁₂ (realC A).ρ₂_eq_π₁₂_π₂.symm M x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      rw [natExt_tmul, LinearMap.rTensor_tmul]
      have hs : π₁₂RetractLinearR₁ A ((realC A).π₁₂ s) = s :=
        congr_fun (congr_arg DFunLike.coe (π₁₂Retract_comp_π₁₂ (A := A))) s
      rw [hs]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The natural extension map along `π₁₂` is injective after tensoring with any
`R₁`-module, because `π₁₂` admits the retraction `π₁₂Retract`. -/
lemma natExt_π₁₂_injective (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] :
    Function.Injective
      (natExt (realC A).π₂ (realC A).π₁₂ (realC A).ρ₂_eq_π₁₂_π₂.symm M) := by
  intro x y hxy
  have hx := π₁₂RetractLinearR₁_rTensor_natExt (A := A) M x
  have hy := π₁₂RetractLinearR₁_rTensor_natExt (A := A) M y
  rw [← hx, ← hy, hxy]

end BottomRetract

section RecoverDiagramCommutativity

variable {Λ : ℝ} [Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

/-- On the element `1 ⊗ m`, scalar extension from `π₁^* M` to `ρ₁^* M` is
independent of whether it is taken along `π₁₂` or `π₁₃`. -/
lemma natExt_π₁₂_oneTmulπ₁_eq_natExt_π₁₃_oneTmulπ₁
    (M : Type*) [AddCommGroup M] [Module (realC A).R₁ M] (m : M) :
    natExt (realC A).π₁ (realC A).π₁₂ (realC A).ρ₁_eq_π₁₂_π₁.symm M
        (oneTmulπ₁ A M m) =
      natExt (realC A).π₁ (realC A).π₁₃ (realC A).ρ₁_eq_π₁₃_π₁.symm M
        (oneTmulπ₁ A M m) := by
  rw [oneTmulπ₁_apply, natExt_tmul, natExt_tmul]
  simp only [map_one]

end RecoverDiagramCommutativity

section RecoverBottomUniversalProperty

variable {Λ : ℝ} [Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

attribute [local irreducible] baseChangeSemilinearSelf pullbackMap_23

/-- Bottom-row equalizer universal property: every `FM3`-fixed element of
`ρ₃^* M` is `recoverBottomMap x` for a unique `x : π₂^* M`. -/
theorem recoverBottomMap_equalizer (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A)
    (y : ρ₃s (realC A) M.M) (hy : FM3 (Λ := Λ) A M y = y) :
    ∃! x : π₂s (realC A) M.M, recoverBottomMap A M x = y := by
  let e := pullbackMap_23 (realC A) M.M M.φ
  have hy23 : FM3_23 (Λ := Λ) A M y = y := by
    simpa [FM3, FM3_13_eq_FM3_23 (Λ := Λ) A M] using hy
  have hfix : baseChangeSemilinearSelf (realC A).ρ₂ (F3 (Λ := Λ) A) (F3Inv (Λ := Λ) A)
      (F3_comp_ρ₂_eq (Λ := Λ) (A := A)) (F3Inv_comp_ρ₂_eq (Λ := Λ) (A := A)) M.M
        (e.symm y) = e.symm y := by
    rw [FM3_23_apply] at hy23
    have h := congrArg e.symm hy23
    simpa [e] using h
  have hexists : ∃ x : π₂s (realC A) M.M,
      e.symm y = natExt (realC A).π₂ (realC A).π₁₂ (realC A).ρ₂_eq_π₁₂_π₂.symm M.M x :=
    rho2_module_frobenius_equalizer_natExt A M.M (e.symm y) hfix
  exact recoverBottomMapGeneric_equalizer_of_natExt (realC A) M y hexists
    (natExt_π₁₂_injective A M.M)

end RecoverBottomUniversalProperty

section RecoverFinal

variable {Λ : ℝ} [Fact (Λ > 1)]
variable (A : Type*) [CommRing A]

/-- Commutativity of the left square in the `RecoverDDFromIsoc` diagram: the two
routes `M → ρ₃^* M` agree, namely `π₁₃^* ∘ (φ ∘ π₁^*) = (π₂₃^* φ ∘ π₁₂^*) ∘
(φ ∘ π₁^*)`.  This is the cocycle condition together with
`natExt_π₁₂_oneTmulπ₁_eq_natExt_π₁₃_oneTmulπ₁`. -/
lemma recoverLeftSquare (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) (m : M.M) :
    natExt (realC A).π₂ (realC A).π₁₃ (realC A).ρ₃_eq_π₁₃_π₂.symm M.M
        (recoverTopMap A M m) =
      recoverBottomMap A M (recoverTopMap A M m) := by
  rw [recoverBottomMap_apply, recoverTopMap_apply]
  exact recoverLeftSquareGeneric (realC A) M (oneTmulπ₁ A M.M m)
    (natExt_π₁₂_oneTmulπ₁_eq_natExt_π₁₃_oneTmulπ₁ A M.M m).symm

/-- Bundled conclusion of Lemma `RecoverDDFromIsoc`: the two-row recovery diagram
commutes and both rows are equalizers of `id` against the descended Frobenius.
The vertical maps are `recoverTopMap = φ ∘ π₁^*` (left), `π₁₃^*` (middle and
right); the rows run from `M`/`π₂^* M` through `π₂^* M`/`ρ₃^* M`. -/
structure RecoverDDFromIsocData
    (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) : Prop where
  /-- The left square commutes. -/
  leftSquare : ∀ m : M.M,
    π₁₃star A M.M (recoverTopMap A M m) = recoverBottomMap A M (recoverTopMap A M m)
  /-- The right squares commute: `π₁₃^* ∘ FM2 = FM3 ∘ π₁₃^*`. -/
  rightSquare : ∀ x : π₂s (realC A) M.M,
    π₁₃star A M.M (FM2 (Λ := Λ) A M x) = FM3 (Λ := Λ) A M (π₁₃star A M.M x)
  /-- The top-row inclusion lands in the equalizer. -/
  topMem : ∀ m : M.M, FM2 (Λ := Λ) A M (recoverTopMap A M m) = recoverTopMap A M m
  /-- The top row is an equalizer: every `FM2`-fixed element of `π₂^* M` is
  `recoverTopMap m` for a unique `m`. -/
  topEqualizer : ∀ x : π₂s (realC A) M.M, FM2 (Λ := Λ) A M x = x →
    ∃! m : M.M, recoverTopMap A M m = x
  /-- The bottom-row inclusion lands in the equalizer. -/
  bottomMem : ∀ x : π₂s (realC A) M.M,
    FM3 (Λ := Λ) A M (recoverBottomMap A M x) = recoverBottomMap A M x
  /-- The bottom row is an equalizer: every `FM3`-fixed element of `ρ₃^* M` is
  `recoverBottomMap x` for a unique `x`. -/
  bottomEqualizer : ∀ y : ρ₃s (realC A) M.M, FM3 (Λ := Λ) A M y = y →
    ∃! x : π₂s (realC A) M.M, recoverBottomMap A M x = y

/-- **Lemma `RecoverDDFromIsoc`.**  For a real Novikov descent datum `M`, the
two-row recovery diagram commutes and both rows are equalizers. -/
theorem recoverDDFromIsoc_equalizerLemma
    (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) A) :
    RecoverDDFromIsocData (Λ := Λ) A M where
  leftSquare m := by rw [π₁₃star_eq_natExt]; exact recoverLeftSquare A M m
  rightSquare x := face13_FM2 (Λ := Λ) A M x
  topMem m := recoverTopMap_mem_equalizer (Λ := Λ) A M m
  topEqualizer x hx := recoverTopMap_equalizer (Λ := Λ) A M x hx
  bottomMem x := recoverBottomMap_mem_equalizer (Λ := Λ) A M x
  bottomEqualizer y hy := recoverBottomMap_equalizer (Λ := Λ) A M y hy

end RecoverFinal

end Novikov.Descent
