import Novikov.Descent.Abstract.Constant
import Mathlib.CategoryTheory.Functor.FullyFaithful

open TensorProduct CategoryTheory
open Novikov.Miscellany

namespace Novikov.Descent.Abstract

variable (E : ExtendedCosimplicialRing)

/-- The natural map from `R₀` to the equalizer of `π₁` and `π₂`. -/
def equalizerMap (E : ExtendedCosimplicialRing) : E.R₀ → E.π₁.eqLocus E.π₂ :=
  fun a => ⟨E.π₀ a, by
    rw [RingHom.mem_eqLocus]
    exact congr_fun (congr_arg DFunLike.coe E.π₁_π₀_eq_π₂_π₀) a⟩

private noncomputable def face₁Linear :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
    E.R₁ →ₗ[E.R₀] E.R₂ := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  exact
  { toFun := E.π₁
    map_add' := E.π₁.map_add
    map_smul' := by
      intro a r
      change E.π₁ (E.π₀ a * r) = (E.π₁.comp E.π₀) a * E.π₁ r
      rw [map_mul]
      rfl }

private noncomputable def face₂Linear :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
    E.R₁ →ₗ[E.R₀] E.R₂ := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  exact
  { toFun := E.π₂
    map_add' := E.π₂.map_add
    map_smul' := by
      intro a r
      change E.π₂ (E.π₀ a * r) = (E.π₁.comp E.π₀) a * E.π₂ r
      rw [show (E.π₁.comp E.π₀) a = (E.π₂.comp E.π₀) a by
        exact congr_fun (congr_arg DFunLike.coe E.π₁_π₀_eq_π₂_π₀) a]
      rw [map_mul]
      rfl }

private lemma equalizer_of_φ_fixed
    (hEq : Function.Bijective (equalizerMap E))
    (P : Type*) [AddCommGroup P] [Module E.R₀ P]
    [Module.Finite E.R₀ P] [Module.Projective E.R₀ P] :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
    ∀ x : E.R₁ ⊗[E.R₀] P,
      (constantDescentDatum E P).φ
          (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
           (1 : E.R₂) ⊗ₜ[E.R₁] x) =
        (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
         (1 : E.R₂) ⊗ₜ[E.R₁] x) →
      ∃ p : P, x = (1 : E.R₁) ⊗ₜ[E.R₀] p := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  letI : Algebra E.R₀ E.R₂ := (E.π₁.comp E.π₀).toAlgebra
  intro x hφ
  -- Deduce face₁ ⊗ id = face₂ ⊗ id from hφ
  let e₁ : (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
      E.R₂ ⊗[E.R₁] (E.R₁ ⊗[E.R₀] P)) ≃ₗ[E.R₂] E.R₂ ⊗[E.R₀] P :=
    baseChange_assoc_eq E.π₀ E.π₁ (rfl : E.π₁.comp E.π₀ = _) P
  let e₂ : (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
      E.R₂ ⊗[E.R₁] (E.R₁ ⊗[E.R₀] P)) ≃ₗ[E.R₂] E.R₂ ⊗[E.R₀] P :=
    baseChange_assoc_eq E.π₀ E.π₂ E.π₁_π₀_eq_π₂_π₀.symm P
  let σ₁ := face₁Linear E
  let σ₂ := face₂Linear E
  have h₁ (w : E.R₁ ⊗[E.R₀] P) :
      e₁ (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
        (1 : E.R₂) ⊗ₜ[E.R₁] w) = TensorProduct.map σ₁ LinearMap.id w := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r p => rw [TensorProduct.map_tmul]; simp [e₁, σ₁, face₁Linear, Algebra.smul_def]; rfl
    | add x y hx hy =>
      letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
      rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]
  have h₂ (w : E.R₁ ⊗[E.R₀] P) :
      e₂ (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra;
        (1 : E.R₂) ⊗ₜ[E.R₁] w) = TensorProduct.map σ₂ LinearMap.id w := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r p => rw [TensorProduct.map_tmul]; simp [e₂, σ₂, face₂Linear, Algebra.smul_def]; rfl
    | add x y hx hy =>
      letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
      rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]
  have hh := congr_arg e₂.toLinearMap hφ
  change e₂ ((e₁.trans e₂.symm) (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
      (1 : E.R₂) ⊗ₜ[E.R₁] x)) =
    e₂ (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra;
      (1 : E.R₂) ⊗ₜ[E.R₁] x) at hh
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] at hh
  have h_eq : TensorProduct.map σ₁ LinearMap.id x = TensorProduct.map σ₂ LinearMap.id x :=
    calc
      TensorProduct.map σ₁ LinearMap.id x = e₁ (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
        (1 : E.R₂) ⊗ₜ[E.R₁] x) := (h₁ x).symm
      _ = e₂ (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra;
        (1 : E.R₂) ⊗ₜ[E.R₁] x) := hh
      _ = TensorProduct.map σ₂ LinearMap.id x := h₂ x
  -- Now h_eq : σ₁ ⊗ id = σ₂ ⊗ id, proceed to equalizer argument
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective E.R₀ P
  have h_recover (x' : E.R₁ ⊗[E.R₀] P) :
      TensorProduct.map LinearMap.id f (TensorProduct.map LinearMap.id g x') = x' := by
    calc
      TensorProduct.map LinearMap.id f (TensorProduct.map LinearMap.id g x')
          = ((TensorProduct.map LinearMap.id f) ∘ₗ (TensorProduct.map LinearMap.id g)) x' := rfl
      _ = TensorProduct.map (LinearMap.id ∘ₗ LinearMap.id) (f ∘ₗ g) x' := by
        rw [TensorProduct.map_comp]
      _ = TensorProduct.map LinearMap.id LinearMap.id x' := by simp [hfg]
      _ = x' := by simp
  set y := TensorProduct.map LinearMap.id g x with hy_def
  have h_comm (σ : E.R₁ →ₗ[E.R₀] E.R₂) :
      TensorProduct.map σ LinearMap.id ∘ₗ TensorProduct.map LinearMap.id g =
      TensorProduct.map LinearMap.id g ∘ₗ TensorProduct.map σ LinearMap.id := by
    calc
      TensorProduct.map σ LinearMap.id ∘ₗ TensorProduct.map LinearMap.id g
          = TensorProduct.map (σ ∘ₗ LinearMap.id) (LinearMap.id ∘ₗ g) := by
        rw [TensorProduct.map_comp]
      _ = TensorProduct.map σ g := by simp
      _ = TensorProduct.map (LinearMap.id ∘ₗ σ) (g ∘ₗ LinearMap.id) := by simp
      _ = TensorProduct.map LinearMap.id g ∘ₗ TensorProduct.map σ LinearMap.id := by
        rw [← TensorProduct.map_comp]
  have hy_eq : TensorProduct.map σ₁ LinearMap.id y = TensorProduct.map σ₂ LinearMap.id y := by
    dsimp [y]
    calc
      TensorProduct.map σ₁ LinearMap.id (TensorProduct.map LinearMap.id g x)
          = (TensorProduct.map σ₁ LinearMap.id ∘ₗ TensorProduct.map LinearMap.id g) x := rfl
      _ = (TensorProduct.map LinearMap.id g ∘ₗ TensorProduct.map σ₁ LinearMap.id) x := by rw [h_comm]
      _ = TensorProduct.map LinearMap.id g (TensorProduct.map σ₁ LinearMap.id x) := rfl
      _ = TensorProduct.map LinearMap.id g (TensorProduct.map σ₂ LinearMap.id x) := by rw [h_eq]
      _ = (TensorProduct.map LinearMap.id g ∘ₗ TensorProduct.map σ₂ LinearMap.id) x := rfl
      _ = (TensorProduct.map σ₂ LinearMap.id ∘ₗ TensorProduct.map LinearMap.id g) x := by rw [h_comm]
      _ = TensorProduct.map σ₂ LinearMap.id (TensorProduct.map LinearMap.id g x) := rfl
      _ = TensorProduct.map σ₂ LinearMap.id y := by rw [hy_def]
  let πR₁ (j : Fin n) : E.R₁ ⊗[E.R₀] (Fin n → E.R₀) →ₗ[E.R₀] E.R₁ :=
    (LinearMap.proj j).comp (TensorProduct.piScalarRightHom E.R₀ E.R₀ E.R₁ (Fin n))
  let πR₂ (j : Fin n) : E.R₂ ⊗[E.R₀] (Fin n → E.R₀) →ₗ[E.R₀] E.R₂ :=
    (LinearMap.proj j).comp (TensorProduct.piScalarRightHom E.R₀ E.R₀ E.R₂ (Fin n))
  have hπR₁_tmul (j : Fin n) (r : E.R₁) (v : Fin n → E.R₀) :
      πR₁ j (r ⊗ₜ[E.R₀] v) = (v j) • r := by
    simp [πR₁, TensorProduct.piScalarRightHom_tmul]
  have hπR₂_tmul (j : Fin n) (r : E.R₂) (v : Fin n → E.R₀) :
      πR₂ j (r ⊗ₜ[E.R₀] v) = (v j) • r := by
    simp [πR₂, TensorProduct.piScalarRightHom_tmul]
  have hπ_natural (j : Fin n) (σ : E.R₁ →ₗ[E.R₀] E.R₂)
      (z : E.R₁ ⊗[E.R₀] (Fin n → E.R₀)) :
      πR₂ j (TensorProduct.map σ LinearMap.id z) = σ (πR₁ j z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r v =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, hπR₂_tmul, hπR₁_tmul]
      exact (σ.map_smul (v j) r).symm
    | add x y hx hy => simp [map_add, hx, hy]
  have hπ_eq (j : Fin n) (z : E.R₁ ⊗[E.R₀] (Fin n → E.R₀)) :
      (TensorProduct.piScalarRight E.R₀ E.R₀ E.R₁ (Fin n) z) j = πR₁ j z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r v => simp [πR₁, TensorProduct.piScalarRightHom_tmul]
    | add x y hx hy => simp only [map_add, Pi.add_apply]; rw [hx, hy]
  classical
  have hconst : ∀ j : Fin n, ∃ a : E.R₀, πR₁ j y = E.π₀ a := by
    intro j
    have hj : σ₁ (πR₁ j y) = σ₂ (πR₁ j y) := by
      rw [← hπ_natural j σ₁ y, ← hπ_natural j σ₂ y]
      exact congr_arg (πR₂ j) hy_eq
    have heq : E.π₁ (πR₁ j y) = E.π₂ (πR₁ j y) := hj
    rcases hEq.2 (⟨πR₁ j y, by rw [RingHom.mem_eqLocus]; exact heq⟩ : E.π₁.eqLocus E.π₂) with ⟨a, ha⟩
    exact ⟨a, (congr_arg Subtype.val ha).symm⟩
  let q : Fin n → E.R₀ := fun j => Classical.choose (hconst j)
  have hq (j : Fin n) : πR₁ j y = E.π₀ (q j) := Classical.choose_spec (hconst j)
  have hsmul_one (a : E.R₀) : a • (1 : E.R₁) = E.π₀ a := by
    change E.π₀ a * (1 : E.R₁) = E.π₀ a; rw [mul_one]
  have hy_const : y = (1 : E.R₁) ⊗ₜ[E.R₀] q := by
    apply (TensorProduct.piScalarRight E.R₀ E.R₀ E.R₁ (Fin n)).injective
    ext j
    rw [hπ_eq j y, hπ_eq j ((1 : E.R₁) ⊗ₜ[E.R₀] q), hq j, hπR₁_tmul, hsmul_one]
  refine ⟨f q, ?_⟩
  rw [← h_recover x, ← hy_def, hy_const]
  rw [TensorProduct.map_tmul]
  simp

private lemma one_tmul_injective_of_equalizer
    (hπ₀ : Function.Injective E.π₀)
    (P : Type*) [AddCommGroup P] [Module E.R₀ P]
    [Module.Finite E.R₀ P] [Module.Projective E.R₀ P] :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    Function.Injective (fun p : P => (1 : E.R₁) ⊗ₜ[E.R₀] p) := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  intro p q hpq
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective E.R₀ P
  have hg_tensor :
      (1 : E.R₁) ⊗ₜ[E.R₀] (g p) = (1 : E.R₁) ⊗ₜ[E.R₀] (g q) := by
    simpa [TensorProduct.map_tmul] using congr_arg (TensorProduct.map LinearMap.id g) hpq
  have hg : g p = g q := by
    ext j
    have hj := congr_fun (congr_arg (TensorProduct.piScalarRight E.R₀ E.R₀ E.R₁ (Fin n)) hg_tensor) j
    have hleft : ((TensorProduct.piScalarRight E.R₀ E.R₀ E.R₁ (Fin n))
        ((1 : E.R₁) ⊗ₜ[E.R₀] (g p))) j = E.π₀ ((g p) j) := by
      simp [TensorProduct.piScalarRightHom_tmul,
        show (algebraMap E.R₀ E.R₁) = E.π₀ by rfl, Algebra.smul_def]
    have hright : ((TensorProduct.piScalarRight E.R₀ E.R₀ E.R₁ (Fin n))
        ((1 : E.R₁) ⊗ₜ[E.R₀] (g q))) j = E.π₀ ((g q) j) := by
      simp [TensorProduct.piScalarRightHom_tmul,
        show (algebraMap E.R₀ E.R₁) = E.π₀ by rfl, Algebra.smul_def]
    rw [hleft, hright] at hj
    exact hπ₀ hj
  calc
    p = (f.comp g) p := by rw [hfg]; rfl
    _ = f (g p) := rfl
    _ = f (g q) := by rw [hg]
    _ = (f.comp g) q := rfl
    _ = q := by rw [hfg]; rfl

private lemma homBaseChange_symm_fixed_raw
    (M N : Type u) [AddCommGroup M] [Module E.R₀ M] [Module.Finite E.R₀ M]
    [Module.Projective E.R₀ M] [AddCommGroup N] [Module E.R₀ N] [Module.Finite E.R₀ N]
    [Module.Projective E.R₀ N]
    (F : constantDescentDatum E M ⟶ constantDescentDatum E N) :
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    let x := (homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁).symm F.toLinearMap
    (constantDescentDatum E (M →ₗ[E.R₀] N)).φ
        (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
         (1 : E.R₂) ⊗ₜ[E.R₁] x) =
      (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra;
       (1 : E.R₂) ⊗ₜ[E.R₁] x) := by
  letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
  let H := homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁
  let x := H.symm F.toLinearMap
  let Mdd : DescentDatum E.toCosimplicialRing := constantDescentDatum E M
  let Ndd : DescentDatum E.toCosimplicialRing := constantDescentDatum E N
  have hFfixed := (DescentDatum.hom_iff_eq_φ (C := E.toCosimplicialRing)
    (M := Mdd) (N := Ndd) (f := F.toLinearMap)).mp F.commute_φ
  have hcomm := constantDescentDatum_internalHom_inv_commute_φ (E := E) M N
  have happ := LinearMap.congr_fun hcomm
    (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
     (1 : E.R₂) ⊗ₜ[E.R₁] F.toLinearMap)
  simp only [LinearMap.comp_apply] at happ
  change ((constantDescentDatum E M).internalHom (constantDescentDatum E N)).φ
    (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
     (1 : E.R₂) ⊗ₜ[E.R₁] F.toLinearMap) =
    (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra;
     (1 : E.R₂) ⊗ₜ[E.R₁] F.toLinearMap) at hFfixed
  change (constantDescentDatum E (M →ₗ[E.R₀] N)).φ
      (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
       (LinearMap.baseChange E.R₂ (homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁).symm.toLinearMap)
          ((1 : E.R₂) ⊗ₜ[E.R₁] F.toLinearMap)) =
    (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra;
     (LinearMap.baseChange E.R₂ (homBaseChangeEquiv (R := E.R₀) (M := M) (N := N) E.R₁).symm.toLinearMap)
      (((constantDescentDatum E M).internalHom (constantDescentDatum E N)).φ
        (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra;
         (1 : E.R₂) ⊗ₜ[E.R₁] F.toLinearMap))) at happ
  rw [hFfixed] at happ
  simpa [LinearMap.baseChange_tmul] using happ

/-- If `R₀` is the equalizer of the two face maps `R₁ → R₂`, then the constant
 descent datum functor is fully faithful. -/
noncomputable def constantDescentDatumFunctor_fullyFaithful
    (hEq : Function.Bijective (equalizerMap E)) :
    (constantDescentDatumFunctor E).FullyFaithful := by
  let Ftor := constantDescentDatumFunctor E
  have hπ₀ : Function.Injective E.π₀ := by
    intro a b h
    apply hEq.1
    exact Subtype.ext h
  have hFull : Ftor.Full := by
    constructor
    intro M N F
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    let H := homBaseChangeEquiv (R := E.R₀) (M := M.M) (N := N.M) E.R₁
    let x := H.symm F.toLinearMap
    have hx_fixed : (constantDescentDatum E (M.M →ₗ[E.R₀] N.M)).φ
        (letI : Algebra E.R₁ E.R₂ := E.π₁.toAlgebra
         (1 : E.R₂) ⊗ₜ[E.R₁] x) =
        (letI : Algebra E.R₁ E.R₂ := E.π₂.toAlgebra
         (1 : E.R₂) ⊗ₜ[E.R₁] x) := by
      exact homBaseChange_symm_fixed_raw E M.M N.M F
    let ex := equalizer_of_φ_fixed E hEq (M.M →ₗ[E.R₀] N.M) x hx_fixed
    refine ⟨Classical.choose ex, ?_⟩
    apply DescentDatum.hom_ext
    change LinearMap.baseChange E.R₁ (Classical.choose ex) = F.toLinearMap
    have hchoose := Classical.choose_spec ex
    have hH := congr_arg H hchoose
    dsimp [x] at hH
    rw [LinearEquiv.apply_symm_apply] at hH
    simp [H, homBaseChangeEquiv_tmul] at hH
    exact hH.symm
  have hFaithful : Ftor.Faithful := by
    constructor
    intro M N f g hfg
    letI : Algebra E.R₀ E.R₁ := E.π₀.toAlgebra
    let f₀ : M.M →ₗ[E.R₀] N.M := f
    let g₀ : M.M →ₗ[E.R₀] N.M := g
    have hlin : LinearMap.baseChange E.R₁ f₀ = LinearMap.baseChange E.R₁ g₀ := by
      simpa [Ftor, constantDescentDatumFunctor, constantDescentDatumMap] using
        congr_arg DescentDatum.Hom.toLinearMap hfg
    let H := homBaseChangeEquiv (R := E.R₀) (M := M.M) (N := N.M) E.R₁
    have htensor : (1 : E.R₁) ⊗ₜ[E.R₀] f₀ = (1 : E.R₁) ⊗ₜ[E.R₀] g₀ := by
      apply H.injective
      simpa [H, homBaseChangeEquiv_tmul] using hlin
    exact one_tmul_injective_of_equalizer E hπ₀ (M.M →ₗ[E.R₀] N.M) htensor
  letI : Ftor.Full := hFull
  letI : Ftor.Faithful := hFaithful
  exact Functor.FullyFaithful.ofFullyFaithful Ftor

end Novikov.Descent.Abstract
