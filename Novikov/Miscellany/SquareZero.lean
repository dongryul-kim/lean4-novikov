import Novikov.Miscellany.Projective
import Novikov.Miscellany.BaseChange
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.CategoryTheory.Iso
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Idempotents

namespace Novikov.Miscellany

open CategoryTheory LinearMap TensorProduct

universe u

section Reduction

variable {A B : Type u} [CommRing A] [CommRing B]
variable {M : Type*} [AddCommGroup M] [Module A M]

/-- The canonical map from a module to its base change. -/
noncomputable def reductionMap (q : A →+* B) (M : Type*) [AddCommGroup M] [Module A M] :
    M →ₗ[A] baseChange_along q M := by
  letI : Algebra A B := q.toAlgebra
  exact TensorProduct.mk A B M 1

@[simp]
theorem reductionMap_apply (q : A →+* B) (m : M) :
    reductionMap q M m =
      (letI : Algebra A B := q.toAlgebra; (1 : B) ⊗ₜ[A] m) := rfl

/-- The canonical map to a base change along a surjective ring map is surjective. -/
theorem reductionMap_surjective (q : A →+* B) (hq : Function.Surjective q) :
    Function.Surjective (reductionMap q M) := by
  letI : Algebra A B := q.toAlgebra
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, by rw [map_add]⟩
  | tmul b m =>
      obtain ⟨a, rfl⟩ := hq b
      refine ⟨a • m, ?_⟩
      rw [reductionMap_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      change (q a * 1) ⊗ₜ[A] m = q a ⊗ₜ[A] m
      rw [mul_one]

private noncomputable def quotientKerAlgEquiv (q : A →+* B)
    (hq : Function.Surjective q) :
    letI : Algebra A B := q.toAlgebra
    (A ⧸ RingHom.ker q) ≃ₐ[A] B := by
  letI : Algebra A B := q.toAlgebra
  exact AlgEquiv.ofRingEquiv
    (R := A) (f := RingHom.quotientKerEquivOfSurjective hq) (by
      intro a
      change q a = q a
      rfl)

/-- The kernel of the canonical map to a base change along a surjective ring map. -/
theorem reductionMap_ker (q : A →+* B) (hq : Function.Surjective q) :
    LinearMap.ker (reductionMap q M) = RingHom.ker q • (⊤ : Submodule A M) := by
  letI : Algebra A B := q.toAlgebra
  let e : ((A ⧸ RingHom.ker q) ⊗[A] M) ≃ₗ[A] B ⊗[A] M :=
    (quotientKerAlgEquiv q hq).toLinearEquiv.rTensor M
  have he (m : M) :
      e (reductionMap (Ideal.Quotient.mk (RingHom.ker q)) M m) = reductionMap q M m := by
    rw [reductionMap_apply, reductionMap_apply]
    change ((quotientKerAlgEquiv q hq).toLinearEquiv.rTensor M) (1 ⊗ₜ[A] m) =
      1 ⊗ₜ[A] m
    rw [LinearEquiv.rTensor_tmul]
    change (quotientKerAlgEquiv q hq) 1 ⊗ₜ[A] m = 1 ⊗ₜ[A] m
    rw [map_one]
  rw [← LinearMap.ker_tensorProductMk (Q := M) (I := RingHom.ker q)]
  ext m
  simp only [LinearMap.mem_ker]
  constructor
  · intro hm
    change reductionMap (Ideal.Quotient.mk (RingHom.ker q)) M m = 0
    apply e.injective
    calc
      e (reductionMap (Ideal.Quotient.mk (RingHom.ker q)) M m) =
          reductionMap q M m := he m
      _ = 0 := hm
      _ = e 0 := (map_zero e).symm
  · intro hm
    change reductionMap (Ideal.Quotient.mk (RingHom.ker q)) M m = 0 at hm
    calc
      reductionMap q M m =
          e (reductionMap (Ideal.Quotient.mk (RingHom.ker q)) M m) := (he m).symm
      _ = e 0 := congrArg e hm
      _ = 0 := map_zero e

/-- A map whose base change is zero has image in the kernel ideal times the target. -/
theorem range_le_ker_smul_of_baseChangeMap_eq_zero
    {N : Type*} [AddCommGroup N] [Module A N]
    (q : A →+* B) (hq : Function.Surjective q) (u : M →ₗ[A] N)
    (hu : baseChangeMap q u = 0) :
    u.range ≤ RingHom.ker q • (⊤ : Submodule A N) := by
  rw [← reductionMap_ker q hq]
  rintro _ ⟨m, rfl⟩
  change reductionMap q N (u m) = 0
  calc
    reductionMap q N (u m) = baseChangeMap q u (reductionMap q M m) := by
      rw [reductionMap_apply, reductionMap_apply, baseChangeMap_tmul]
    _ = 0 := by rw [hu, LinearMap.zero_apply]

/-- Over a square-zero extension, the composite of two maps vanishing after
base change is zero. -/
theorem comp_eq_zero_of_baseChangeMap_eq_zero
    {L N : Type*} [AddCommGroup L] [Module A L]
    [AddCommGroup N] [Module A N]
    (q : A →+* B) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (u : M →ₗ[A] N) (v : L →ₗ[A] M)
    (hu : baseChangeMap q u = 0) (hv : baseChangeMap q v = 0) :
    u.comp v = 0 := by
  let K := RingHom.ker q
  have hu_range : u.range ≤ K • (⊤ : Submodule A N) :=
    range_le_ker_smul_of_baseChangeMap_eq_zero q hq u hu
  have hv_range : v.range ≤ K • (⊤ : Submodule A M) :=
    range_le_ker_smul_of_baseChangeMap_eq_zero q hq v hv
  apply LinearMap.ext
  intro x
  have hvx : v x ∈ K • (⊤ : Submodule A M) :=
    hv_range (LinearMap.mem_range_self v x)
  have hux : u (v x) ∈ Submodule.map u (K • (⊤ : Submodule A M)) :=
    Submodule.mem_map_of_mem (f := u) hvx
  rw [Submodule.map_smul'', Submodule.map_top] at hux
  have hux' : u (v x) ∈ K • (K • (⊤ : Submodule A N)) :=
    (Submodule.smul_mono (I := K) (J := K) le_rfl hu_range) hux
  have hK : K * K = ⊥ := by
    simpa only [K, pow_two] using hq_sq
  have hzero : K • (K • (⊤ : Submodule A N)) = ⊥ :=
    calc
      K • (K • (⊤ : Submodule A N)) = (K * K) • (⊤ : Submodule A N) :=
        (Submodule.mul_smul K K (⊤ : Submodule A N)).symm
      _ = (⊥ : Ideal A) • (⊤ : Submodule A N) := congrArg (fun J : Ideal A =>
        J • (⊤ : Submodule A N)) hK
      _ = ⊥ := by simp
  change u (v x) = 0
  rw [hzero] at hux'
  simpa using hux'

/-- Base change of a linear equivalence along a ring homomorphism, with the
algebra structure induced by that homomorphism. -/
noncomputable def baseChangeLinearEquiv (q : A →+* B)
    {N : Type*} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) :
    baseChange_along q M ≃ₗ[B] baseChange_along q N := by
  letI : Algebra A B := q.toAlgebra
  exact LinearEquiv.baseChange A B M N e

@[simp]
theorem baseChangeLinearEquiv_tmul (q : A →+* B)
    {N : Type*} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N)
    (b : B) (m : M) :
    baseChangeLinearEquiv q e
      (letI : Algebra A B := q.toAlgebra; b ⊗ₜ[A] m) =
      (letI : Algebra A B := q.toAlgebra; b ⊗ₜ[A] e m) := by
  letI : Algebra A B := q.toAlgebra
  exact LinearEquiv.baseChange_tmul
    (R := A) (A := B) (M := M) (N := N) (e := e) b m

/-- An equivalence after a surjective square-zero base change between
projective modules lifts to an equivalence before base change. -/
theorem exists_linearEquiv_lift_of_surjective_of_ker_sq
    {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Projective A M] [Module.Projective A N]
    (q : A →+* B) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (eBar : baseChange_along q M ≃ₗ[B] baseChange_along q N) :
    ∃ e : M ≃ₗ[A] N, baseChangeLinearEquiv q e = eBar := by
  letI : Algebra A B := q.toAlgebra
  let targetF : M →ₗ[A] B ⊗[A] N :=
    eBar.toLinearMap.restrictScalars A ∘ₗ reductionMap q M
  obtain ⟨f, hf⟩ := Module.projective_lifting_property
    (reductionMap q N) targetF (reductionMap_surjective q hq)
  have hf_base : baseChangeMap q f = eBar.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b m
    have hfm := LinearMap.congr_fun hf m
    change reductionMap q N (f m) = eBar (reductionMap q M m) at hfm
    rw [reductionMap_apply, reductionMap_apply] at hfm
    calc
      baseChangeMap q f (b ⊗ₜ[A] m) = b ⊗ₜ[A] f m := baseChangeMap_tmul q f b m
      _ = b • ((1 : B) ⊗ₜ[A] f m) := TensorProduct.tmul_eq_smul_one_tmul b (f m)
      _ = b • eBar ((1 : B) ⊗ₜ[A] m) := congrArg (fun z => b • z) hfm
      _ = eBar (b • ((1 : B) ⊗ₜ[A] m)) := (eBar.map_smul b _).symm
      _ = eBar (b ⊗ₜ[A] m) := congrArg eBar
        (TensorProduct.tmul_eq_smul_one_tmul b m).symm
  let targetG : N →ₗ[A] B ⊗[A] M :=
    eBar.symm.toLinearMap.restrictScalars A ∘ₗ reductionMap q N
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    (reductionMap q M) targetG (reductionMap_surjective q hq)
  have hg_base : baseChangeMap q g = eBar.symm.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b n
    have hgn := LinearMap.congr_fun hg n
    change reductionMap q M (g n) = eBar.symm (reductionMap q N n) at hgn
    rw [reductionMap_apply, reductionMap_apply] at hgn
    calc
      baseChangeMap q g (b ⊗ₜ[A] n) = b ⊗ₜ[A] g n := baseChangeMap_tmul q g b n
      _ = b • ((1 : B) ⊗ₜ[A] g n) := TensorProduct.tmul_eq_smul_one_tmul b (g n)
      _ = b • eBar.symm ((1 : B) ⊗ₜ[A] n) := congrArg (fun z => b • z) hgn
      _ = eBar.symm (b • ((1 : B) ⊗ₜ[A] n)) := (eBar.symm.map_smul b _).symm
      _ = eBar.symm (b ⊗ₜ[A] n) := congrArg eBar.symm
        (TensorProduct.tmul_eq_smul_one_tmul b n).symm
  let a : M →ₗ[A] M := g.comp f - LinearMap.id
  let b : N →ₗ[A] N := f.comp g - LinearMap.id
  have ha_base : baseChangeMap q a = 0 := by
    change LinearMap.baseChange B (g.comp f - LinearMap.id) = 0
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_comp,
      LinearMap.baseChange_id]
    change baseChangeMap q g ∘ₗ baseChangeMap q f - LinearMap.id = 0
    rw [hg_base, hf_base]
    ext x
    simp
  have hb_base : baseChangeMap q b = 0 := by
    change LinearMap.baseChange B (f.comp g - LinearMap.id) = 0
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_comp,
      LinearMap.baseChange_id]
    change baseChangeMap q f ∘ₗ baseChangeMap q g - LinearMap.id = 0
    rw [hf_base, hg_base]
    ext x
    simp
  have haa : a.comp a = 0 :=
    comp_eq_zero_of_baseChangeMap_eq_zero q hq hq_sq a a ha_base ha_base
  have hbb : b.comp b = 0 :=
    comp_eq_zero_of_baseChangeMap_eq_zero q hq hq_sq b b hb_base hb_base
  have hgf : g.comp f = LinearMap.id + a := by
    simp only [a]
    abel
  have hfg : f.comp g = LinearMap.id + b := by
    simp only [b]
    abel
  have hfa : f.comp a = b.comp f := by
    ext x
    simp [a, b, LinearMap.comp_apply]
  have haa_apply (x : M) : a (a x) = 0 := by
    exact LinearMap.congr_fun haa x
  have hbb_apply (x : N) : b (b x) = 0 := by
    exact LinearMap.congr_fun hbb x
  have hgf_apply (x : M) : g (f x) = x + a x :=
    LinearMap.congr_fun hgf x
  have hfg_apply (x : N) : f (g x) = x + b x :=
    LinearMap.congr_fun hfg x
  have hfa_apply (x : M) : f (a x) = b (f x) :=
    LinearMap.congr_fun hfa x
  let g' : N →ₗ[A] M := (LinearMap.id - a).comp g
  have hg'f : g'.comp f = LinearMap.id := by
    ext x
    change ((LinearMap.id : M →ₗ[A] M) - a) (g (f x)) = x
    rw [hgf_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_add]
    rw [haa_apply]
    abel
  have hfg' : f.comp g' = LinearMap.id := by
    ext x
    change f (((LinearMap.id : M →ₗ[A] M) - a) (g x)) = x
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    rw [hfa_apply, hfg_apply, map_add, hbb_apply]
    abel
  let e : M ≃ₗ[A] N := LinearEquiv.ofLinear f g' hfg' hg'f
  refine ⟨e, ?_⟩
  apply LinearEquiv.ext
  intro x
  change baseChangeMap q f x = eBar x
  exact LinearMap.congr_fun hf_base x

private theorem mapMatrix_surjective (q : A →+* B) (hq : Function.Surjective q)
    (n : ℕ) : Function.Surjective
      (q.mapMatrix : Matrix (Fin n) (Fin n) A → Matrix (Fin n) (Fin n) B) := by
  classical
  intro X
  choose Y hY using fun i j => hq (X i j)
  refine ⟨fun i j => Y i j, ?_⟩
  ext i j
  simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hY i j

private theorem mapMatrix_ker_isNilpotent (q : A →+* B)
    (hq_sq : RingHom.ker q ^ 2 = ⊥) (n : ℕ) :
    ∀ X ∈ RingHom.ker
      (q.mapMatrix : Matrix (Fin n) (Fin n) A →+* Matrix (Fin n) (Fin n) B),
      IsNilpotent X := by
  classical
  intro X hX
  have hX_entry (i j : Fin n) : q (X i j) = 0 := by
    have h := congr_fun (congr_fun hX i) j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using h
  have hK : RingHom.ker q * RingHom.ker q = ⊥ := by
    simpa only [pow_two] using hq_sq
  refine ⟨2, ?_⟩
  rw [pow_two]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hik : X i k ∈ RingHom.ker q := hX_entry i k
  have hkj : X k j ∈ RingHom.ker q := hX_entry k j
  have hprod : X i k * X k j ∈ RingHom.ker q * RingHom.ker q :=
    Ideal.mul_mem_mul hik hkj
  rw [hK] at hprod
  simpa using hprod

private theorem piScalarRight_baseChange_toLin (q : A →+* B) {n : ℕ}
    (e : Matrix (Fin n) (Fin n) A) :
    letI : Algebra A B := q.toAlgebra
    let κ := TensorProduct.piScalarRight A B B (Fin n)
    κ.toLinearMap ∘ₗ baseChangeMap q (Matrix.toLinAlgEquiv' e) =
      Matrix.toLinAlgEquiv' (q.mapMatrix e) ∘ₗ κ.toLinearMap := by
  classical
  letI : Algebra A B := q.toAlgebra
  let κ := TensorProduct.piScalarRight A B B (Fin n)
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.comp_apply, hx, hy]
  | tmul b v =>
      simp only [LinearMap.comp_apply, baseChangeMap_tmul]
      change TensorProduct.piScalarRightHom A B B (Fin n)
          (b ⊗ₜ[A] Matrix.toLinAlgEquiv' e v) =
        Matrix.toLinAlgEquiv' (q.mapMatrix e)
          (TensorProduct.piScalarRightHom A B B (Fin n) (b ⊗ₜ[A] v))
      rw [TensorProduct.piScalarRightHom_tmul,
        TensorProduct.piScalarRightHom_tmul]
      rw [Matrix.toLinAlgEquiv'_apply, RingHom.mapMatrix_apply]
      ext i
      change q (Matrix.mulVec e v i) * b =
        Matrix.mulVec (e.map q) (fun j => q (v j) * b) i
      rw [RingHom.map_mulVec q e v i]
      simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

private theorem exists_idempotent_matrix_lift (q : A →+* B)
    (hq : Function.Surjective q) (hq_sq : RingHom.ker q ^ 2 = ⊥)
    {n : ℕ} (eBar : Matrix (Fin n) (Fin n) B)
    (heBar : IsIdempotentElem eBar) :
    ∃ e : Matrix (Fin n) (Fin n) A,
      IsIdempotentElem e ∧ q.mapMatrix e = eBar := by
  apply exists_isIdempotentElem_eq_of_ker_isNilpotent
    (q.mapMatrix : Matrix (Fin n) (Fin n) A →+* Matrix (Fin n) (Fin n) B)
    (mapMatrix_ker_isNilpotent q hq_sq n) eBar
  · exact mapMatrix_surjective q hq n eBar
  · exact heBar

/-- A finite projective module over the target of a surjective square-zero ring
map lifts to a finite projective module over the source. -/
theorem FiniteProjectiveModule.exists_lift_of_surjective_of_ker_sq
    (q : A →+* B) (hq : Function.Surjective q)
    (hq_sq : RingHom.ker q ^ 2 = ⊥)
    (Q : FiniteProjectiveModule.{u, u} B) :
    ∃ P : FiniteProjectiveModule.{u, u} A,
      Nonempty (P.baseChange q ≅ Q) := by
  classical
  letI : Algebra A B := q.toAlgebra
  obtain ⟨n, rBar, iBar, _, _, hri⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective B Q.M
  let pBar : Module.End B (Fin n → B) := iBar.comp rBar
  have hpBar : IsIdempotentElem pBar := by
    rw [IsIdempotentElem]
    apply LinearMap.ext
    intro x
    change iBar (rBar (iBar (rBar x))) = iBar (rBar x)
    rw [← LinearMap.comp_apply rBar iBar, hri, LinearMap.id_apply]
  let eBar : Matrix (Fin n) (Fin n) B :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) B ≃ₐ[B]
      Module.End B (Fin n → B)).symm pBar
  have heBar : IsIdempotentElem eBar := by
    dsimp only [eBar]
    exact hpBar.map
      (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) B ≃ₐ[B]
        Module.End B (Fin n → B)).symm
  obtain ⟨e, he, heq⟩ := exists_idempotent_matrix_lift q hq hq_sq eBar heBar
  let p : Module.End A (Fin n → A) := Matrix.toLinAlgEquiv' e
  have hp : IsIdempotentElem p := by
    dsimp only [p]
    exact he.map
      (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) A ≃ₐ[A]
        Module.End A (Fin n → A))
  let proj : LinearMap.IsProj p.range p := hp.isProj_range p
  let j : p.range →ₗ[A] (Fin n → A) := p.range.subtype
  let s : (Fin n → A) →ₗ[A] p.range := proj.codRestrict
  have hsj : s.comp j = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, s, j] using
      proj.codRestrict_apply_cod x
  have hjsp : j.comp s = p := by
    simpa only [j, s] using proj.subtype_comp_codRestrict
  have hs_surjective : Function.Surjective s := by
    intro x
    exact ⟨j x, by simpa only [s, j] using proj.codRestrict_apply_cod x⟩
  let P : FiniteProjectiveModule.{u, u} A :=
    { M := p.range
      instFinite := Module.Finite.of_surjective s hs_surjective
      instProjective := Module.Projective.of_split j s hsj }
  let jB : (B ⊗[A] p.range) →ₗ[B] (B ⊗[A] (Fin n → A)) := baseChangeMap q j
  let sB : (B ⊗[A] (Fin n → A)) →ₗ[B] (B ⊗[A] p.range) := baseChangeMap q s
  have hsjB : sB.comp jB = LinearMap.id := by
    change LinearMap.baseChange B s ∘ₗ LinearMap.baseChange B j = LinearMap.id
    rw [← LinearMap.baseChange_comp, hsj, LinearMap.baseChange_id]
  have hjsB : jB.comp sB = baseChangeMap q p := by
    change LinearMap.baseChange B j ∘ₗ LinearMap.baseChange B s =
      LinearMap.baseChange B p
    rw [← LinearMap.baseChange_comp, hjsp]
  let κ : (B ⊗[A] (Fin n → A)) ≃ₗ[B] (Fin n → B) :=
    TensorProduct.piScalarRight A B B (Fin n)
  have heBar_toLin : Matrix.toLinAlgEquiv' eBar = pBar := by
    exact (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) B ≃ₐ[B]
      Module.End B (Fin n → B)).apply_symm_apply pBar
  have hconj : κ.toLinearMap.comp (baseChangeMap q p) =
      pBar.comp κ.toLinearMap := by
    have h := piScalarRight_baseChange_toLin q e
    rw [heq] at h
    change κ.toLinearMap.comp (baseChangeMap q p) =
      Matrix.toLinAlgEquiv' eBar ∘ₗ κ.toLinearMap at h
    rw [heBar_toLin] at h
    exact h
  have hsjB_apply (x : B ⊗[A] p.range) : sB (jB x) = x := by
    exact LinearMap.congr_fun hsjB x
  have hjsB_apply (x : B ⊗[A] (Fin n → A)) :
      jB (sB x) = baseChangeMap q p x := by
    exact LinearMap.congr_fun hjsB x
  have hpjB (x : B ⊗[A] p.range) : baseChangeMap q p (jB x) = jB x := by
    rw [← hjsB_apply, hsjB_apply]
  have hconj_apply (x : B ⊗[A] (Fin n → A)) :
      κ (baseChangeMap q p x) = pBar (κ x) := by
    exact LinearMap.congr_fun hconj x
  have hconj_symm (y : Fin n → B) :
      baseChangeMap q p (κ.symm y) = κ.symm (pBar y) := by
    apply κ.injective
    simpa only [κ.apply_symm_apply] using hconj_apply (κ.symm y)
  let toQ : (B ⊗[A] p.range) →ₗ[B] Q.M :=
    rBar.comp (κ.toLinearMap.comp jB)
  let fromQ : Q.M →ₗ[B] (B ⊗[A] p.range) :=
    sB.comp (κ.symm.toLinearMap.comp iBar)
  have hleft : fromQ.comp toQ = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change sB (κ.symm (iBar (rBar (κ (jB x))))) = x
    calc
      sB (κ.symm (iBar (rBar (κ (jB x))))) =
          sB (κ.symm (pBar (κ (jB x)))) := rfl
      _ = sB (baseChangeMap q p (jB x)) := by
        have h := hconj_symm (κ (jB x))
        rw [κ.symm_apply_apply] at h
        exact congrArg sB h.symm
      _ = sB (jB x) := congrArg sB (hpjB x)
      _ = x := hsjB_apply x
  have hright : toQ.comp fromQ = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change rBar (κ (jB (sB (κ.symm (iBar x))))) = x
    calc
      rBar (κ (jB (sB (κ.symm (iBar x))))) =
          rBar (κ (baseChangeMap q p (κ.symm (iBar x)))) :=
        congrArg (fun z => rBar (κ z)) (hjsB_apply (κ.symm (iBar x)))
      _ = rBar (pBar (κ (κ.symm (iBar x)))) :=
        congrArg rBar (hconj_apply (κ.symm (iBar x)))
      _ = rBar (pBar (iBar x)) := by rw [κ.apply_symm_apply]
      _ = rBar (iBar (rBar (iBar x))) := rfl
      _ = rBar (iBar x) := by
        rw [← LinearMap.comp_apply rBar iBar, hri, LinearMap.id_apply]
      _ = x := by
        rw [← LinearMap.comp_apply rBar iBar, hri, LinearMap.id_apply]
  let equiv : (B ⊗[A] p.range) ≃ₗ[B] Q.M :=
    LinearEquiv.ofLinear toQ fromQ hright hleft
  let iso : P.baseChange q ≅ Q :=
    { hom := equiv.toLinearMap
      inv := equiv.symm.toLinearMap
      hom_inv_id := by
        change equiv.symm.toLinearMap.comp equiv.toLinearMap = LinearMap.id
        apply LinearMap.ext
        intro x
        exact equiv.symm_apply_apply x
      inv_hom_id := by
        change equiv.toLinearMap.comp equiv.symm.toLinearMap = LinearMap.id
        apply LinearMap.ext
        intro x
        exact equiv.apply_symm_apply x }
  exact ⟨P, ⟨iso⟩⟩

/-- An equivalence of projective modules modulo a square-zero ideal lifts to an
equivalence before taking the quotient.  This is the first clause of
`Lem:VectSquareZeroDeform`. -/
theorem exists_linearEquiv_lift_of_quotient_sq
    {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Projective A M] [Module.Projective A N]
    (I : Ideal A) (hI : I ^ 2 = ⊥)
    (eBar :
      letI : Algebra A (A ⧸ I) := (Ideal.Quotient.mk I).toAlgebra
      ((A ⧸ I) ⊗[A] M) ≃ₗ[A ⧸ I] ((A ⧸ I) ⊗[A] N)) :
    ∃ e : M ≃ₗ[A] N,
      baseChangeLinearEquiv (Ideal.Quotient.mk I) e = eBar := by
  apply exists_linearEquiv_lift_of_surjective_of_ker_sq
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  simpa only [Ideal.mk_ker] using hI

/-- A finite projective module modulo a square-zero ideal lifts to a finite
projective module before taking the quotient.  This is the second clause of
`Lem:VectSquareZeroDeform`. -/
theorem FiniteProjectiveModule.exists_lift_of_quotient_sq
    (I : Ideal A) (hI : I ^ 2 = ⊥)
    (Q : FiniteProjectiveModule.{u, u} (A ⧸ I)) :
    ∃ P : FiniteProjectiveModule.{u, u} A,
      Nonempty (P.baseChange (Ideal.Quotient.mk I) ≅ Q) := by
  apply FiniteProjectiveModule.exists_lift_of_surjective_of_ker_sq
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  simpa only [Ideal.mk_ker] using hI

end Reduction

end Novikov.Miscellany
