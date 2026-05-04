import Novikov.Miscellany.Split
import Novikov.Series.Module
import Novikov.Series.OneVar
import Novikov.Isocrystal.Frobenius
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.FinitePresentation

/-! # Descent of finite projectivity along Novikov series

This file shows that if `M` is an `A`-module such that `RealNovikovSeries M` is
a finite projective `RealNovikovSeries A`-module whose canonical topology agrees
with the natural topology, then `M` itself is a finite projective `A`-module.

The agreement of the canonical topology with the natural one is encoded as the
hypothesis that every `RealNovikovSeries A`-linear map
`RealNovikovSeries M → RealNovikovSeries A` is continuous, which is the
direction of the agreement that the proofs in this file rely on.
-/

namespace Novikov

variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]

/-- Auxiliary: if `a` is a one-variable Novikov series in `A` supported on the
non-negative half-line (i.e. lies in `filtration Γ A 0`), then for any one-variable
Novikov series `x` in `M` and exponent `d`, the value `(a • x) d` lies in the
`A`-span of the values of `x` at exponents at most `d ()`. -/
private lemma novikovSMul_apply_mem_span_below
    {Γ : AddSubgroup ℝ} (a : OneVarNovikovSeries Γ A) (x : OneVarNovikovSeries Γ M)
    (ha : a ∈ filtration Γ A 0) (d : Unit → Γ) :
    (a • x : OneVarNovikovSeries Γ M) d ∈
      Submodule.span A ((fun q : Unit → Γ => (x : (Unit → Γ) → M) q) ''
        {q | (q () : ℝ) ≤ (d () : ℝ)}) := by
  rw [novikovSMul_val]
  change novikovSeriesMulFun a x (_root_.smulAddHom A M) d ∈ _
  simp only [novikovSeriesMulFun]
  apply Submodule.sum_mem
  rintro p hp
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hp
  obtain ⟨h_sum, ha_nz, _hx_nz⟩ := hp
  change (_root_.smulAddHom A M) (a p.1) (x p.2) ∈ _
  rw [_root_.smulAddHom_apply]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨p.2, ?_, rfl⟩
  have ha_nonneg : (0 : ℝ) ≤ (p.1 () : ℝ) := by
    by_contra h_neg
    push Not at h_neg
    exact ha_nz (ha p.1 h_neg)
  have h_eq : (p.1 () : ℝ) + (p.2 () : ℝ) = (d () : ℝ) := by
    have h := congr_fun h_sum ()
    have h' := congr_arg (fun y : Γ => (y : ℝ)) h
    change (p.1 () : ℝ) + (p.2 () : ℝ) = (d () : ℝ) at h'
    exact h'
  change (p.2 () : ℝ) ≤ (d () : ℝ)
  linarith

/-- Under the hypothesis that `RealNovikovSeries M` is a finite projective
`RealNovikovSeries A`-module whose canonical topology agrees with the natural
topology, the `A`-module `M` is finitely generated. -/
lemma module_finite_of_realNovikovSeries
    [Module.Finite (RealNovikovSeries A) (RealNovikovSeries M)]
    [Module.Projective (RealNovikovSeries A) (RealNovikovSeries M)]
    (h_canonical : ∀ (f : RealNovikovSeries M →ₗ[RealNovikovSeries A]
        RealNovikovSeries A), Continuous f) :
    Module.Finite A M := by
  classical
  set R := RealNovikovSeries A with hR_def
  -- Step 1: Get a finite presentation `π` of `RealNovikovSeries M` and a
  -- splitting `σ` from the projective hypothesis.
  obtain ⟨n, π, σ, hπ_surj, hσ_inj, hπσ⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R (RealNovikovSeries M)
  -- Step 2: Each component of `σ` is `R`-linear, hence continuous.
  let σi : Fin n → (RealNovikovSeries M →ₗ[R] R) := fun i => (LinearMap.proj i).comp σ
  have hσi_cont : ∀ i, Continuous (σi i) := fun i => h_canonical (σi i)
  -- Step 3: Therefore `σ` itself is continuous.
  have hσ_cont : Continuous σ := continuous_pi (fun i => hσi_cont i)
  -- Step 4: For each `i`, find a filtration depth that maps into `filtration ⊤ A 0`.
  have h_nhd_zero : ∀ i, ∃ Ni : ℝ, ∀ x ∈ filtration (⊤ : AddSubgroup ℝ) M Ni,
      σi i x ∈ filtration (⊤ : AddSubgroup ℝ) A 0 := by
    intro i
    have hbasis_A := (filtrationBasis (⊤ : AddSubgroup ℝ) A).nhds_zero_hasBasis
    have hbasis_M := (filtrationBasis (⊤ : AddSubgroup ℝ) M).nhds_zero_hasBasis
    have h0 : σi i 0 = 0 := (σi i).map_zero
    have h_at : ContinuousAt (σi i) 0 := (hσi_cont i).continuousAt
    have h_nhd : (filtration (⊤ : AddSubgroup ℝ) A 0 : Set _) ∈ nhds (0 : R) :=
      hbasis_A.mem_of_mem ⟨0, rfl⟩
    have h_pre : (σi i) ⁻¹' (filtration (⊤ : AddSubgroup ℝ) A 0 : Set _) ∈ nhds (0 : RealNovikovSeries M) := by
      have := h_at.preimage_mem_nhds (by rw [h0]; exact h_nhd)
      exact this
    obtain ⟨V, ⟨D, rfl⟩, hVsub⟩ := hbasis_M.mem_iff.mp h_pre
    exact ⟨D, fun x hx => hVsub hx⟩
  choose Ns hNs using h_nhd_zero
  -- Step 5: Take a uniform filtration depth `N` working for all components.
  obtain ⟨N, hN⟩ : ∃ N : ℝ, ∀ i x, x ∈ filtration (⊤ : AddSubgroup ℝ) M N →
      σi i x ∈ filtration (⊤ : AddSubgroup ℝ) A 0 := by
    by_cases hn : n = 0
    · refine ⟨0, ?_⟩
      intro i; subst hn; exact i.elim0
    · have hne : (Finset.univ.image Ns).Nonempty :=
        ⟨Ns ⟨0, Nat.pos_of_ne_zero hn⟩, by simp⟩
      refine ⟨(Finset.univ.image Ns).max' hne, fun i x hx => ?_⟩
      apply hNs
      have h_le : Ns i ≤ (Finset.univ.image Ns).max' hne :=
        Finset.le_max' _ _ (by simp)
      exact filtration_mono h_le hx
  -- Step 6: Generators `xi i := π (Pi.single i 1)` of `RealNovikovSeries M`.
  let xi : Fin n → RealNovikovSeries M := fun i => π (Pi.single i 1)
  have hπ_eq : ∀ v : Fin n → R, π v = ∑ i, v i • xi i := by
    intro v
    conv_lhs => rw [← (Pi.basisFun R (Fin n)).sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.basisFun_apply, Pi.basisFun_repr]
  -- Step 7: The exponent `dN` of degree `N`.
  let dN : Unit → ↥(⊤ : AddSubgroup ℝ) := fun _ => ⟨N, AddSubgroup.mem_top _⟩
  -- Step 8: `novikovMonomial m₀ dN` lies in `filtration ⊤ M N`.
  have h_monomial_filt : ∀ m₀ : M,
      (novikovMonomial m₀ dN : RealNovikovSeries M) ∈ filtration (⊤ : AddSubgroup ℝ) M N := by
    intro m₀ d hd
    have h_ne : d ≠ dN := by
      intro h_eq
      have h_d_eq : (d () : ℝ) = N := by rw [h_eq]
      linarith
    change (if d = dN then m₀ else 0) = 0
    rw [if_neg h_ne]
  -- Step 9: For each generator, the support below `N` is finite.
  have h_supp_finite : ∀ i : Fin n,
      {q : Unit → ↥(⊤ : AddSubgroup ℝ) |
        (xi i : (Unit → ↥(⊤ : AddSubgroup ℝ)) → M) q ≠ 0 ∧ (q () : ℝ) ≤ N}.Finite := by
    intro i
    have h_nov := (xi i).prop
    have hfin := h_nov (fun _ => (1 : ℝ)) (fun _ => one_pos) (N + 1)
    apply hfin.subset
    rintro d ⟨h_nz, h_le⟩
    refine ⟨h_nz, ?_⟩
    simp only [Fintype.sum_unique, one_mul]
    linarith
  -- Step 10: Assemble the finite set of candidate generators of `M`.
  let qset : Fin n → Finset (Unit → ↥(⊤ : AddSubgroup ℝ)) :=
    fun i => (h_supp_finite i).toFinset
  let G : Finset M := (Finset.univ : Finset (Fin n)).biUnion fun i =>
    (qset i).image fun q => (xi i : (Unit → ↥(⊤ : AddSubgroup ℝ)) → M) q
  -- Step 11: Show that `G` generates `M` as an `A`-module.
  refine ⟨⟨G, ?_⟩⟩
  rw [eq_top_iff]
  intro m₀ _
  -- Construct the lift `a := σ (monomial m₀ dN)`.
  set y : RealNovikovSeries M := novikovMonomial m₀ dN with hy_def
  have hy_filt : y ∈ filtration (⊤ : AddSubgroup ℝ) M N := h_monomial_filt m₀
  have h_a_filt : ∀ i, σi i y ∈ filtration (⊤ : AddSubgroup ℝ) A 0 := fun i => hN i y hy_filt
  -- We have `y = π (σ y) = ∑ i, σi i y • xi i`.
  have h_y_eq : y = ∑ i, σi i y • xi i := by
    have hπσ_y : π (σ y) = y := by
      change (π ∘ₗ σ) y = y
      rw [hπσ]; rfl
    conv_lhs => rw [← hπσ_y, hπ_eq]
    rfl
  -- Take the value at `dN` to recover `m₀`.
  have h_m_eq : m₀ = ∑ i, ((σi i y • xi i : RealNovikovSeries M) :
      (Unit → ↥(⊤ : AddSubgroup ℝ)) → M) dN := by
    have h_y_dN : (y : (Unit → ↥(⊤ : AddSubgroup ℝ)) → M) dN = m₀ := by
      change (if dN = dN then m₀ else 0) = m₀
      rw [if_pos rfl]
    have h_apply : (y : (Unit → ↥(⊤ : AddSubgroup ℝ)) → M) dN =
        (∑ i, σi i y • xi i : RealNovikovSeries M).val dN :=
      congr_arg (fun z : RealNovikovSeries M => (z : (Unit → ↥(⊤ : AddSubgroup ℝ)) → M) dN)
        h_y_eq
    rw [← h_y_dN, h_apply, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
  -- Each term lies in the `A`-span of `G`.
  rw [h_m_eq]
  apply Submodule.sum_mem
  intro i _
  have h_term : (σi i y • xi i : RealNovikovSeries M).val dN ∈
      Submodule.span A ((fun q : Unit → ↥(⊤ : AddSubgroup ℝ) =>
        (xi i : (Unit → ↥(⊤ : AddSubgroup ℝ)) → M) q) ''
        {q | (q () : ℝ) ≤ (dN () : ℝ)}) :=
    novikovSMul_apply_mem_span_below (Γ := (⊤ : AddSubgroup ℝ)) (σi i y) (xi i)
      (h_a_filt i) dN
  -- Lift to span over `G`.
  apply (Submodule.span_le.mpr ?_) h_term
  rintro - ⟨q, hq, rfl⟩
  by_cases hxq : (xi i : (Unit → ↥(⊤ : AddSubgroup ℝ)) → M) q = 0
  · change (xi i : (Unit → ↥(⊤ : AddSubgroup ℝ)) → M) q ∈ Submodule.span A (G : Set M)
    rw [hxq]; exact Submodule.zero_mem _
  · apply Submodule.subset_span
    refine Finset.mem_coe.mpr ?_
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    refine Finset.mem_image.mpr ⟨q, ?_, rfl⟩
    refine Set.Finite.mem_toFinset _ |>.mpr ?_
    exact ⟨hxq, hq⟩

/-- Under the same hypotheses as `module_finite_of_realNovikovSeries`, the
`A`-module `M` is finitely presented. The argument chooses an `A`-linear
surjection `A^m → M` from a finite set of generators of `M` and reapplies the
finitely-generated lemma to its kernel. -/
lemma module_finitePresentation_of_realNovikovSeries
    [Module.Finite (RealNovikovSeries A) (RealNovikovSeries M)]
    [Module.Projective (RealNovikovSeries A) (RealNovikovSeries M)]
    (h_canonical : ∀ (f : RealNovikovSeries M →ₗ[RealNovikovSeries A]
        RealNovikovSeries A), Continuous f) :
    Module.FinitePresentation A M := by
  haveI hM_fin : Module.Finite A M := module_finite_of_realNovikovSeries h_canonical
  -- Choose a finite set of generators of `M`, packaged as a surjection
  -- `π_M : (Fin m → A) →ₗ[A] M`.
  obtain ⟨m, π_M, hπ_M_surj⟩ := Module.Finite.exists_fin' A M
  -- The kernel `K := ker π_M` is finitely generated by the same lemma applied
  -- to `K` in place of `M`; we reduce to that statement here.
  suffices hK_fg : (LinearMap.ker π_M).FG by
    exact Module.finitePresentation_of_free_of_surjective π_M hπ_M_surj hK_fg
  set R := RealNovikovSeries A
  -- Lift `π_M` to a `R`-linear surjection `π_M_seq : (Fin m → R) → M⟦t⟧`
  -- through the natural identification `(A^m)⟦t⟧ ≃ R^m`.
  let eqA : NovikovSeries (⊤ : AddSubgroup ℝ) Unit (Fin m → A) ≃ₗ[R] (Fin m → R) :=
    novikovPiEquiv (M := A) (Γ := (⊤ : AddSubgroup ℝ)) (ι' := Fin m)
  let π_M_seq : (Fin m → R) →ₗ[R] RealNovikovSeries M :=
    (lmapNovikov (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) π_M).comp
      eqA.symm.toLinearMap
  have hπ_M_seq_surj : Function.Surjective π_M_seq :=
    (lmap_surjective π_M hπ_M_surj).comp eqA.symm.surjective
  -- Use projectivity of `RealNovikovSeries M` to get a `R`-linear splitting
  -- `σ' : RealNovikovSeries M → (Fin m → R)`.
  obtain ⟨σ', hσ'⟩ : ∃ σ' : RealNovikovSeries M →ₗ[R] (Fin m → R),
      π_M_seq ∘ₗ σ' = LinearMap.id :=
    Module.projective_lifting_property π_M_seq LinearMap.id hπ_M_seq_surj
  -- Set `K_seq := ker π_M_seq`. It is a direct summand of `R^m` via the
  -- projection `s := id - σ' ∘ π_M_seq`.
  let K_seq : Submodule R (Fin m → R) := LinearMap.ker π_M_seq
  let s : (Fin m → R) →ₗ[R] (Fin m → R) :=
    LinearMap.id - σ'.comp π_M_seq
  have hs_image : ∀ x, s x ∈ K_seq := by
    intro x
    change π_M_seq (x - σ' (π_M_seq x)) = 0
    rw [map_sub]
    have : π_M_seq (σ' (π_M_seq x)) = π_M_seq x := by
      have h := congr_arg (fun L : RealNovikovSeries M →ₗ[R] RealNovikovSeries M =>
        L (π_M_seq x)) hσ'
      simpa using h
    rw [this, sub_self]
  let s' : (Fin m → R) →ₗ[R] K_seq := LinearMap.codRestrict K_seq s hs_image
  let i_seq : K_seq →ₗ[R] (Fin m → R) := K_seq.subtype
  have h_split : s' ∘ₗ i_seq = LinearMap.id := by
    refine LinearMap.ext ?_
    rintro ⟨x, hx⟩
    apply Subtype.ext
    have hx' : π_M_seq x = 0 := hx
    change x - σ' (π_M_seq x) = x
    rw [hx', map_zero, sub_zero]
  -- `K_seq` is finite projective over `R` as a direct summand of the free `R^m`.
  haveI : Module.Free R (Fin m → R) := Module.Free.of_basis (Pi.basisFun R (Fin m))
  haveI : Module.Finite R (Fin m → R) := Module.Finite.of_basis (Pi.basisFun R (Fin m))
  haveI hKseq_proj : Module.Projective R K_seq :=
    Module.Projective.of_split i_seq s' h_split
  haveI hKseq_fin : Module.Finite R K_seq := by
    have hs'_surj : Function.Surjective s' := by
      rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      have hy' : π_M_seq y = 0 := hy
      change y - σ' (π_M_seq y) = y
      rw [hy', map_zero, sub_zero]
    exact Module.Finite.of_surjective s' hs'_surj
  -- Identify `K⟦t⟧` with `K_seq` via the natural iso through `(A^m)⟦t⟧ ≃ R^m`.
  let K : Submodule A (Fin m → A) := LinearMap.ker π_M
  have h_π_K_zero : π_M.comp K.subtype = 0 := by
    ext k; exact k.prop
  -- Forward map K⟦t⟧ → R^m, lands in K_seq
  let φ_fwd_lin : RealNovikovSeries K →ₗ[R] (Fin m → R) :=
    eqA.toLinearMap.comp (lmapNovikov (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K.subtype)
  have h_φ_fwd_in_Kseq : ∀ f, φ_fwd_lin f ∈ K_seq := by
    intro f
    change lmap π_M (eqA.symm (eqA (lmap K.subtype f))) = 0
    rw [eqA.symm_apply_apply]
    have : (lmap π_M).comp (lmap (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K.subtype) f = 0 := by
      rw [← lmap_comp, h_π_K_zero]
      ext d; rfl
    exact this
  let φ_K : RealNovikovSeries K →ₗ[R] K_seq :=
    LinearMap.codRestrict K_seq φ_fwd_lin h_φ_fwd_in_Kseq
  -- Inverse map: K_seq → K⟦t⟧.
  let ψ_K_fun : K_seq → RealNovikovSeries K := fun y =>
    let h : NovikovSeries (⊤ : AddSubgroup ℝ) Unit (Fin m → A) := eqA.symm y.val
    have h_in_K : ∀ d, h.val d ∈ K := by
      intro d
      have hy : π_M_seq y.val = 0 := y.prop
      have h0 : lmap π_M h = 0 := by
        change lmap π_M (eqA.symm y.val) = 0
        exact hy
      have := congr_arg (fun s : NovikovSeries (⊤ : AddSubgroup ℝ) Unit M => s.val d) h0
      change π_M (h.val d) = 0 at this
      exact this
    ⟨fun d => ⟨h.val d, h_in_K d⟩, by
      apply is_novikov_series_of_subset h.prop
      intro d hd h_zero
      apply hd
      apply Subtype.ext
      exact h_zero⟩
  -- φ_K is injective and surjective.
  have h_φ_K_inj : Function.Injective φ_K := by
    intro f g hfg
    apply lmap_injective (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K.subtype
      Subtype.val_injective
    apply eqA.injective
    have := congr_arg Subtype.val hfg
    exact this
  have h_φ_K_surj : Function.Surjective φ_K := by
    intro y
    refine ⟨ψ_K_fun y, ?_⟩
    apply Subtype.ext
    change eqA (lmap K.subtype (ψ_K_fun y)) = y.val
    have h_lmap_eq : lmap (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K.subtype
        (ψ_K_fun y) = eqA.symm y.val := by
      apply NovikovSeries.ext
      intro d
      rfl
    rw [h_lmap_eq, LinearEquiv.apply_symm_apply]
  -- Build LinearEquiv K⟦t⟧ ≃[R] K_seq.
  let φ_K_equiv : RealNovikovSeries K ≃ₗ[R] K_seq :=
    LinearEquiv.ofBijective φ_K ⟨h_φ_K_inj, h_φ_K_surj⟩
  -- Transfer Module.Finite and Module.Projective from K_seq to K⟦t⟧.
  haveI : Module.Finite R (RealNovikovSeries K) :=
    Module.Finite.equiv φ_K_equiv.symm
  haveI : Module.Projective R (RealNovikovSeries K) :=
    Module.Projective.of_equiv φ_K_equiv.symm
  -- Canonical-topology hypothesis on K⟦t⟧, derived from the splitting.
  have h_canonical_K : ∀ (f : RealNovikovSeries K →ₗ[R] R), Continuous f := by
    haveI : IsTopologicalRing R := Novikov.is_topological_ring
    haveI : IsTopologicalAddGroup (RealNovikovSeries K) := is_topological_add_group
    haveI : IsTopologicalAddGroup (RealNovikovSeries (Fin m → A)) := is_topological_add_group
    haveI : IsTopologicalAddGroup R := is_topological_add_group
    intro f
    let g : K_seq →ₗ[R] R := f.comp φ_K_equiv.symm.toLinearMap
    let g_ext : (Fin m → R) →ₗ[R] R := g.comp s'
    -- Lemma A: any R-linear map (Fin m → R) →ₗ[R] R is continuous (R is a topological ring)
    have h_g_ext_cont : Continuous g_ext := by
      let b := Pi.basisFun R (Fin m)
      let a : Fin m → R := fun i => g_ext (b i)
      have h_formula (v : Fin m → R) : g_ext v = ∑ i, a i * v i := by
        have hv : ∑ i, v i • b i = v := (Pi.basisFun R (Fin m)).sum_repr v
        calc
          g_ext v = g_ext (∑ i, v i • b i) := by { conv_lhs => rw [← hv] }
          _ = ∑ i, g_ext (v i • b i) := map_sum _ _ _
          _ = ∑ i, v i • g_ext (b i) := by simp only [map_smul]
          _ = ∑ i, a i * v i := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            exact mul_comm (v i) (a i)
      have h_g_ext_eq : (g_ext : (Fin m → R) → R) = (fun (v : Fin m → R) => ∑ i, a i * v i) := by
        funext v; exact h_formula v
      rw [h_g_ext_eq]
      refine continuous_finset_sum (M := R) Finset.univ (fun i _ => ?_)
      exact (continuous_const.mul (continuous_apply i))
    -- Lemma B.1: lmap is continuous (preserves filtration)
    have h_lmap_cont : Continuous (lmap (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (K.subtype : K →ₗ[A] (Fin m → A))) := by
      apply continuous_of_continuousAt_zero
      let FB_K := filtrationBasis (⊤ : AddSubgroup ℝ) K
      let FB_Am := filtrationBasis (⊤ : AddSubgroup ℝ) (Fin m → A)
      rw [ContinuousAt, map_zero, FB_K.nhds_zero_hasBasis.tendsto_iff FB_Am.nhds_zero_hasBasis]
      intro V ⟨D, hV⟩; subst hV
      refine ⟨filtration (⊤ : AddSubgroup ℝ) K D, ⟨D, rfl⟩, ?_⟩
      intro x hx d hd
      rw [lmap_apply, hx d hd, map_zero]
    -- Lemma B.2: novikovPiEquiv is continuous (each component is lmap of a projection)
    have h_eq_cont : Continuous (eqA : RealNovikovSeries (Fin m → A) → (Fin m → R)) := by
      apply continuous_pi
      intro i
      have h_component : (fun (s : RealNovikovSeries (Fin m → A)) => (eqA s) i) =
          lmap (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (LinearMap.proj i : (Fin m → A) →ₗ[A] A) := by
        ext s d; rfl
      rw [h_component]
      apply continuous_of_continuousAt_zero
      let FB_Am := filtrationBasis (⊤ : AddSubgroup ℝ) (Fin m → A)
      let FB_A := filtrationBasis (⊤ : AddSubgroup ℝ) A
      rw [ContinuousAt, map_zero, FB_Am.nhds_zero_hasBasis.tendsto_iff FB_A.nhds_zero_hasBasis]
      intro V ⟨D, hV⟩; subst hV
      refine ⟨filtration (⊤ : AddSubgroup ℝ) (Fin m → A) D, ⟨D, rfl⟩, ?_⟩
      intro x hx d hd
      rw [lmap_apply, hx d hd, map_zero]
    -- Lemma B: φ_fwd_lin = eqA ∘ lmap K.subtype is continuous
    have h_φ_fwd_cont : Continuous φ_fwd_lin :=
      h_eq_cont.comp h_lmap_cont
    -- f = g_ext ∘ φ_fwd_lin
    have h_eq : (f : RealNovikovSeries K → R) = (g_ext : (Fin m → R) → R) ∘
        (φ_fwd_lin : RealNovikovSeries K → (Fin m → R)) := by
      funext x
      calc
        f x = g (φ_K x) := by simp [g, φ_K_equiv]
        _ = (g ∘ₗ (s' ∘ₗ i_seq)) (φ_K x) := by simp [h_split]
        _ = g (s' (i_seq (φ_K x))) := rfl
        _ = g_ext (i_seq (φ_K x)) := rfl
        _ = g_ext (φ_fwd_lin x) := rfl
    rw [h_eq]
    exact h_g_ext_cont.comp h_φ_fwd_cont
  -- Apply the finitely-generated lemma to `K`.
  haveI hK_fin : Module.Finite A K :=
    module_finite_of_realNovikovSeries h_canonical_K
  exact (Submodule.fg_top K).mp hK_fin.fg_top

/-- The `A`-linear splitting of `A → RealNovikovSeries A` given by evaluating at `0`. -/
def realNovikovSeriesSplit : RealNovikovSeries A →ₗ[A] A where
  toFun f := f.val fun _ => 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma realNovikovSeriesSplit_comp_algebraMap :
    realNovikovSeriesSplit.comp (Algebra.linearMap A (RealNovikovSeries A)) = LinearMap.id := by
  refine LinearMap.ext fun a => ?_
  have h : (algebraMap A (RealNovikovSeries A) a).val (fun _ => 0) = a := by
    change (algebraMapNovikov a : RealNovikovSeries A).val (fun _ => 0) = a
    dsimp [algebraMapNovikov]
    split_ifs
    · rfl
    · exfalso; apply ‹_›; rfl
  simpa [realNovikovSeriesSplit] using h

/-- The main theorem: if `RealNovikovSeries M` is a finite projective
`RealNovikovSeries A`-module with canonical topology agreeing with the natural one,
then `M` is a finite projective `A`-module. -/
theorem projective_of_realNovikovSeries
    [Module.Finite (RealNovikovSeries A) (RealNovikovSeries M)]
    [Module.Projective (RealNovikovSeries A) (RealNovikovSeries M)]
    (h_canonical : ∀ (f : RealNovikovSeries M →ₗ[RealNovikovSeries A]
        RealNovikovSeries A), Continuous f) :
    Module.Finite A M ∧ Module.Projective A M := by
  haveI : Module.FinitePresentation A M := module_finitePresentation_of_realNovikovSeries h_canonical
  have h_bij := novikovBaseChangeMap_bijective (A := A) (ι := Unit) (M := M) (⊤ : AddSubgroup ℝ)
  let iso := LinearEquiv.ofBijective (novikovBaseChangeMap (⊤ : AddSubgroup ℝ)) h_bij
  haveI : Module.Finite (RealNovikovSeries A) (TensorProduct A (RealNovikovSeries A) M) := by
    exact Module.Finite.equiv iso.symm
  haveI h_proj : Module.Projective (RealNovikovSeries A) (TensorProduct A (RealNovikovSeries A) M) := by
    exact Module.Projective.of_equiv iso.symm
  exact @Novikov.Miscellany.finite_projective_of_split_baseChange A _ M _ _ (RealNovikovSeries A) _ _ realNovikovSeriesSplit realNovikovSeriesSplit_comp_algebraMap ‹_› ‹_›

end Novikov
