import Novikov.Isocrystal.Lattice.Contraction
import Novikov.Isocrystal.Injective
import Novikov.Series.Projective

/-!
# Constant Novikov isocrystals from lattices

This file proves that a Novikov isocrystal admitting a finite power-series
lattice on which Frobenius is congruent to the identity in positive degree is
constant.

The first part constructs the presentation associated to a finite family of
Frobenius-fixed lattice generators. Its kernel is coefficientwise constant by
`frobenius_limit`, and its constant-coefficient submodule is finite projective.
The resulting coefficient quotient base-changes back to the isocrystal; split
base-change descent makes it finite projective and yields the final isomorphism.
-/

open Filter Topology
open Novikov.Miscellany

namespace Novikov

universe u

variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]
variable {A : Type u} [CommRing A]

namespace NovikovIsocrystal.Lattice

variable {M : NovikovIsocrystal (Λ := Λ) A}

private noncomputable def fixedGeneratorMap {n : ℕ} (m : Fin n → M.M) :
    RealNovikovSeries (Fin n → A) →ₗ[RealNovikovSeries A] M.M :=
  (Fintype.linearCombination (RealNovikovSeries A) m).comp
    (novikovPiEquiv (A := A) (M := A) (ι := Unit) (ι' := Fin n)
      (⊤ : AddSubgroup ℝ)).toLinearMap

private lemma fixedGeneratorMap_frobenius {n : ℕ} (m : Fin n → M.M)
    (hm : ∀ i, M.F_M (m i) = m i) (x : RealNovikovSeries (Fin n → A)) :
    fixedGeneratorMap m (frobenius Λ x) = M.F_M (fixedGeneratorMap m x) := by
  classical
  simp only [fixedGeneratorMap, LinearMap.comp_apply,
    Fintype.linearCombination_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [M.F_M.map_smulₛₗ, hm i]
  congr 1

private lemma fixedGeneratorMap_surjective {n : ℕ} (L : M.Lattice)
    (m : Fin n → L.carrier)
    (hm : Submodule.span (RealNovikovPowerSeries A)
      (Set.range fun i => (m i : M.M)) = L.carrier) :
    Function.Surjective (fixedGeneratorMap (fun i => (m i : M.M))) := by
  classical
  let q := fixedGeneratorMap (fun i => (m i : M.M))
  have hm_range (i : Fin n) : (m i : M.M) ∈ LinearMap.range q := by
    let π := novikovPiEquiv (A := A) (M := A) (ι := Unit) (ι' := Fin n)
      (⊤ : AddSubgroup ℝ)
    refine ⟨π.symm (Pi.single i 1), ?_⟩
    change Fintype.linearCombination (RealNovikovSeries A)
      (fun i => (m i : M.M)) (Pi.single i 1) = (m i : M.M)
    rw [Fintype.linearCombination_apply_single, one_smul]
  have hcarrier_range : L.carrier ≤
      (LinearMap.range q).restrictScalars (RealNovikovPowerSeries A) := by
    rw [← hm]
    apply Submodule.span_le.2
    rintro y ⟨i, rfl⟩
    exact hm_range i
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rw [← L.span_eq_top]
  apply Submodule.span_le.2
  intro y hy
  exact hcarrier_range hy

private noncomputable def fixedGeneratorKernel {n : ℕ} (m : Fin n → M.M) :
    Submodule A (RealNovikovSeries (Fin n → A)) :=
  (LinearMap.ker (fixedGeneratorMap m)).restrictScalars A

private noncomputable def fixedGeneratorKernelZero {n : ℕ} (m : Fin n → M.M) :
    Submodule A (Fin n → A) :=
  S_zero_submodule (fixedGeneratorKernel m)

private lemma fixedGeneratorKernel_eq {n : ℕ} (L : M.Lattice)
    (m : Fin n → M.M) (hm : ∀ i, M.F_M (m i) = m i) :
    fixedGeneratorKernel m = submoduleSeries (fixedGeneratorKernelZero m) := by
  letI : TopologicalSpace M.M :=
    canonicalTopology (RealNovikovSeries A) M.M
  letI : T2Space M.M := L.canonicalTopology_t2
  let q := fixedGeneratorMap m
  have hq_cont : Continuous q := by
    have h := canonicalTopology.continuous_linearMap
      (RealNovikovSeries A) (RealNovikovSeries (Fin n → A)) M.M q
    rw [canonicalTopology_realNovikovSeries_eq
      (A := A) (M := Fin n → A)] at h
    exact h
  have hK : FrobeniusLimitHyp (Λ := Λ) (fixedGeneratorKernel m) := by
    refine ⟨?_, ?_, ?_⟩
    · change IsClosed (q ⁻¹' {0})
      exact isClosed_singleton.preimage hq_cont
    · intro x hx
      change q (frobenius Λ x) = 0
      rw [fixedGeneratorMap_frobenius m hm]
      have hxq : q x = 0 := hx
      rw [hxq, map_zero]
    · intro d x hx
      change q
        ((novikovMonomial (1 : A)
          (fun _ : Unit => ⟨d, AddSubgroup.mem_top _⟩) : RealNovikovSeries A) • x) = 0
      rw [map_smul]
      have hxq : q x = 0 := hx
      rw [hxq, smul_zero]
  simpa [fixedGeneratorKernelZero] using
    frobenius_limit (fixedGeneratorKernel m) hK

private lemma fixedGeneratorKernelZero_finite_projective {n : ℕ}
    (L : M.Lattice) (m : Fin n → L.carrier)
    (hm_fixed : ∀ i, M.F_M (m i : M.M) = m i)
    (hm_span : Submodule.span (RealNovikovPowerSeries A)
      (Set.range fun i => (m i : M.M)) = L.carrier) :
    Module.Finite A (fixedGeneratorKernelZero (fun i => (m i : M.M))) ∧
      Module.Projective A (fixedGeneratorKernelZero (fun i => (m i : M.M))) := by
  let R := RealNovikovSeries A
  let mM : Fin n → M.M := fun i => (m i : M.M)
  let q := fixedGeneratorMap mM
  let KR : Submodule R (RealNovikovSeries (Fin n → A)) := LinearMap.ker q
  let KA : Submodule A (RealNovikovSeries (Fin n → A)) := fixedGeneratorKernel mM
  let K0 : Submodule A (Fin n → A) := fixedGeneratorKernelZero mM
  have hq_surj : Function.Surjective q := by
    simpa [q, mM] using fixedGeneratorMap_surjective L m hm_span
  obtain ⟨s, hs⟩ : ∃ s : M.M →ₗ[R] RealNovikovSeries (Fin n → A),
      q.comp s = LinearMap.id :=
    Module.projective_lifting_property q LinearMap.id hq_surj
  let p : RealNovikovSeries (Fin n → A) →ₗ[R]
      RealNovikovSeries (Fin n → A) := LinearMap.id - s.comp q
  have hp_mem (x : RealNovikovSeries (Fin n → A)) : p x ∈ KR := by
    change q (x - s (q x)) = 0
    rw [map_sub]
    have hsec : q (s (q x)) = q x := by
      have h := LinearMap.congr_fun hs (q x)
      simpa using h
    rw [hsec, sub_self]
  let pK : RealNovikovSeries (Fin n → A) →ₗ[R] KR :=
    LinearMap.codRestrict KR p hp_mem
  have hp_split : pK.comp KR.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx : q (x : RealNovikovSeries (Fin n → A)) = 0 := x.property
    change (x : RealNovikovSeries (Fin n → A)) - s (q x) = x
    rw [hx, map_zero, sub_zero]
  let π := novikovPiEquiv (A := A) (M := A) (ι := Unit) (ι' := Fin n)
    (⊤ : AddSubgroup ℝ)
  let qPi : (Fin n → R) →ₗ[R] M.M :=
    Fintype.linearCombination R mM
  have hq_eq : q = qPi.comp π.toLinearMap := by
    rfl
  have hqPi_surj : Function.Surjective qPi := by
    intro y
    obtain ⟨x, hx⟩ := hq_surj y
    refine ⟨π x, ?_⟩
    simpa [q, qPi, fixedGeneratorMap] using hx
  obtain ⟨sPi, hsPi⟩ : ∃ sPi : M.M →ₗ[R] (Fin n → R),
      qPi.comp sPi = LinearMap.id :=
    Module.projective_lifting_property qPi LinearMap.id hqPi_surj
  let KPi : Submodule R (Fin n → R) := LinearMap.ker qPi
  let pPi : (Fin n → R) →ₗ[R] (Fin n → R) :=
    LinearMap.id - sPi.comp qPi
  have hpPi_mem (x : Fin n → R) : pPi x ∈ KPi := by
    change qPi (x - sPi (qPi x)) = 0
    rw [map_sub]
    have hsec : qPi (sPi (qPi x)) = qPi x := by
      have h := LinearMap.congr_fun hsPi (qPi x)
      simpa using h
    rw [hsec, sub_self]
  let pKPi : (Fin n → R) →ₗ[R] KPi :=
    LinearMap.codRestrict KPi pPi hpPi_mem
  have hpPi_split : pKPi.comp KPi.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx : qPi (x : Fin n → R) = 0 := x.property
    change (x : Fin n → R) - sPi (qPi x) = x
    rw [hx, map_zero, sub_zero]
  haveI : Module.Free R (Fin n → R) :=
    Module.Free.of_basis (Pi.basisFun R (Fin n))
  haveI : Module.Finite R (Fin n → R) :=
    Module.Finite.of_basis (Pi.basisFun R (Fin n))
  haveI : Module.Projective R (Fin n → R) := inferInstance
  haveI : Module.Projective R KPi :=
    Module.Projective.of_split KPi.subtype pKPi hpPi_split
  have hpKPi_surj : Function.Surjective pKPi := by
    intro y
    refine ⟨(y : Fin n → R), ?_⟩
    exact LinearMap.congr_fun hpPi_split y
  haveI : Module.Finite R KPi :=
    Module.Finite.of_surjective pKPi hpKPi_surj
  let toKPi : KR →ₗ[R] KPi :=
    LinearMap.codRestrict KPi (π.toLinearMap.comp KR.subtype) (by
      intro x
      have hx : q (x : RealNovikovSeries (Fin n → A)) = 0 := x.property
      change (qPi.comp π.toLinearMap)
        (x : RealNovikovSeries (Fin n → A)) = 0
      rw [← hq_eq]
      exact hx)
  have htoKPi_inj : Function.Injective toKPi := by
    intro x y hxy
    apply Subtype.ext
    apply π.injective
    exact congrArg Subtype.val hxy
  have htoKPi_surj : Function.Surjective toKPi := by
    intro y
    let x : RealNovikovSeries (Fin n → A) := π.symm (y : Fin n → R)
    have hx : x ∈ KR := by
      have hy : qPi (y : Fin n → R) = 0 := y.property
      change q x = 0
      rw [hq_eq]
      change qPi (π (π.symm (y : Fin n → R))) = 0
      rw [π.apply_symm_apply]
      exact hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    change π (π.symm (y : Fin n → R)) = y
    exact π.apply_symm_apply y
  let kernelEquiv : KR ≃ₗ[R] KPi :=
    LinearEquiv.ofBijective toKPi ⟨htoKPi_inj, htoKPi_surj⟩
  haveI : Module.Finite R KR :=
    Module.Finite.equiv kernelEquiv.symm
  haveI : Module.Projective R KR :=
    Module.Projective.of_equiv kernelEquiv.symm
  have hK_eq : KA = submoduleSeries K0 := by
    simpa [KA, K0, mM] using fixedGeneratorKernel_eq L mM (by
      simpa [mM] using hm_fixed)
  let liftMap : RealNovikovSeries K0 →ₗ[R]
      RealNovikovSeries (Fin n → A) :=
    lmapNovikov (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K0.subtype
  have hlift_mem (x : RealNovikovSeries K0) : liftMap x ∈ KR := by
    have hx : liftMap x ∈ submoduleSeries K0 := by
      intro d
      exact (x.val d).property
    rw [← hK_eq] at hx
    exact hx
  let φK : RealNovikovSeries K0 →ₗ[R] KR :=
    LinearMap.codRestrict KR liftMap hlift_mem
  have hφK_inj : Function.Injective φK := by
    intro x y hxy
    apply lmap_injective (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
      K0.subtype Subtype.val_injective
    exact congrArg Subtype.val hxy
  have hφK_surj : Function.Surjective φK := by
    intro y
    have hyKA : (y : RealNovikovSeries (Fin n → A)) ∈ KA := y.property
    have hyseries : (y : RealNovikovSeries (Fin n → A)) ∈
        submoduleSeries K0 := by
      rw [← hK_eq]
      exact hyKA
    let x : RealNovikovSeries K0 :=
      ⟨fun d => ⟨y.val.val d, hyseries d⟩, by
        apply is_novikov_series_of_subset y.val.prop
        intro d hd hzero
        apply hd
        apply Subtype.ext
        exact hzero⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    ext d
    rfl
  let φKEquiv : RealNovikovSeries K0 ≃ₗ[R] KR :=
    LinearEquiv.ofBijective φK ⟨hφK_inj, hφK_surj⟩
  haveI : Module.Finite R (RealNovikovSeries K0) :=
    Module.Finite.equiv φKEquiv.symm
  haveI : Module.Projective R (RealNovikovSeries K0) :=
    Module.Projective.of_equiv φKEquiv.symm
  have hcanonical : ∀ f : RealNovikovSeries K0 →ₗ[R] R, Continuous f := by
    intro f
    let g : KR →ₗ[R] R := f.comp φKEquiv.symm.toLinearMap
    let gext : RealNovikovSeries (Fin n → A) →ₗ[R] R := g.comp pK
    have hgext : Continuous gext := every_linearMap_continuous_pi gext
    have hlift : Continuous liftMap :=
      lmap_continuous (Γ := (⊤ : AddSubgroup ℝ)) K0.subtype
    have heq : (f : RealNovikovSeries K0 → R) =
        (gext : RealNovikovSeries (Fin n → A) → R) ∘ liftMap := by
      funext x
      have hp_lift : pK (liftMap x) = φK x := by
        change pK (KR.subtype (φK x)) = φK x
        exact LinearMap.congr_fun hp_split (φK x)
      change f x = g (pK (liftMap x))
      rw [hp_lift]
      simp [g, φKEquiv]
    rw [heq]
    exact hgext.comp hlift
  have hresult : Module.Finite A K0 ∧ Module.Projective A K0 :=
    projective_of_realNovikovSeries hcanonical
  simpa [K0, mM] using hresult

private noncomputable abbrev coefficientQuotient {n : ℕ} (m : Fin n → M.M) :=
  (Fin n → A) ⧸ fixedGeneratorKernelZero m

private noncomputable def coefficientQuotientMap {n : ℕ} (m : Fin n → M.M) :
    (Fin n → A) →ₗ[A] coefficientQuotient m :=
  (fixedGeneratorKernelZero m).mkQ

private noncomputable def seriesQuotientMap {n : ℕ} (m : Fin n → M.M) :
    RealNovikovSeries (Fin n → A) →ₗ[RealNovikovSeries A]
      RealNovikovSeries (coefficientQuotient m) :=
  lmapNovikov (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
    (coefficientQuotientMap m)

private lemma seriesQuotientMap_ker_eq {n : ℕ} (L : M.Lattice)
    (m : Fin n → M.M) (hm : ∀ i, M.F_M (m i) = m i) :
    LinearMap.ker (seriesQuotientMap m) =
      LinearMap.ker (fixedGeneratorMap m) := by
  let K0 := fixedGeneratorKernelZero m
  let q0 : (Fin n → A) →ₗ[A] coefficientQuotient m :=
    coefficientQuotientMap m
  let qSeries := seriesQuotientMap m
  have hK_eq : fixedGeneratorKernel m = submoduleSeries K0 := by
    simpa [K0] using fixedGeneratorKernel_eq L m hm
  have hexact : Function.Exact
      (lmapNovikov (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K0.subtype)
      qSeries := by
    apply lmap_exact
    exact LinearMap.exact_subtype_mkQ K0
  ext x
  constructor
  · intro hx
    have hx0 : qSeries x = 0 := hx
    obtain ⟨y, hy⟩ := (hexact x).mp hx0
    have hylift :
        lmapNovikov (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) K0.subtype y ∈
          fixedGeneratorKernel m := by
      rw [hK_eq]
      intro d
      exact (y.val d).property
    have hxK : x ∈ fixedGeneratorKernel m := by
      rw [← hy]
      exact hylift
    exact hxK
  · intro hx
    have hxK : x ∈ fixedGeneratorKernel m := hx
    rw [hK_eq] at hxK
    let y : RealNovikovSeries K0 :=
      ⟨fun d => ⟨x.val d, hxK d⟩, by
        apply is_novikov_series_of_subset x.prop
        intro d hd hzero
        apply hd
        apply Subtype.ext
        exact hzero⟩
    apply (hexact x).mpr
    refine ⟨y, ?_⟩
    ext d
    rfl

private noncomputable def fixedGeneratorSeriesEquiv {n : ℕ}
    (L : M.Lattice) (m : Fin n → L.carrier)
    (hm_fixed : ∀ i, M.F_M (m i : M.M) = m i)
    (hm_span : Submodule.span (RealNovikovPowerSeries A)
      (Set.range fun i => (m i : M.M)) = L.carrier) :
    RealNovikovSeries
        (coefficientQuotient (fun i => (m i : M.M))) ≃ₗ[RealNovikovSeries A]
      M.M := by
  let mM : Fin n → M.M := fun i => (m i : M.M)
  let q := fixedGeneratorMap mM
  let qSeries := seriesQuotientMap mM
  have hq_surj : Function.Surjective q := by
    simpa [q, mM] using fixedGeneratorMap_surjective L m hm_span
  have hqSeries_surj : Function.Surjective qSeries := by
    apply lmap_surjective
    exact Submodule.mkQ_surjective _
  have hker : LinearMap.ker qSeries = LinearMap.ker q := by
    simpa [qSeries, q, mM] using
      seriesQuotientMap_ker_eq L mM (by simpa [mM] using hm_fixed)
  exact (qSeries.quotKerEquivOfSurjective hqSeries_surj).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    q.quotKerEquivOfSurjective hq_surj

private lemma fixedGeneratorSeriesEquiv_apply {n : ℕ}
    (L : M.Lattice) (m : Fin n → L.carrier)
    (hm_fixed : ∀ i, M.F_M (m i : M.M) = m i)
    (hm_span : Submodule.span (RealNovikovPowerSeries A)
      (Set.range fun i => (m i : M.M)) = L.carrier)
    (x : RealNovikovSeries (Fin n → A)) :
    fixedGeneratorSeriesEquiv L m hm_fixed hm_span
        (seriesQuotientMap (fun i => (m i : M.M)) x) =
      fixedGeneratorMap (fun i => (m i : M.M)) x := by
  simp [fixedGeneratorSeriesEquiv]

private lemma seriesQuotientMap_frobenius {n : ℕ} (m : Fin n → M.M)
    (x : RealNovikovSeries (Fin n → A)) :
    seriesQuotientMap m (frobenius Λ x) =
      frobenius Λ (seriesQuotientMap m x) := by
  simpa [seriesQuotientMap, coefficientQuotientMap, lmapNovikov] using
    (frobenius_comp_map (Λ := Λ)
      (coefficientQuotientMap m).toAddMonoidHom x).symm

private lemma fixedGeneratorSeriesEquiv_frobenius {n : ℕ}
    (L : M.Lattice) (m : Fin n → L.carrier)
    (hm_fixed : ∀ i, M.F_M (m i : M.M) = m i)
    (hm_span : Submodule.span (RealNovikovPowerSeries A)
      (Set.range fun i => (m i : M.M)) = L.carrier)
    (x : RealNovikovSeries
      (coefficientQuotient (fun i => (m i : M.M)))) :
    fixedGeneratorSeriesEquiv L m hm_fixed hm_span (frobenius Λ x) =
      M.F_M (fixedGeneratorSeriesEquiv L m hm_fixed hm_span x) := by
  let mM : Fin n → M.M := fun i => (m i : M.M)
  let q0 := coefficientQuotientMap mM
  let qSeries := seriesQuotientMap mM
  have hqSeries_surj : Function.Surjective qSeries := by
    apply lmap_surjective
    exact Submodule.mkQ_surjective _
  obtain ⟨y, rfl⟩ := hqSeries_surj x
  calc
    fixedGeneratorSeriesEquiv L m hm_fixed hm_span
        (frobenius Λ (qSeries y)) =
        fixedGeneratorSeriesEquiv L m hm_fixed hm_span
          (qSeries (frobenius Λ y)) := by
            rw [seriesQuotientMap_frobenius mM y]
    _ = fixedGeneratorMap mM (frobenius Λ y) := by
      simpa [mM, qSeries] using
        fixedGeneratorSeriesEquiv_apply L m hm_fixed hm_span (frobenius Λ y)
    _ = M.F_M (fixedGeneratorMap mM y) :=
      fixedGeneratorMap_frobenius mM (by simpa [mM] using hm_fixed) y
    _ = M.F_M
        (fixedGeneratorSeriesEquiv L m hm_fixed hm_span (qSeries y)) := by
      rw [fixedGeneratorSeriesEquiv_apply L m hm_fixed hm_span y]

end NovikovIsocrystal.Lattice

open NovikovIsocrystal.Lattice

/-- A Novikov isocrystal with a finite power-series lattice on which Frobenius
is pointwise congruent to the identity in positive degree is constant. -/
theorem lattice_isocrystal
    (M : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (L : M.Lattice)
    (hF : ∀ m : L.carrier, ∃ ε : ℝ, 0 < ε ∧
      M.F_M (m : M.M) - (m : M.M) ∈ L.shift ε) :
    ∃ M0 : FiniteProjectiveModule A,
      Nonempty (M ≅ NovikovIsocrystal.ConstIsocrystal M0) := by
  classical
  have hF' : ∀ m : M.M, m ∈ L.carrier →
      ∃ ε : ℝ, 0 < ε ∧ M.F_M m - m ∈ L.shift ε := by
    intro m hm
    simpa using hF ⟨m, hm⟩
  obtain ⟨n, m, hm_fixed, hm_span⟩ := L.exists_fixed_generators hF'
  let mM : Fin n → M.M := fun i => (m i : M.M)
  let K0 : Submodule A (Fin n → A) := fixedGeneratorKernelZero mM
  let N0 := coefficientQuotient mM
  have hK0 : Module.Finite A K0 ∧ Module.Projective A K0 := by
    simpa [K0, mM] using
      fixedGeneratorKernelZero_finite_projective L m hm_fixed hm_span
  letI : Module.Finite A K0 := hK0.1
  letI : Module.Projective A K0 := hK0.2
  let q0 : (Fin n → A) →ₗ[A] N0 := coefficientQuotientMap mM
  have hq0_surj : Function.Surjective q0 := by
    simpa [q0, K0, N0, coefficientQuotientMap] using
      Submodule.mkQ_surjective K0
  have hq0_ker : LinearMap.ker q0 = K0 := by
    simp [q0, K0, N0, coefficientQuotientMap]
  have hq0_ker_fg : (LinearMap.ker q0).FG := by
    rw [hq0_ker]
    exact (Submodule.fg_top K0).mp Module.Finite.fg_top
  letI : Module.Free A (Fin n → A) :=
    Module.Free.of_basis (Pi.basisFun A (Fin n))
  letI : Module.Finite A (Fin n → A) :=
    Module.Finite.of_basis (Pi.basisFun A (Fin n))
  letI : Module.FinitePresentation A N0 :=
    Module.finitePresentation_of_free_of_surjective q0 hq0_surj hq0_ker_fg
  let eSeries : RealNovikovSeries N0 ≃ₗ[RealNovikovSeries A] M.M :=
    fixedGeneratorSeriesEquiv L m hm_fixed hm_span
  let baseEquiv :
      TensorProduct A (RealNovikovSeries A) N0 ≃ₗ[RealNovikovSeries A]
        RealNovikovSeries N0 :=
    novikovModule_base_change_equiv (⊤ : AddSubgroup ℝ)
  let eTensor :
      TensorProduct A (RealNovikovSeries A) N0 ≃ₗ[RealNovikovSeries A] M.M :=
    baseEquiv.trans eSeries
  letI : Module.Finite (RealNovikovSeries A)
      (TensorProduct A (RealNovikovSeries A) N0) :=
    Module.Finite.equiv eTensor.symm
  letI : Module.Projective (RealNovikovSeries A)
      (TensorProduct A (RealNovikovSeries A) N0) :=
    Module.Projective.of_equiv eTensor.symm
  have hN0 : Module.Finite A N0 ∧ Module.Projective A N0 :=
    Novikov.Miscellany.finite_projective_of_split_baseChange
      (M := N0) (B := RealNovikovSeries A)
      realNovikovSeriesSplit realNovikovSeriesSplit_comp_algebraMap
  letI : Module.Finite A N0 := hN0.1
  letI : Module.Projective A N0 := hN0.2
  let M0 : FiniteProjectiveModule A := { M := N0 }
  let c := constIsocrystal_to_realSeries (Λ := Λ) M0
  let e : (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) M0).M ≃ₗ[
      RealNovikovSeries A] M.M := c.trans eSeries
  have he_frobenius
      (x : (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) M0).M) :
      M.F_M (e x) =
        e ((NovikovIsocrystal.ConstIsocrystal (Λ := Λ) M0).F_M x) := by
    change M.F_M (eSeries (c x)) =
      eSeries (c ((NovikovIsocrystal.ConstIsocrystal (Λ := Λ) M0).F_M x))
    rw [← fixedGeneratorSeriesEquiv_frobenius L m hm_fixed hm_span]
    have hc : c ((NovikovIsocrystal.ConstIsocrystal (Λ := Λ) M0).F_M x) =
        frobenius Λ (c x) := by
      simpa [c] using
        constIsocrystal_to_realSeries_commutes_frobenius (Λ := Λ) M0 x
    rw [hc]
  let iso : M ≅ NovikovIsocrystal.ConstIsocrystal M0 :=
    { hom :=
        { toLinearMap := e.symm.toLinearMap
          commute_frobenius := by
            intro x
            apply e.injective
            rw [← he_frobenius]
            calc
              M.F_M (e (e.symm x)) = M.F_M x :=
                congrArg M.F_M (e.apply_symm_apply x)
              _ = e (e.symm (M.F_M x)) :=
                (e.apply_symm_apply (M.F_M x)).symm }
      inv :=
        { toLinearMap := e.toLinearMap
          commute_frobenius := he_frobenius }
      hom_inv_id := by
        apply NovikovIsocrystal.hom_ext
        apply LinearMap.ext
        intro x
        exact e.apply_symm_apply x
      inv_hom_id := by
        apply NovikovIsocrystal.hom_ext
        apply LinearMap.ext
        intro x
        exact e.symm_apply_apply x }
  exact ⟨M0, ⟨iso⟩⟩

end Novikov
