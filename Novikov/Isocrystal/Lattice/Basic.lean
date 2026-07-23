import Novikov.Isocrystal.Basic
import Novikov.Series.PowerSeries
import Novikov.Series.Projective

/-!
# Lattices in Novikov isocrystals

This file defines finite power-series lattices in Novikov isocrystals. A split
finite-free presentation identifies monomial shifts of a lattice with the
images of source filtrations. Consequently, the shifts form a neighborhood
basis for the canonical module topology. The same presentation proves
Hausdorffness and transports convergence from a complete finite-free source.
-/

open Filter Topology
open Novikov.Miscellany

namespace Novikov

variable {Λ : ℝ} [Fact (Λ > 1)]
variable {A : Type*} [CommRing A]

namespace NovikovIsocrystal

/-- A finite power-series lattice spanning a Novikov isocrystal. -/
structure Lattice (M : NovikovIsocrystal (Λ := Λ) A) where
  carrier : Submodule (RealNovikovPowerSeries A) M.M
  finite : Module.Finite (RealNovikovPowerSeries A) carrier
  span_eq_top : Submodule.span (RealNovikovSeries A) (carrier : Set M.M) = ⊤

namespace Lattice

variable {M : NovikovIsocrystal (Λ := Λ) A}

/-- The shift `t^d L` of a lattice. -/
noncomputable def shift (L : M.Lattice) (d : ℝ) :
    Submodule (RealNovikovPowerSeries A) M.M :=
  L.carrier.realNovikovShift d

@[simp]
lemma shift_zero (L : M.Lattice) : L.shift 0 = L.carrier :=
  Submodule.realNovikovShift_zero L.carrier

lemma shift_add (L : M.Lattice) (d e : ℝ) :
    (L.shift d).realNovikovShift e = L.shift (d + e) :=
  Submodule.realNovikovShift_add L.carrier d e

lemma shift_mono (L : M.Lattice) {d e : ℝ} (hde : d ≤ e) :
    L.shift e ≤ L.shift d :=
  Submodule.realNovikovShift_mono L.carrier hde

private noncomputable def presentationRank (L : M.Lattice) : ℕ :=
  letI := L.finite
  Classical.choose
    (Module.Finite.exists_fin (R := RealNovikovPowerSeries A) (M := L.carrier))

private noncomputable def presentationGenerators (L : M.Lattice) :
    Fin (presentationRank L) → L.carrier :=
  letI := L.finite
  Classical.choose (Classical.choose_spec
    (Module.Finite.exists_fin (R := RealNovikovPowerSeries A) (M := L.carrier)))

private lemma presentationGenerators_span (L : M.Lattice) :
    Submodule.span (RealNovikovPowerSeries A)
      (Set.range (presentationGenerators L)) = ⊤ := by
  letI := L.finite
  exact Classical.choose_spec (Classical.choose_spec
    (Module.Finite.exists_fin (R := RealNovikovPowerSeries A) (M := L.carrier)))

private noncomputable def presentationMap (L : M.Lattice) :
    RealNovikovSeries (Fin (presentationRank L) → A) →ₗ[RealNovikovSeries A] M.M :=
  (Fintype.linearCombination (RealNovikovSeries A)
    (fun i => (presentationGenerators L i : M.M))).comp
      (novikovPiEquiv (A := A) (M := A) (ι := Unit)
        (ι' := Fin (presentationRank L)) (⊤ : AddSubgroup ℝ)).toLinearMap

private lemma presentationMap_image_filtration_zero (L : M.Lattice) :
    presentationMap L ''
        (filtration (⊤ : AddSubgroup ℝ) (Fin (presentationRank L) → A) 0 :
          Set (RealNovikovSeries (Fin (presentationRank L) → A))) =
      (L.carrier : Set M.M) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [presentationMap, LinearMap.comp_apply, Fintype.linearCombination_apply]
    apply L.carrier.sum_mem
    intro i hi
    let p : RealNovikovPowerSeries A :=
      ⟨(novikovPiEquiv (A := A) (M := A) (ι := Unit)
        (ι' := Fin (presentationRank L)) (⊤ : AddSubgroup ℝ) x) i, by
          intro d hd
          exact congrFun (hx d hd) i⟩
    change (p : RealNovikovSeries A) • (presentationGenerators L i : M.M) ∈ L.carrier
    exact L.carrier.smul_mem p (presentationGenerators L i).property
  · intro hy
    have hsurj : Function.Surjective
        (Fintype.linearCombination (RealNovikovPowerSeries A)
          (presentationGenerators L)) := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination,
        presentationGenerators_span]
    obtain ⟨p, hp⟩ := hsurj ⟨y, hy⟩
    let v : Fin (presentationRank L) → RealNovikovSeries A :=
      fun i => (p i : RealNovikovSeries A)
    let x : RealNovikovSeries (Fin (presentationRank L) → A) :=
      (novikovPiEquiv (A := A) (M := A) (ι := Unit)
        (ι' := Fin (presentationRank L)) (⊤ : AddSubgroup ℝ)).symm v
    refine ⟨x, ?_, ?_⟩
    · intro d hd
      funext i
      change (p i : RealNovikovSeries A).val d = 0
      exact (p i).property d hd
    · rw [presentationMap, LinearMap.comp_apply]
      change Fintype.linearCombination (RealNovikovSeries A)
        (fun i => (presentationGenerators L i : M.M)) v = y
      have hp_coe := congrArg Subtype.val hp
      simpa [v, Fintype.linearCombination_apply] using hp_coe

private lemma presentationMap_image_filtration (L : M.Lattice) (d : ℝ) :
    presentationMap L ''
        (filtration (⊤ : AddSubgroup ℝ) (Fin (presentationRank L) → A) d :
          Set (RealNovikovSeries (Fin (presentationRank L) → A))) =
      (L.shift d : Set M.M) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hxz⟩ :=
      (mem_filtration_iff_exists_realNovikovMonomial_smul
        (A := A) x d).mp hx
    rw [hxz, map_smul]
    refine Submodule.mem_realNovikovShift.mpr ⟨presentationMap L z, ?_, rfl⟩
    change presentationMap L z ∈ (L.carrier : Set M.M)
    rw [← presentationMap_image_filtration_zero L]
    exact ⟨z, hz, rfl⟩
  · intro hy
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_realNovikovShift.mp hy
    have hz_image : z ∈ presentationMap L ''
        (filtration (⊤ : AddSubgroup ℝ) (Fin (presentationRank L) → A) 0 :
          Set (RealNovikovSeries (Fin (presentationRank L) → A))) := by
      rw [presentationMap_image_filtration_zero L]
      exact hz
    obtain ⟨x, hx, hqx⟩ := hz_image
    refine ⟨realNovikovMonomial A d • x, ?_, ?_⟩
    · simpa using realNovikovMonomial_smul_mem_filtration
        (A := A) x d 0 hx
    · rw [map_smul, hqx, hzy]

private lemma presentationMap_surjective (L : M.Lattice) :
    Function.Surjective (presentationMap L) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rw [← L.span_eq_top]
  apply Submodule.span_le.2
  intro y hy
  have hy_image : y ∈ presentationMap L ''
      (filtration (⊤ : AddSubgroup ℝ) (Fin (presentationRank L) → A) 0 :
        Set (RealNovikovSeries (Fin (presentationRank L) → A))) := by
    rw [presentationMap_image_filtration_zero L]
    exact hy
  obtain ⟨x, hx, hxy⟩ := hy_image
  exact ⟨x, hxy⟩

private noncomputable def presentationSection (L : M.Lattice) :
    M.M →ₗ[RealNovikovSeries A]
      RealNovikovSeries (Fin (presentationRank L) → A) :=
  Classical.choose (Module.projective_lifting_property
    (presentationMap L) LinearMap.id (presentationMap_surjective L))

private lemma presentationMap_comp_presentationSection (L : M.Lattice) :
    (presentationMap L).comp (presentationSection L) = LinearMap.id :=
  Classical.choose_spec (Module.projective_lifting_property
    (presentationMap L) LinearMap.id (presentationMap_surjective L))

private lemma source_nhds_zero_hasBasis (L : M.Lattice) :
    (𝓝 (0 : RealNovikovSeries (Fin (presentationRank L) → A))).HasBasis
      (fun _ : ℝ => True)
      (fun d => (filtration (⊤ : AddSubgroup ℝ)
        (Fin (presentationRank L) → A) d :
          Set (RealNovikovSeries (Fin (presentationRank L) → A)))) := by
  apply (filtrationBasis (⊤ : AddSubgroup ℝ)
    (Fin (presentationRank L) → A)).nhds_zero_hasBasis.to_hasBasis
  · intro V hV
    rcases hV with ⟨d, rfl⟩
    exact ⟨d, trivial, Set.Subset.rfl⟩
  · intro d hd
    exact ⟨filtration (⊤ : AddSubgroup ℝ)
      (Fin (presentationRank L) → A) d, ⟨d, rfl⟩, Set.Subset.rfl⟩

private lemma presentationMap_continuous (L : M.Lattice) :
    @Continuous
      (RealNovikovSeries (Fin (presentationRank L) → A)) M.M
      inferInstance
      (canonicalTopology (RealNovikovSeries A) M.M)
      (presentationMap L) := by
  have h := canonicalTopology.continuous_linearMap
    (RealNovikovSeries A)
    (RealNovikovSeries (Fin (presentationRank L) → A)) M.M
    (presentationMap L)
  rw [canonicalTopology_realNovikovSeries_eq
    (A := A) (M := Fin (presentationRank L) → A)] at h
  exact h

private lemma presentationSection_continuous (L : M.Lattice) :
    @Continuous M.M
      (RealNovikovSeries (Fin (presentationRank L) → A))
      (canonicalTopology (RealNovikovSeries A) M.M)
      inferInstance
      (presentationSection L) := by
  have h := canonicalTopology.continuous_linearMap
    (RealNovikovSeries A) M.M
    (RealNovikovSeries (Fin (presentationRank L) → A))
    (presentationSection L)
  rw [canonicalTopology_realNovikovSeries_eq
    (A := A) (M := Fin (presentationRank L) → A)] at h
  exact h

private lemma presentationMap_isOpenMap (L : M.Lattice) :
    @IsOpenMap
      (RealNovikovSeries (Fin (presentationRank L) → A)) M.M
      inferInstance
      (canonicalTopology (RealNovikovSeries A) M.M)
      (presentationMap L) := by
  letI : IsTopologicalRing (RealNovikovSeries A) := is_topological_ring
  have h := canonicalTopology.isOpenMap_of_surjective_of_projective
    (RealNovikovSeries A)
    (RealNovikovSeries (Fin (presentationRank L) → A)) M.M
    (presentationMap L) (presentationMap_surjective L)
  rw [canonicalTopology_realNovikovSeries_eq
    (A := A) (M := Fin (presentationRank L) → A)] at h
  exact h

/-- The shifted lattices form a neighborhood basis of zero for the canonical
module topology. -/
lemma nhds_zero_hasBasis (L : M.Lattice) :
    letI : TopologicalSpace M.M :=
      canonicalTopology (RealNovikovSeries A) M.M
    (𝓝 (0 : M.M)).HasBasis (fun _ : ℝ => True)
      (fun d => (L.shift d : Set M.M)) := by
  letI : TopologicalSpace M.M :=
    canonicalTopology (RealNovikovSeries A) M.M
  have hmap := (source_nhds_zero_hasBasis L).map (presentationMap L)
  have hfilter : Filter.map (presentationMap L)
      (𝓝 (0 : RealNovikovSeries (Fin (presentationRank L) → A))) =
      𝓝 (0 : M.M) := by
    simpa using (presentationMap_isOpenMap L).map_nhds_eq
      (x := (0 : RealNovikovSeries (Fin (presentationRank L) → A)))
      (presentationMap_continuous L).continuousAt
  rw [hfilter] at hmap
  refine hmap.congr (fun _ => Iff.rfl) ?_
  intro d hd
  exact presentationMap_image_filtration L d

/-- Every shifted lattice is open in the canonical module topology. -/
lemma shift_isOpen (L : M.Lattice) (d : ℝ) :
    letI : TopologicalSpace M.M :=
      canonicalTopology (RealNovikovSeries A) M.M
    IsOpen (L.shift d : Set M.M) := by
  letI : TopologicalSpace M.M :=
    canonicalTopology (RealNovikovSeries A) M.M
  letI : IsTopologicalRing (RealNovikovSeries A) := is_topological_ring
  letI : IsTopologicalAddGroup M.M :=
    canonicalTopology.isTopologicalAddGroup (RealNovikovSeries A) M.M
  exact (L.shift d).toAddSubgroup.isOpen_of_mem_nhds
    (L.nhds_zero_hasBasis.mem_of_mem (i := d) trivial)

/-- Every shifted lattice is closed in the canonical module topology. -/
lemma shift_isClosed (L : M.Lattice) (d : ℝ) :
    letI : TopologicalSpace M.M :=
      canonicalTopology (RealNovikovSeries A) M.M
    IsClosed (L.shift d : Set M.M) := by
  letI : TopologicalSpace M.M :=
    canonicalTopology (RealNovikovSeries A) M.M
  letI : IsTopologicalRing (RealNovikovSeries A) := is_topological_ring
  letI : IsTopologicalAddGroup M.M :=
    canonicalTopology.isTopologicalAddGroup (RealNovikovSeries A) M.M
  exact (L.shift d).toAddSubgroup.isClosed_of_isOpen (L.shift_isOpen d)

/-- The canonical module topology is Hausdorff in the presence of a lattice. -/
lemma canonicalTopology_t2 (L : M.Lattice) :
    @T2Space M.M (canonicalTopology (RealNovikovSeries A) M.M) := by
  letI : TopologicalSpace M.M :=
    canonicalTopology (RealNovikovSeries A) M.M
  have hleft : Function.LeftInverse (presentationMap L) (presentationSection L) := by
    intro x
    simpa using LinearMap.congr_fun
      (presentationMap_comp_presentationSection L) x
  have hemb : Topology.IsEmbedding (presentationSection L) :=
    hleft.isEmbedding (presentationMap_continuous L)
      (presentationSection_continuous L)
  exact hemb.t2Space

/-- A sequence whose successive differences eventually lie in every lattice
shift converges for the canonical module topology. -/
lemma exists_limit_of_succ_diff_shift (L : M.Lattice) (x : ℕ → M.M)
    (h : ∀ D : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      x (n + 1) - x n ∈ L.shift D) :
    letI : TopologicalSpace M.M :=
      canonicalTopology (RealNovikovSeries A) M.M
    ∃ y : M.M, Filter.Tendsto x Filter.atTop (𝓝 y) := by
  letI : TopologicalSpace M.M :=
    canonicalTopology (RealNovikovSeries A) M.M
  let s := presentationSection L
  have hs_cont : Continuous s := presentationSection_continuous L
  have hs_cauchy : CauchySeq (fun n => s (x n)) := by
    apply cauchySeq_of_succ_diff_filtration
    intro D
    have hFD :
        (filtration (⊤ : AddSubgroup ℝ) (Fin (presentationRank L) → A) D :
          Set (RealNovikovSeries (Fin (presentationRank L) → A))) ∈
          𝓝 (0 : RealNovikovSeries (Fin (presentationRank L) → A)) :=
      (source_nhds_zero_hasBasis L).mem_of_mem (i := D) trivial
    have hpre : s ⁻¹'
        (filtration (⊤ : AddSubgroup ℝ) (Fin (presentationRank L) → A) D :
          Set (RealNovikovSeries (Fin (presentationRank L) → A))) ∈
          𝓝 (0 : M.M) := by
      have hs_at : ContinuousAt s (0 : M.M) := hs_cont.continuousAt
      apply hs_at.preimage_mem_nhds
      simpa only [map_zero] using hFD
    obtain ⟨E, hE, hEsub⟩ := L.nhds_zero_hasBasis.mem_iff.mp hpre
    obtain ⟨N, hN⟩ := h E
    refine ⟨N, fun n hn => ?_⟩
    have hsn := hEsub (hN n hn)
    change s (x (n + 1)) - s (x n) ∈
      filtration (⊤ : AddSubgroup ℝ) (Fin (presentationRank L) → A) D
    rw [← map_sub]
    exact hsn
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hs_cauchy
  refine ⟨presentationMap L z, ?_⟩
  have hqz : Filter.Tendsto
      (fun n => presentationMap L (s (x n))) Filter.atTop
      (𝓝 (presentationMap L z)) := by
    simpa [Function.comp_def] using
      (presentationMap_continuous L).tendsto z |>.comp hz
  have hqs : (fun n => presentationMap L (s (x n))) = x := by
    funext n
    simpa [s] using LinearMap.congr_fun
      (presentationMap_comp_presentationSection L) (x n)
  rwa [hqs] at hqz

end Lattice

end NovikovIsocrystal

end Novikov
