import Novikov.Isocrystal.Lattice.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Nakayama

/-!
# Frobenius contraction on a Novikov-isocrystal lattice

Under the hypothesis that Frobenius is congruent to the identity modulo a
positive shift at every lattice element, Frobenius contracts all lattice
shifts. Its orbits therefore converge to fixed lattice elements. Correcting a
finite generating family by these limits and applying Nakayama's lemma gives a
finite Frobenius-fixed generating family.
-/

open Filter Topology
open Novikov.Miscellany

namespace Novikov

variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]
variable {A : Type*} [CommRing A]

namespace NovikovIsocrystal.Lattice

variable {M : NovikovIsocrystal (Λ := Λ) A}
variable (L : M.Lattice)
variable (hF : ∀ m : M.M, m ∈ L.carrier →
  ∃ ε : ℝ, 0 < ε ∧ M.F_M m - m ∈ L.shift ε)

include hF

/-- Frobenius preserves a lattice on which it is pointwise congruent to the
identity modulo positive shifts. -/
lemma frobenius_mem {m : M.M} (hm : m ∈ L.carrier) :
    M.F_M m ∈ L.carrier := by
  obtain ⟨ε, hε, hmε⟩ := hF m hm
  have herr : M.F_M m - m ∈ L.carrier :=
    Submodule.realNovikovShift_le L.carrier hε.le hmε
  have hadd := L.carrier.add_mem herr hm
  simpa using hadd

/-- Frobenius sends the `d`-shift of a lattice into its `Λ * d`-shift. -/
lemma frobenius_shift {x y : M.M} {d : ℝ}
    (hxy : x - y ∈ L.shift d) :
    M.F_M x - M.F_M y ∈ L.shift (Λ * d) := by
  obtain ⟨z, hz, hzy⟩ := Submodule.mem_realNovikovShift.mp hxy
  refine Submodule.mem_realNovikovShift.mpr
    ⟨M.F_M z, frobenius_mem L hF hz, ?_⟩
  rw [← map_sub, ← hzy, M.F_M.map_smulₛₗ]
  change realNovikovMonomial A (Λ * d) • M.F_M z =
    frobenius Λ (realNovikovMonomial A d) • M.F_M z
  rw [frobenius_realNovikovMonomial]

/-- Consecutive terms of a Frobenius orbit lie in exponentially deeper lattice
shifts. -/
lemma frobenius_iterate_succ_sub_mem_shift {m : M.M} {ε : ℝ}
    (hm : M.F_M m - m ∈ L.shift ε) (k : ℕ) :
    (M.F_M^[k + 1]) m - (M.F_M^[k]) m ∈
      L.shift (Λ ^ k * ε) := by
  induction k with
  | zero => simpa using hm
  | succ k ih =>
    have hnext := frobenius_shift L hF ih
    simpa [Function.iterate_succ_apply', pow_succ, mul_assoc,
      mul_left_comm, mul_comm] using hnext

/-- If the initial Frobenius error has positive depth, consecutive orbit terms
eventually lie in any prescribed lattice shift. -/
lemma eventually_iterate_succ_sub_mem_shift {m : M.M} {ε : ℝ}
    (hε : 0 < ε) (hm : M.F_M m - m ∈ L.shift ε) (D : ℝ) :
    ∃ N : ℕ, ∀ k ≥ N,
      (M.F_M^[k + 1]) m - (M.F_M^[k]) m ∈ L.shift D := by
  have hgrowth : Filter.Tendsto (fun k : ℕ => Λ ^ k * ε)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hε
      (tendsto_pow_atTop_atTop_of_one_lt hΛ1.out)
  have hev : ∀ᶠ k : ℕ in Filter.atTop, D ≤ Λ ^ k * ε :=
    (Filter.tendsto_atTop.1 hgrowth) D
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, fun k hk => ?_⟩
  exact L.shift_mono (hN k hk)
    (frobenius_iterate_succ_sub_mem_shift L hF hm k)

/-- Frobenius is continuous for the canonical module topology induced by a
contracting lattice. -/
lemma frobenius_continuous :
    letI : TopologicalSpace M.M :=
      canonicalTopology (RealNovikovSeries A) M.M
    Continuous M.F_M := by
  letI : TopologicalSpace M.M :=
    canonicalTopology (RealNovikovSeries A) M.M
  letI : IsTopologicalRing (RealNovikovSeries A) := is_topological_ring
  letI : IsTopologicalAddGroup M.M :=
    canonicalTopology.isTopologicalAddGroup (RealNovikovSeries A) M.M
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero,
    (L.nhds_zero_hasBasis).tendsto_iff (L.nhds_zero_hasBasis)]
  intro D _
  refine ⟨D / Λ, trivial, ?_⟩
  intro x hx
  have hshift := frobenius_shift L hF (x := x) (y := 0) (d := D / Λ) (by
    simpa using hx)
  have hΛ0 : Λ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hΛ1.out)
  have heq : Λ * (D / Λ) = D := by field_simp
  simpa [heq] using hshift

/-- A lattice element whose Frobenius error has positive depth can be corrected
to a nearby Frobenius-fixed lattice element. -/
lemma exists_fixed_point_of_sub_mem_shift {m : M.M} (hmL : m ∈ L.carrier)
    {ε : ℝ} (hε : 0 < ε) (hm : M.F_M m - m ∈ L.shift ε) :
    ∃ m' : M.M, m' ∈ L.carrier ∧ M.F_M m' = m' ∧
      m' - m ∈ L.shift ε := by
  letI : TopologicalSpace M.M :=
    canonicalTopology (RealNovikovSeries A) M.M
  letI : IsTopologicalRing (RealNovikovSeries A) := is_topological_ring
  letI : IsTopologicalAddGroup M.M :=
    canonicalTopology.isTopologicalAddGroup (RealNovikovSeries A) M.M
  letI : T2Space M.M := L.canonicalTopology_t2
  let orbit : ℕ → M.M := fun k => (M.F_M^[k]) m
  have horbit_diff (k : ℕ) : orbit (k + 1) - orbit k ∈
      L.shift (Λ ^ k * ε) := by
    simpa [orbit] using frobenius_iterate_succ_sub_mem_shift L hF hm k
  have horbit_diff_eventually (D : ℝ) :
      ∃ N : ℕ, ∀ k ≥ N, orbit (k + 1) - orbit k ∈ L.shift D := by
    simpa [orbit] using eventually_iterate_succ_sub_mem_shift L hF hε hm D
  obtain ⟨m', hm'_lim⟩ :=
    L.exists_limit_of_succ_diff_shift orbit horbit_diff_eventually
  have horbit_mem (k : ℕ) : orbit k ∈ L.carrier := by
    induction k with
    | zero => simpa [orbit] using hmL
    | succ k ih =>
      simpa [orbit, Function.iterate_succ_apply'] using frobenius_mem L hF ih
  have hm'L : m' ∈ L.carrier := by
    have hm'0 : m' ∈ L.shift 0 :=
      (L.shift_isClosed 0).mem_of_tendsto hm'_lim
        (Filter.Eventually.of_forall fun k => by simpa using horbit_mem k)
    simpa using hm'0
  have hm'_fixed : M.F_M m' = m' := by
    have hF_lim : Filter.Tendsto (fun k => M.F_M (orbit k)) Filter.atTop
        (𝓝 (M.F_M m')) := by
      simpa [Function.comp_def] using
        (frobenius_continuous L hF).tendsto m' |>.comp hm'_lim
    have hshift_lim : Filter.Tendsto (fun k => orbit (k + 1)) Filter.atTop
        (𝓝 m') :=
      (Filter.tendsto_add_atTop_iff_nat 1).2 hm'_lim
    have hF_orbit : (fun k => M.F_M (orbit k)) = fun k => orbit (k + 1) := by
      funext k
      simp [orbit, Function.iterate_succ_apply']
    rw [hF_orbit] at hF_lim
    exact tendsto_nhds_unique hF_lim hshift_lim
  have horbit_sub_mem (k : ℕ) : orbit k - m ∈ L.shift ε := by
    induction k with
    | zero => simp [orbit]
    | succ k ih =>
      have hpow : (1 : ℝ) ≤ Λ ^ k := one_le_pow₀ hΛ1.out.le
      have hdepth : ε ≤ Λ ^ k * ε := by
        calc
          ε = 1 * ε := (one_mul ε).symm
          _ ≤ Λ ^ k * ε := mul_le_mul_of_nonneg_right hpow hε.le
      have hstep : orbit (k + 1) - orbit k ∈ L.shift ε :=
        L.shift_mono hdepth (horbit_diff k)
      have heq : orbit (k + 1) - m =
          (orbit (k + 1) - orbit k) + (orbit k - m) := by abel
      rw [heq]
      exact (L.shift ε).add_mem hstep ih
  have hsub_lim : Filter.Tendsto (fun k => orbit k - m) Filter.atTop
      (𝓝 (m' - m)) := hm'_lim.sub tendsto_const_nhds
  have hm'_sub : m' - m ∈ L.shift ε :=
    (L.shift_isClosed ε).mem_of_tendsto hsub_lim
      (Filter.Eventually.of_forall horbit_sub_mem)
  exact ⟨m', hm'L, hm'_fixed, hm'_sub⟩

/-- Every lattice element has a Frobenius-fixed correction congruent to it
modulo the positive ideal. -/
lemma exists_fixed_point_mod_positive (m : L.carrier) :
    ∃ m' : L.carrier, M.F_M (m' : M.M) = m' ∧
      (m' : M.M) - m ∈
        RealNovikovPowerSeries.positiveIdeal (A := A) • L.carrier := by
  obtain ⟨ε, hε, hm⟩ := hF m m.property
  obtain ⟨m', hm'L, hm'_fixed, hm'_sub⟩ :=
    exists_fixed_point_of_sub_mem_shift L hF m.property hε hm
  refine ⟨⟨m', hm'L⟩, hm'_fixed, ?_⟩
  exact Submodule.realNovikovShift_le_positiveIdeal_smul L.carrier hε hm'_sub

/-- The lattice admits a finite generating family fixed by Frobenius. -/
lemma exists_fixed_generators :
    ∃ n : ℕ, ∃ m : Fin n → L.carrier,
      (∀ i, M.F_M (m i : M.M) = m i) ∧
      Submodule.span (RealNovikovPowerSeries A)
        (Set.range fun i => (m i : M.M)) = L.carrier := by
  letI : Module.Finite (RealNovikovPowerSeries A) L.carrier := L.finite
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin
    (R := RealNovikovPowerSeries A) (M := L.carrier)
  have hcorrect (i : Fin n) :
      ∃ m' : L.carrier, M.F_M (m' : M.M) = m' ∧
        (m' : M.M) - g i ∈
          RealNovikovPowerSeries.positiveIdeal (A := A) • L.carrier :=
    exists_fixed_point_mod_positive L hF (g i)
  choose m hm_fixed hm_diff using hcorrect
  let I := RealNovikovPowerSeries.positiveIdeal (A := A)
  let N : Submodule (RealNovikovPowerSeries A) M.M :=
    Submodule.span (RealNovikovPowerSeries A)
      (Set.range fun i => (m i : M.M))
  have hg_sup (i : Fin n) :
      (g i : M.M) ∈ N ⊔ I • L.carrier := by
    have hmN : (m i : M.M) ∈ N :=
      Submodule.subset_span ⟨i, rfl⟩
    have hmSup : (m i : M.M) ∈ N ⊔ I • L.carrier :=
      Submodule.mem_sup_left hmN
    have hdiffSup : (m i : M.M) - g i ∈ N ⊔ I • L.carrier :=
      Submodule.mem_sup_right (hm_diff i)
    have heq : (g i : M.M) =
        (m i : M.M) - ((m i : M.M) - g i) := by abel
    rw [heq]
    exact (N ⊔ I • L.carrier).sub_mem hmSup hdiffSup
  have hL_sup : L.carrier ≤ N ⊔ I • L.carrier := by
    intro y hy
    let Q : Submodule (RealNovikovPowerSeries A) L.carrier :=
      (N ⊔ I • L.carrier).comap L.carrier.subtype
    have hspan_le : Submodule.span (RealNovikovPowerSeries A)
        (Set.range g) ≤ Q := by
      apply Submodule.span_le.2
      rintro z ⟨i, rfl⟩
      exact hg_sup i
    have hy_span : (⟨y, hy⟩ : L.carrier) ∈
        Submodule.span (RealNovikovPowerSeries A) (Set.range g) := by
      rw [hg]
      exact Submodule.mem_top
    have hyQ := hspan_le hy_span
    exact hyQ
  have hLfg : L.carrier.FG :=
    (Submodule.fg_top L.carrier).mp Module.Finite.fg_top
  have hL_N : L.carrier ≤ N :=
    Submodule.le_of_le_smul_of_le_jacobson_bot
      (I := I) hLfg
      (RealNovikovPowerSeries.positiveIdeal_le_jacobson (A := A)) hL_sup
  have hN_L : N ≤ L.carrier := by
    apply Submodule.span_le.2
    rintro z ⟨i, rfl⟩
    exact (m i).property
  refine ⟨n, m, hm_fixed, ?_⟩
  change N = L.carrier
  exact le_antisymm hN_L hL_N

end NovikovIsocrystal.Lattice

end Novikov
