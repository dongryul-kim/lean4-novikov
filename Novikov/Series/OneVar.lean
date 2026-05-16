
import Novikov.Series.Basic
import Novikov.Series.Ring
import Novikov.Series.Exact
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.Algebra.UniformFilterBasis
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Subgroup.Finite


open Pointwise Filter Topology

namespace Novikov

variable {ι A : Type*} [Fintype ι]
variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S}

/-- Novikov series in one variable -/
abbrev OneVarNovikovSeries {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] (Γ : S) (A : Type*) [AddCommGroup A] :=
  NovikovSeries Γ Unit A

/-- The special case `Γ = ⊤ : AddSubgroup ℝ`, i.e. real-exponent Novikov series. -/
abbrev RealNovikovSeries (A : Type*) [AddCommGroup A] : Type _ :=
  OneVarNovikovSeries (⊤ : AddSubgroup ℝ) A

/-- Set of series with support bounded below by D -/
def filtration {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] (Γ : S) (A : Type*) [AddCommGroup A] (D : ℝ) : AddSubgroup (OneVarNovikovSeries Γ A) where
  carrier := {f | ∀ d : Unit → Γ, (d () : ℝ) < D → f d = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' hf hg d hd := by
    simp only [AddSubgroup.coe_add, Pi.add_apply]
    rw [hf d hd, hg d hd, add_zero]
  neg_mem' hf d hd := by
    simp only [AddSubgroup.coe_neg, Pi.neg_apply]
    rw [hf d hd, neg_zero]

/-- For a one-variable Novikov series, the set of exponents with nonzero coefficient
and value strictly below `D` is finite. -/
lemma finite_support_below {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S}
    {A : Type*} [AddCommGroup A] (s : OneVarNovikovSeries Γ A) (D : ℝ) :
    ({d : Unit → Γ | s.val d ≠ 0 ∧ (d () : ℝ) < D} : Set _).Finite := by
  let s_w : Unit → ℝ := fun _ => 1
  have h_eq : {d : Unit → Γ | s.val d ≠ 0 ∧ (d () : ℝ) < D} =
      {d | s.val d ≠ 0 ∧ ∑ i, s_w i * (d i : ℝ) < D} := by
    ext d; simp [s_w]
  rw [h_eq]; exact s.prop s_w (fun _ => zero_lt_one) D

lemma filtration_mono [AddCommGroup A] {D₁ D₂ : ℝ} (h : D₁ ≤ D₂) :
    filtration Γ A D₂ ≤ filtration Γ A D₁ := by
  intro f hf d hd
  exact hf d (lt_of_lt_of_le hd h)

lemma filtration_eq_of_sub_mem [AddCommGroup A] {f g : OneVarNovikovSeries Γ A} {D : ℝ}
    (h : f - g ∈ filtration Γ A D) (d : Unit → Γ) (hd : (d () : ℝ) < D) : f d = g d := by
  simpa [Pi.sub_apply, sub_eq_zero] using h d hd

lemma filtration_mul [CommRing A] {D₁ D₂ : ℝ} :
    (filtration Γ A D₁ : Set (OneVarNovikovSeries Γ A)) * (filtration Γ A D₂ : Set _) ⊆ (filtration Γ A (D₁ + D₂) : Set _) := by
  rintro f ⟨g, hg, h, hh, rfl⟩ d hd
  simp only [novikovMul_val, novikovMulFun]
  apply Finset.sum_eq_zero
  rintro ⟨d1, d2⟩ hp
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hp
  rcases hp with ⟨hsum, hg_nz, hh_nz⟩
  have h_lt : (d1 () : ℝ) < D₁ ∨ (d2 () : ℝ) < D₂ := by
    have h_eq' : (d1 () : ℝ) + (d2 () : ℝ) = (d () : ℝ) := by
      simpa [Pi.add_apply] using congrArg (fun f : Unit → Γ => (f () : ℝ)) hsum
    by_contra h_not
    push Not at h_not
    have : (d1 () : ℝ) + (d2 () : ℝ) ≥ D₁ + D₂ := add_le_add h_not.1 h_not.2
    rw [h_eq'] at this
    linarith
  cases h_lt with
  | inl h1 => rw [hg d1 h1, zero_mul]
  | inr h2 => rw [hh d2 h2, mul_zero]

lemma exists_filtration [AddCommGroup A] (f : OneVarNovikovSeries Γ A) : ∃ D : ℝ, f ∈ filtration Γ A D := by
  by_cases h0 : ∀ d : Unit → Γ, f d = 0
  · use 0
    intro d _
    apply h0
  · push Not at h0
    rcases h0 with ⟨d0, hd0⟩
    let C := (d0 () : ℝ) + 1
    let S := {d : Unit → Γ | f d ≠ 0 ∧ (d () : ℝ) < C}
    have hS : S.Finite := finite_support_below f C
    have hSne : S.Nonempty := ⟨d0, hd0, by linarith⟩
    let Sf := hS.toFinset
    let D := (Sf.image (fun d => (d () : ℝ))).min' (by
      rcases hSne with ⟨x, hx⟩
      use (x () : ℝ)
      simp only [Sf, Finset.mem_image, Set.Finite.mem_toFinset, S]
      exact ⟨x, hx, rfl⟩)
    use D
    intro d hd
    by_contra h_nz
    have hmem : d ∈ S := ⟨h_nz, lt_trans hd (by
      have hD : D ≤ (d0 () : ℝ) := by
        apply Finset.min'_le
        simp only [Sf, Finset.mem_image, Set.Finite.mem_toFinset, S]
        exact ⟨d0, ⟨hd0, by linarith⟩, rfl⟩
      linarith)⟩
    have h_ge : (d () : ℝ) ≥ D := by
      apply Finset.min'_le
      simp only [Sf, Finset.mem_image, Set.Finite.mem_toFinset, S]
      exact ⟨d, hmem, rfl⟩
    linarith

/-- The filter basis of filtrations. -/
@[reducible]
def filtrationBasis {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] (Γ : S) (A : Type*) [AddCommGroup A] : AddGroupFilterBasis (OneVarNovikovSeries Γ A) where
  sets := {s | ∃ D : ℝ, s = (filtration Γ A D : Set (OneVarNovikovSeries Γ A))}
  nonempty := ⟨(filtration Γ A 0 : Set _), ⟨0, rfl⟩⟩
  inter_sets := by
    rintro _ _ ⟨D₁, rfl⟩ ⟨D₂, rfl⟩
    use (filtration Γ A (max D₁ D₂) : Set _)
    constructor
    · use max D₁ D₂
    · intro f hf
      constructor
      · exact filtration_mono (le_max_left D₁ D₂) hf
      · exact filtration_mono (le_max_right D₁ D₂) hf
  zero' := by
    rintro _ ⟨D, rfl⟩
    exact (filtration Γ A D).zero_mem
  add' := by
    rintro _ ⟨D, rfl⟩
    refine ⟨(filtration Γ A D : Set _), ⟨D, rfl⟩, ?_⟩
    rintro f ⟨g, hg, h, hh, rfl⟩
    exact (filtration Γ A D).add_mem hg hh
  neg' := by
    rintro _ ⟨D, rfl⟩
    refine ⟨(filtration Γ A D : Set _), ⟨D, rfl⟩, ?_⟩
    intro f hf
    exact (filtration Γ A D).neg_mem hf
  conj' := by
    rintro x _ ⟨D, rfl⟩
    refine ⟨(filtration Γ A D : Set _), ⟨D, rfl⟩, ?_⟩
    intro f hf
    simp only [Set.mem_preimage, add_comm x f, add_neg_cancel_right]
    exact hf

lemma filtration_mul_mono {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S} {A : Type*} [CommRing A]
    {D₁ D₂ D : ℝ} (h : D₁ + D₂ ≥ D) {x y : OneVarNovikovSeries Γ A}
    (hx : x ∈ filtration Γ A D₁) (hy : y ∈ filtration Γ A D₂) :
    x * y ∈ filtration Γ A D :=
  filtration_mono (A := A) (Γ := Γ) h (filtration_mul ⟨x, hx, y, hy, rfl⟩)

/-- At degree 0, the product of two series in the 0-filtration equals the product
of their constant terms: `(f * g) 0 = f 0 * g 0`. -/
lemma filtration_zero_mul_val [CommRing A] {f g : OneVarNovikovSeries Γ A}
    (hf : f ∈ filtration Γ A 0) (hg : g ∈ filtration Γ A 0) : (f * g) 0 = f 0 * g 0 := by
  rw [novikovMul_val, novikovMulFun]
  let S := (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop (0 : Unit → Γ)).toFinset
  have h_nonneg {x : Unit → Γ} (hx : x ∈ fnSupport f.val) : 0 ≤ (x () : ℝ) :=
    not_lt.mp (fun hneg => hx (hf x hneg))
  have h_nonneg_g {x : Unit → Γ} (hx : x ∈ fnSupport g.val) : 0 ≤ (x () : ℝ) :=
    not_lt.mp (fun hneg => hx (hg x hneg))
  have h_mem (p : (Unit → Γ) × (Unit → Γ)) (hp : p ∈ S) : p = (0, 0) := by
    have hp_mem := by simpa [S] using hp
    rcases hp_mem with ⟨hsum, h1, h2⟩
    have hsum_zero : (p.1 () : ℝ) + (p.2 () : ℝ) = 0 := by
      have := congr_fun hsum ()
      simpa using congrArg (fun (x : ↥Γ) => (x : ℝ)) this
    have hd1_zero : (p.1 () : ℝ) = 0 := by
      nlinarith [h_nonneg h1, h_nonneg_g h2, hsum_zero]
    have hd2_zero : (p.2 () : ℝ) = 0 := by nlinarith
    have h1_eq : p.1 = (0 : Unit → Γ) := by
      ext x
      have hx : x = () := PUnit.ext x ()
      subst hx
      simpa using hd1_zero
    have h2_eq : p.2 = (0 : Unit → Γ) := by
      ext x
      have hx : x = () := PUnit.ext x ()
      subst hx
      simpa using hd2_zero
    exact Prod.ext h1_eq h2_eq
  by_cases hf0 : f 0 = 0
  · have h_empty : S = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨p, hp⟩
      have hp0 : p = (0, 0) := h_mem p hp
      subst hp0
      have hp_mem_raw : (0 : Unit → Γ) + (0 : Unit → Γ) = (0 : Unit → Γ) ∧ (0 : Unit → Γ) ∈ fnSupport f.val ∧ (0 : Unit → Γ) ∈ fnSupport g.val := by
        simpa [S] using hp
      exact hp_mem_raw.2.1 hf0
    dsimp [S] at *
    simp [h_empty, Finset.sum_empty, hf0, zero_mul]
  · by_cases hg0 : g 0 = 0
    · have h_empty : S = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨p, hp⟩
        have hp0 : p = (0, 0) := h_mem p hp
        subst hp0
        have hp_mem_raw : (0 : Unit → Γ) + (0 : Unit → Γ) = (0 : Unit → Γ) ∧ (0 : Unit → Γ) ∈ fnSupport f.val ∧ (0 : Unit → Γ) ∈ fnSupport g.val := by
          simpa [S] using hp
        exact hp_mem_raw.2.2 hg0
      dsimp [S] at *
      simp [h_empty, Finset.sum_empty, hg0, mul_zero]
    · have hS_singleton : S = {(0, 0)} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun p hp => h_mem p hp⟩
        have hsum : (0 : Unit → Γ) + 0 = (0 : Unit → Γ) := add_zero _
        have h_f0 : (0 : Unit → Γ) ∈ fnSupport f.val := fun h => hf0 h
        have h_g0 : (0 : Unit → Γ) ∈ fnSupport g.val := fun h => hg0 h
        simpa [S] using And.intro hsum (And.intro h_f0 h_g0)
      dsimp [S] at *
      rw [hS_singleton, Finset.sum_singleton]

/-- The filter basis of filtrations as a ring filter basis. -/
@[reducible]
noncomputable def ringFiltrationBasis {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] (Γ : S) (A : Type*) [CommRing A] : RingFilterBasis (OneVarNovikovSeries Γ A) where

  toAddGroupFilterBasis := filtrationBasis Γ A
  mul' := by
    rintro _ ⟨D, rfl⟩
    refine ⟨(filtration Γ A (D/2 + 1) : Set _), ⟨D/2 + 1, rfl⟩, ?_⟩
    rintro _ ⟨g, hg, h, hh, rfl⟩
    exact filtration_mul_mono (by linarith) hg hh
  mul_left' := by
    rintro x _ ⟨D, rfl⟩
    rcases exists_filtration x with ⟨Dx, hx⟩
    refine ⟨(filtration Γ A (D - Dx + 1) : Set _), ⟨D - Dx + 1, rfl⟩, ?_⟩
    intro y hy
    exact filtration_mul_mono (by linarith) hx hy
  mul_right' := by
    rintro x _ ⟨D, rfl⟩
    rcases exists_filtration x with ⟨Dx, hx⟩
    refine ⟨(filtration Γ A (D - Dx + 1) : Set _), ⟨D - Dx + 1, rfl⟩, ?_⟩
    intro y hy
    exact filtration_mul_mono (by linarith) hy hx

instance [AddCommGroup A] : TopologicalSpace (OneVarNovikovSeries Γ A) :=
  (filtrationBasis Γ A).topology

section AddCommGroup
variable [AddCommGroup A]

lemma is_topological_add_group : IsTopologicalAddGroup (OneVarNovikovSeries Γ A) :=
  (filtrationBasis Γ A).isTopologicalAddGroup

instance : UniformSpace (OneVarNovikovSeries Γ A) :=
  is_topological_add_group.rightUniformSpace (OneVarNovikovSeries Γ A)

instance : IsUniformAddGroup (OneVarNovikovSeries Γ A) :=
  isUniformAddGroup_of_addCommGroup

/-- One-variable Novikov series are complete. -/
instance : CompleteSpace (OneVarNovikovSeries Γ A) where
  complete := by
    intro B hB
    let FB := filtrationBasis Γ A
    have h_cauchy : ∀ D : ℝ, ∃ M ∈ B, ∀ x ∈ M, ∀ y ∈ M, y - x ∈ filtration Γ A D := by
      intro D
      have h := (@AddGroupFilterBasis.cauchy_iff (OneVarNovikovSeries Γ A) _ FB B).1 hB
      exact h.2 (filtration Γ A D) ⟨D, rfl⟩
    let M_spec (D : ℝ) := (h_cauchy D).choose
    let hM_spec (D : ℝ) : M_spec D ∈ B ∧ ∀ x ∈ M_spec D, ∀ y ∈ M_spec D, y - x ∈ filtration Γ A D :=
      (h_cauchy D).choose_spec
    let g_spec (D : ℝ) := (hB.1.nonempty_of_mem (hM_spec D).1).choose
    let hg_spec (D : ℝ) : g_spec D ∈ M_spec D := (hB.1.nonempty_of_mem (hM_spec D).1).choose_spec
    let f_coeff (d : Unit → Γ) : A := (g_spec ((d () : ℝ) + 1)) d
    have h_coeff_stable : ∀ (d : Unit → Γ) (D : ℝ) (M : Set (OneVarNovikovSeries Γ A)),
        (d () : ℝ) < D → M ∈ B → (∀ x ∈ M, ∀ y ∈ M, y - x ∈ filtration Γ A D) →
        ∀ g ∈ M, f_coeff d = g d := by
      intro d D M hd hM_B hM_sub g hg
      let D' := (d () : ℝ) + 1
      let M' := M_spec D'
      let hM' := hM_spec D'
      let g' := g_spec D'
      let hg' := hg_spec D'
      let M_inter := M ∩ M'
      have h_inter : M_inter ∈ B := B.inter_mem hM_B hM'.1
      rcases hB.1.nonempty_of_mem h_inter with ⟨h, h_M, h_M'⟩
      have h1 : h d = g d := filtration_eq_of_sub_mem (hM_sub g hg h h_M) d hd
      have h2 : h d = g' d :=
        filtration_eq_of_sub_mem (hM'.2 g' hg' h h_M') d (by
          dsimp [D']
          linarith)
      simpa [f_coeff, g', D'] using h2.symm.trans h1
    have h_nov : isNovikovSeries f_coeff := by
      intro s hs C
      let D := C / s () + 1
      let M := M_spec D
      let hM := hM_spec D
      rcases hB.1.nonempty_of_mem hM.1 with ⟨g, hg⟩
      have h_eq : {d | f_coeff d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} = {d | g d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} := by
        ext d
        apply and_congr_left
        intro h_sum_lt
        have h_sum : ∑ i, s i * (d i : ℝ) = s () * (d () : ℝ) := by
          simp
        have h_D : (d () : ℝ) < D := by
          dsimp [D]
          rw [h_sum] at h_sum_lt
          have h_pos : 0 < s () := hs ()
          -- Use lt_div_iff₀ for fields
          have : (d () : ℝ) < C / s () := (lt_div_iff₀ h_pos).mpr (by rwa [mul_comm] at h_sum_lt)
          linarith
        rw [h_coeff_stable d D M h_D hM.1 hM.2 g hg]
      change {d | f_coeff d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C}.Finite
      rw [h_eq]
      exact g.prop s hs C
    let f : OneVarNovikovSeries Γ A := ⟨f_coeff, h_nov⟩
    use f
    rw [FB.nhds_eq]
    apply (FB.hasBasis f).ge_iff.2
    intro V hV
    rcases hV with ⟨D, rfl⟩
    let M := M_spec D
    let hM := hM_spec D
    apply B.sets_of_superset hM.1
    intro g hg
    simp only [Set.mem_image]
    use g - f
    constructor
    · intro d hd
      simp only [AddSubgroup.coe_sub, Pi.sub_apply, sub_eq_zero]
      exact (h_coeff_stable d D M hd hM.1 hM.2 g hg).symm
    · simp only [add_sub_cancel]

lemma filtration_add {D₁ D₂ : ℝ} : (filtration Γ A D₁ : Set (OneVarNovikovSeries Γ A)) + (filtration Γ A D₂ : Set _) ⊆ (filtration Γ A (min D₁ D₂) : Set _) := by
  rintro f ⟨g, hg, h, hh, rfl⟩ d hd
  simp only [AddSubgroup.coe_add, Pi.add_apply]
  rw [hg d (lt_of_lt_of_le hd (min_le_left _ _)), hh d (lt_of_lt_of_le hd (min_le_right _ _)), add_zero]

/-- The topology on `OneVarNovikovSeries` is Hausdorff: the intersection of all
filtrations is `{0}`, so the uniformity separates points. -/
instance : T2Space (OneVarNovikovSeries Γ A) := by
  rw [R1Space.t2Space_iff_t0Space, t0Space_iff_uniformity]
  intro x y hxy
  ext d
  have h_uniform : (filtration Γ A ((d () : ℝ) + 1) : Set _) ∈
      𝓝 (0 : OneVarNovikovSeries Γ A) :=
    (filtrationBasis Γ A).nhds_zero_hasBasis.mem_of_mem ⟨_, rfl⟩
  have h_ent : {p : OneVarNovikovSeries Γ A × OneVarNovikovSeries Γ A | p.2 - p.1 ∈
      filtration Γ A ((d () : ℝ) + 1)} ∈ uniformity _ := by
    rw [uniformity_eq_comap_nhds_zero]
    exact Filter.mem_comap.mpr ⟨_, h_uniform, fun p hp => hp⟩
  have h_in := hxy _ h_ent
  simpa [eq_comm] using filtration_eq_of_sub_mem h_in d (by linarith)

/-- If the consecutive differences of a sequence are eventually in arbitrarily
small filtrations, then the sequence is Cauchy. -/
lemma cauchySeq_of_succ_diff_filtration (b_seq : ℕ → OneVarNovikovSeries Γ A)
    (h_succ : ∀ D : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      b_seq (n + 1) - b_seq n ∈ filtration Γ A D) : CauchySeq b_seq := by
  let FB := filtrationBasis Γ A
  apply (FB.cauchy_iff (F := Filter.map b_seq atTop)).mpr
  constructor
  · exact (atTop_neBot (α := ℕ)).map b_seq
  · intro U hU
    rcases hU with ⟨D, rfl⟩
    rcases h_succ D with ⟨N, hN⟩
    have hmem : {x | ∃ n ≥ N, b_seq n = x} ∈ Filter.map b_seq Filter.atTop := by
      rw [Filter.mem_map]
      apply Filter.mem_of_superset (Filter.mem_atTop N)
      intro k hk; exact ⟨k, hk, rfl⟩
    refine ⟨{x | ∃ n ≥ N, b_seq n = x}, hmem, ?_⟩
    rintro x ⟨m, hm, rfl⟩ y ⟨n, hn, rfl⟩
    by_cases hmn : m ≤ n
    · rw [← Finset.sum_Ico_sub (f := b_seq) hmn]
      refine AddSubgroup.sum_mem (filtration Γ A D) (t := Finset.Ico m n) fun i hi => ?_
      rcases Finset.mem_Ico.mp hi with ⟨hi_m, _⟩
      have hi_ge_N : N ≤ i := le_trans hm hi_m
      exact hN i hi_ge_N
    · have hnm : n ≤ m := by omega
      have hsum := AddSubgroup.sum_mem (filtration Γ A D) (t := Finset.Ico n m) fun i hi => by
        rcases Finset.mem_Ico.mp hi with ⟨hi_n, _⟩
        have hi_ge_N : N ≤ i := le_trans hn hi_n
        exact hN i hi_ge_N
      have h_eq : b_seq n - b_seq m =
          -((Finset.sum (Finset.Ico n m : Finset ℕ) fun i => b_seq (i + 1) - b_seq i)) := by
        rw [Finset.sum_Ico_sub (f := b_seq) hnm, neg_sub]
      rw [h_eq]
      exact (filtration Γ A D).neg_mem hsum

/-- The "coefficient at `d`" projection `s ↦ s.val d` from `OneVarNovikovSeries Γ A` to `A`
is continuous when `A` has the discrete topology. -/
lemma coefficient_continuous [TopologicalSpace A] [DiscreteTopology A]
    (d : Unit → Γ) :
    Continuous (fun s : OneVarNovikovSeries Γ A => s.val d) := by
  haveI := is_topological_add_group (Γ := Γ) (A := A)
  refine continuous_iff_continuousAt.mpr fun s₀ => ?_
  -- Discrete codomain: 𝓝 (f s₀) = pure (f s₀), so ContinuousAt is eventual constancy.
  change Tendsto (fun s : OneVarNovikovSeries Γ A => s.val d) (𝓝 s₀) (𝓝 (s₀.val d))
  rw [show (𝓝 (s₀.val d) : Filter A) = pure (s₀.val d) from
        congrFun (nhds_discrete (α := A)) _,
      Filter.tendsto_pure]
  -- Local constancy: use neighborhood `s₀ + filtration Γ A ((d () : ℝ) + 1)`.
  have h_nhds := (filtrationBasis Γ A).nhds_hasBasis (x₀ := s₀)
  rw [h_nhds.eventually_iff]
  refine ⟨(filtration Γ A ((d () : ℝ) + 1) : Set _), ⟨_, rfl⟩, ?_⟩
  intro s hs
  -- `s ∈ s₀ + filtration` means `s = s₀ + t` for some `t ∈ filtration`.
  obtain ⟨t, ht, rfl⟩ := hs
  change s₀.val d + t.val d = s₀.val d
  rw [ht d (by linarith), add_zero]

/-- The image of `Novikov.map f` is closed in `OneVarNovikovSeries Γ B`, for any
additive group homomorphism `f : A →+ B` when `B` has the discrete topology.
In particular, if `B` is a subgroup of `A` then `OneVarNovikovSeries Γ B` embeds
as a closed subgroup of `OneVarNovikovSeries Γ A`. -/
lemma map_range_closed {B : Type*} [AddCommGroup B]
    [TopologicalSpace B] [DiscreteTopology B] (f : A →+ B) :
    IsClosed (Set.range (Novikov.map (Γ := Γ) (ι := Unit) f) :
      Set (OneVarNovikovSeries Γ B)) := by
  -- Range of `Novikov.map f` = `⋂ d, {s | s.val d ∈ Set.range f}`, closed as
  -- intersection of preimages of closed (discrete codomain) sets under continuous
  -- coefficient projections.
  have h_eq : (Set.range (Novikov.map (Γ := Γ) (ι := Unit) f) :
      Set (OneVarNovikovSeries Γ B)) =
      ⋂ d, {s : OneVarNovikovSeries Γ B | s.val d ∈ Set.range f} := by
    ext s
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨s', rfl⟩ d
      exact ⟨s'.val d, (Novikov.map_apply f s' d).symm⟩
    · intro hs
      have hs_range : ∀ d, s.val d ∈ f.range := hs
      rcases Novikov.exists_preimage_of_range s hs_range with ⟨g_val, hg_eq, hg_supp⟩
      have hg_nov : isNovikovSeries g_val := is_novikov_series_of_subset s.prop hg_supp
      refine ⟨⟨g_val, hg_nov⟩, ?_⟩
      ext d
      rw [Novikov.map_apply]
      exact hg_eq d
  rw [h_eq]
  apply isClosed_iInter
  intro d
  exact IsClosed.preimage (coefficient_continuous (A := B) d) (isClosed_discrete _)

end AddCommGroup

/-- `lmap f` is continuous in the t-adic topology for any `R`-linear map `f : M →ₗ[R] N`. -/
lemma lmap_continuous {R M N : Type*} [Semiring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    Continuous (lmap (Γ := Γ) (ι := Unit) f) := by
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero,
      (filtrationBasis Γ M).nhds_zero_hasBasis.tendsto_iff
        (filtrationBasis Γ N).nhds_zero_hasBasis]
  intro V ⟨D, hV⟩; subst hV
  refine ⟨filtration Γ M D, ⟨D, rfl⟩, ?_⟩
  intro x hx d hd
  rw [lmap_apply, hx d hd, map_zero]

/-- If `f : M →ₗ[R] N` is injective, then `lmap f` is a topological embedding
in the t-adic topology. -/
lemma lmap_isEmbedding {R M N : Type*} [Semiring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Topology.IsEmbedding (lmap (Γ := Γ) (ι := Unit) f) := by
  have h_cont : Continuous (lmap (Γ := Γ) (ι := Unit) f) := lmap_continuous f
  have h_inj : Function.Injective (lmap (Γ := Γ) (ι := Unit) f) :=
    lmap_injective f hf
  -- Show that the filtrations match: preimage of codomain filtration = domain filtration
  have h_filt (D : ℝ) : (lmap (Γ := Γ) (ι := Unit) f)⁻¹'
      (filtration Γ N D : Set (OneVarNovikovSeries Γ N)) =
      (filtration Γ M D : Set (OneVarNovikovSeries Γ M)) := by
    ext x
    constructor
    · intro h d hd
      have hx := h d hd
      rw [lmap_apply] at hx
      -- hx : f (x.val d) = 0
      exact hf (hx.trans (map_zero f).symm)
    · intro h d hd
      have hx := h d hd
      rw [lmap_apply, hx, map_zero]
  -- Using `IsTopologicalAddGroup.isInducing_iff_nhds_zero`, we show `lmap f` is inducing
  have h_inducing : Topology.IsInducing (lmap (Γ := Γ) (ι := Unit) f) := by
    haveI : IsTopologicalAddGroup (OneVarNovikovSeries Γ M) :=
      is_topological_add_group (A := M)
    haveI : IsTopologicalAddGroup (OneVarNovikovSeries Γ N) :=
      is_topological_add_group (A := N)
    refine (IsTopologicalAddGroup.isInducing_iff_nhds_zero
      (f := (lmap (Γ := Γ) (ι := Unit) f).toAddMonoidHom)).mpr ?_
    apply Filter.ext
    intro s
    rw [Filter.mem_comap]
    let FB_M : AddGroupFilterBasis (OneVarNovikovSeries Γ M) :=
      filtrationBasis Γ M
    let FB_N : AddGroupFilterBasis (OneVarNovikovSeries Γ N) :=
      filtrationBasis Γ N
    rw [FB_M.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨t, ⟨D, ht⟩, hts⟩
      subst ht
      refine ⟨filtration Γ N D, FB_N.nhds_zero_hasBasis.mem_of_mem ⟨D, rfl⟩, ?_⟩
      dsimp
      rw [h_filt D]
      exact hts
    · rintro ⟨u, hu, hus⟩
      rw [FB_N.nhds_zero_hasBasis.mem_iff] at hu
      rcases hu with ⟨t, ⟨D, ht⟩, htu⟩
      subst ht
      refine ⟨filtration Γ M D, ⟨D, rfl⟩, ?_⟩
      calc
        filtration Γ M D = (lmap (Γ := Γ) (ι := Unit) f)⁻¹' (filtration Γ N D) :=
          (h_filt D).symm
        _ ⊆ (lmap (Γ := Γ) (ι := Unit) f)⁻¹' u := Set.preimage_mono htu
        _ ⊆ s := hus
  exact Topology.IsEmbedding.mk h_inducing h_inj

section CommRing
variable [CommRing A]

lemma is_topological_ring : IsTopologicalRing (OneVarNovikovSeries Γ A) :=
  (ringFiltrationBasis Γ A).isTopologicalRing

lemma filtration_smul (a : A) {D : ℝ} {f : OneVarNovikovSeries Γ A}
    (hf : f ∈ filtration Γ A D) : a • f ∈ filtration Γ A D := by
  intro d hd
  change (a • f.val) d = 0
  rw [Pi.smul_apply, hf d hd, smul_zero]

/-- `filtration` as a submodule. -/
def filtrationSubmodule (D : ℝ) : Submodule A (OneVarNovikovSeries Γ A) where
  carrier := filtration Γ A D
  add_mem' hf hg := (filtration Γ A D).add_mem hf hg
  zero_mem' := (filtration Γ A D).zero_mem
  smul_mem' a _ hf := filtration_smul a hf

lemma is_linear_topology : IsLinearTopology A (OneVarNovikovSeries Γ A) := by
  let s : ℝ → Submodule A (OneVarNovikovSeries Γ A) := fun D => filtrationSubmodule D
  refine IsLinearTopology.mk_of_hasBasis (R := A) (s := s) (p := fun _ => True) ?_
  have h := (filtrationBasis Γ A).nhds_zero_hasBasis
  rw [Filter.hasBasis_iff]
  intro t
  rw [h.mem_iff]
  constructor
  · rintro ⟨V, hV, hVt⟩
    rcases hV with ⟨D, rfl⟩
    exact ⟨D, trivial, hVt⟩
  · rintro ⟨D, -, hDt⟩
    refine ⟨filtration Γ A D, ⟨D, rfl⟩, hDt⟩

end CommRing

end Novikov
