import Novikov.Series.OneVar
import Novikov.Series.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Module.Basic
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Ring

import Mathlib.Algebra.Group.Pointwise.Set.Basic

open Finset Topology Pointwise

namespace Novikov

variable {S : Type*} [SetLike S ℝ] [AddSubgroupClass S ℝ] {Γ : S}

section CommRing

variable {A : Type*} [CommRing A]

/-- The support of a one-variable Novikov series. -/
def support (f : OneVarNovikovSeries Γ A) : Set (Unit → Γ) :=
  {d | f d ≠ 0}

lemma support_finite_below (f : OneVarNovikovSeries Γ A) (C : ℝ) :
    {d | d ∈ support f ∧ (d () : ℝ) < C}.Finite := by
  let s : Unit → ℝ := fun _ => 1
  have hs : ∀ i, 0 < s i := fun _ => zero_lt_one
  have h_sum : ∀ d : Unit → Γ, ∑ i, s i * (d i : ℝ) = (d () : ℝ) := by
    intro d
    simp [s, Finset.sum_singleton]
  have h_eq : {d | d ∈ support f ∧ (d () : ℝ) < C} = {d | f.val d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} := by
    ext d
    simp only [support, Set.mem_setOf_eq, h_sum]
  rw [h_eq]
  exact f.property s hs C

lemma support_has_min (f : OneVarNovikovSeries Γ A) (hf : f ≠ 0) :
    ∃ d ∈ support f, ∀ d' ∈ support f, (d () : ℝ) ≤ (d' () : ℝ) := by
  classical
  obtain ⟨d0, hd0⟩ : ∃ d0, f d0 ≠ 0 := by
    contrapose! hf
    ext d
    exact hf d
  let S := {d | d ∈ support f ∧ (d () : ℝ) ≤ (d0 () : ℝ)}
  have hS_fin : S.Finite := by
    apply Set.Finite.subset (support_finite_below f ((d0 () : ℝ) + 1))
    rintro d ⟨hd_supp, hd_le⟩
    exact ⟨hd_supp, by linarith⟩
  have hS_ne : S.Nonempty := ⟨d0, hd0, le_refl _⟩
  let Sf := hS_fin.toFinset
  let d_min_val := (Sf.image (fun d => (d () : ℝ))).min' (by
    rcases hS_ne with ⟨x, hx⟩
    use (x () : ℝ)
    simp only [Sf, Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨x, hx, rfl⟩)
  have h_mem_min : d_min_val ∈ Sf.image (fun d => (d () : ℝ)) := Finset.min'_mem _ _
  obtain ⟨d, hd, hd_eq⟩ := Finset.mem_image.1 h_mem_min
  use d
  have hd_supp : d ∈ support f := by
    simp only [Sf, Set.Finite.mem_toFinset] at hd
    exact hd.1
  refine ⟨hd_supp, ?_⟩
  intro d' hd'_supp
  by_cases h_le : (d' () : ℝ) ≤ (d0 () : ℝ)
  · have hd'_Sf : d' ∈ Sf := by
      simp only [Sf, Set.Finite.mem_toFinset]
      exact ⟨hd'_supp, h_le⟩
    have h_min := Finset.min'_le (Sf.image (fun d => (d () : ℝ))) (d' () : ℝ) (Finset.mem_image_of_mem _ hd'_Sf)
    rwa [hd_eq]
  · have : (d () : ℝ) ≤ (d0 () : ℝ) := by
      simp only [Sf, Set.Finite.mem_toFinset] at hd
      exact hd.2
    linarith

/-- The minimum degree of a nonzero Novikov series. -/
noncomputable def minDegree (f : OneVarNovikovSeries Γ A) : Unit → Γ :=
  open Classical in
  if hf : f = 0 then 0 else (support_has_min f hf).choose

lemma minDegree_mem (f : OneVarNovikovSeries Γ A) (hf : f ≠ 0) :
    minDegree f ∈ support f := by
  classical
  simp only [minDegree, hf, ↓reduceDIte]
  exact (support_has_min f hf).choose_spec.1

lemma minDegree_le (f : OneVarNovikovSeries Γ A) (hf : f ≠ 0) :
    ∀ d ∈ support f, (minDegree f () : ℝ) ≤ (d () : ℝ) := by
  classical
  simp only [minDegree, hf, ↓reduceDIte]
  exact (support_has_min f hf).choose_spec.2

/-- The coefficient of the minimum degree. -/
noncomputable def leadingCoeff (f : OneVarNovikovSeries Γ A) : A :=
  f (minDegree f)

lemma leadingCoeff_ne_zero (f : OneVarNovikovSeries Γ A) (hf : f ≠ 0) :
    leadingCoeff f ≠ 0 :=
  minDegree_mem f hf

/-- If `d` has degree strictly less than the minDegree, then `f d = 0`. -/
lemma minDegree_lt_apply (f : OneVarNovikovSeries Γ A) (hf : f ≠ 0) (d : Unit → Γ)
    (hd : (d () : ℝ) < (minDegree f () : ℝ)) : f d = 0 := by
  by_contra! h
  have h_supp : d ∈ support f := h
  have h_le := minDegree_le f hf d h_supp
  linarith

/-- A series is "positive" if its support is contained in (0, ∞). -/
def IsPositive (f : OneVarNovikovSeries Γ A) : Prop :=
  ∀ d : Unit → Γ, (d () : ℝ) ≤ 0 → f d = 0

lemma support_has_min_pos (f : OneVarNovikovSeries Γ A) (hf : f ≠ 0) (hpos : IsPositive f) :
    0 < (minDegree f () : ℝ) := by
  have h_mem := minDegree_mem f hf
  have h_supp : minDegree f ∈ support f := h_mem
  by_contra! h_le
  have h_zero := hpos (minDegree f) h_le
  simp only [support, Set.mem_setOf_eq] at h_supp
  exact h_supp h_zero

lemma geometricSeries_pow_supp_le (g : OneVarNovikovSeries Γ A) (hg0 : g ≠ 0) (ε : ℝ) (hε : (minDegree g () : ℝ) = ε) :
    ∀ (n : ℕ) d, (g ^ n : NovikovSeries Γ Unit A) d ≠ 0 → n * ε ≤ (d () : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro d hd
    have : d = 0 := by
      rw [pow_zero] at hd
      have h1 : (1 : OneVarNovikovSeries Γ A) d = if d = 0 then 1 else 0 := rfl
      rw [h1] at hd
      by_contra h; rw [if_neg h] at hd; contradiction
    subst this; simp
  | succ n ih =>
    intro d hd; rw [pow_succ] at hd
    have h_supp : d ∈ ((g ^ n) * g).support := hd
    have h_mem := support_mul_subset (g ^ n) g (AddMonoidHom.mul) h_supp
    rw [Set.mem_add] at h_mem
    obtain ⟨d1, hd1, d2, hd2, rfl⟩ := h_mem
    rw [Pi.add_apply, Nat.cast_succ, add_mul, one_mul]
    apply add_le_add
    · exact ih d1 hd1
    · rw [← hε]; exact minDegree_le g hg0 d2 hd2

lemma positiveTopNilp (g : OneVarNovikovSeries Γ A) (hg : IsPositive g) : IsTopologicallyNilpotent g := by
  refine (Novikov.filtrationBasis Γ A).nhds_zero_hasBasis.tendsto_right_iff.2 ?_
  intro V hV
  rcases hV with ⟨D, rfl⟩
  rw [Filter.eventually_atTop]
  by_cases hg0 : g = 0
  · use 1
    intro n hn
    rw [hg0, zero_pow (by linarith)]
    exact (Novikov.filtration Γ A D).zero_mem
  · let ε := (minDegree g () : ℝ)
    have hε : 0 < ε := support_has_min_pos g hg0 hg
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℝ) ≥ D / ε := exists_nat_ge (D / ε)
    use N
    intro n hn
    have h_le : D ≤ n * ε := by
      calc D = (D / ε) * ε := by rw [div_mul_cancel₀ _ hε.ne']
           _ ≤ (N : ℝ) * ε := by gcongr
           _ ≤ n * ε := by gcongr
    apply Novikov.filtration_mono h_le
    intro d hd
    by_contra h_nz
    have h_ge := geometricSeries_pow_supp_le g hg0 ε rfl n d h_nz
    linarith

/-- The geometric series Σ g^n, defined via `tsum` using that `g` is topologically
nilpotent (`positiveTopNilp`) and that `OneVarNovikovSeries` is a complete uniform
linearly topologized ring. -/
noncomputable def geometricSeries (g : OneVarNovikovSeries Γ A) (hg : IsPositive g) :
    OneVarNovikovSeries Γ A :=
  have _hnil : IsTopologicallyNilpotent g := positiveTopNilp g hg
  ∑' n : ℕ, g ^ n

/-- The powers of a positive series are summable. The partial sums form a Cauchy
filter because `g` is topologically nilpotent (`positiveTopNilp`) and the topology
is generated by additive subgroups (the filtration). -/
lemma geometric_summable (g : OneVarNovikovSeries Γ A) (hg : IsPositive g) :
    Summable (fun n : ℕ => (g ^ n : OneVarNovikovSeries Γ A)) := by
  have hnil : IsTopologicallyNilpotent g := positiveTopNilp g hg
  rw [summable_iff_vanishing]
  intro e he
  obtain ⟨V, hV, hVe⟩ :=
    ((Novikov.filtrationBasis Γ A).nhds_zero_hasBasis).mem_iff.mp he
  obtain ⟨D, rfl⟩ := hV
  have hV_nhds : (Novikov.filtration Γ A D : Set _) ∈
      𝓝 (0 : OneVarNovikovSeries Γ A) :=
    (Novikov.filtrationBasis Γ A).nhds_zero_hasBasis.mem_of_mem ⟨D, rfl⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hnil hV_nhds)
  refine ⟨Finset.range N, fun t ht => hVe (sum_mem fun i hi => ?_)⟩
  apply hN
  by_contra h
  push Not at h
  exact Finset.disjoint_left.mp ht hi (Finset.mem_range.mpr h)

lemma geometricSeries_mul_inv (g : OneVarNovikovSeries Γ A) (hg : IsPositive g) :
    (1 - g) * geometricSeries g hg = 1 := by
  haveI : IsTopologicalRing (OneVarNovikovSeries Γ A) :=
    Novikov.is_topological_ring
  change (1 - g) * (∑' n : ℕ, g ^ n) = 1
  exact (geometric_summable g hg).one_sub_mul_tsum_pow

end CommRing

section Field

variable {A : Type*} [Field A]

lemma isPositive_one_sub_norm (f : OneVarNovikovSeries Γ A) (hf : f ≠ 0) :
    let d := minDegree f
    let a := leadingCoeff f
    let inv_d_val : Unit → Γ := fun () => ⟨- (d () : ℝ), NegMemClass.neg_mem (Subtype.mem (d ()))⟩
    IsPositive (1 - (novikovMonomial a⁻¹ inv_d_val * f : OneVarNovikovSeries Γ A)) := by
  intro d a inv_d_val e he
  set f_norm := novikovMonomial a⁻¹ inv_d_val * f
  dsimp only [AddSubgroupClass.coe_sub, Pi.sub_apply]
  let h_mul := novikovSeriesMul_left_monomial a⁻¹ f AddMonoidHom.mul inv_d_val (e - inv_d_val)
  have h_one : (1 : OneVarNovikovSeries Γ A) e = if e = 0 then (1 : A) else 0 := by
    rw [show (1 : OneVarNovikovSeries Γ A) = novikovOne by rfl]
    simp [novikovOne_val]
  rw [h_one]
  -- Use `novikovSeriesMul_left_monomial` to calculate coefficients
  have h_add : inv_d_val + (e - inv_d_val) = e := by ext x; simp
  have h_mul_val : (f_norm.val (inv_d_val + (e - inv_d_val)) : A) = a⁻¹ * f (e - inv_d_val) := h_mul
  rw [h_add] at h_mul_val
  change (if e = 0 then (1 : A) else 0) - f_norm e = 0
  rw [h_mul_val]
  by_cases heq : e = 0
  · subst heq
    have hd_eq : 0 - inv_d_val = d := by ext x; simp [inv_d_val]
    rw [hd_eq]
    have ha : f d = a := rfl
    rw [ha, inv_mul_cancel₀ (leadingCoeff_ne_zero f hf)]
    simp
  · rw [if_neg heq, zero_sub, neg_eq_zero, mul_eq_zero]
    right
    have h_lt : (e () : ℝ) < 0 := by
      apply lt_of_le_of_ne he
      intro h
      apply heq
      ext x
      cases x
      have h2 : e () = 0 := ZeroMemClass.coe_eq_zero.mp h
      rw [h2]
      rfl
    by_contra h_nz
    have h_min := minDegree_le f hf _ h_nz
    have h_sub : ((e - inv_d_val) () : ℝ) = (e () : ℝ) + (d () : ℝ) := by
      simp [inv_d_val, Pi.sub_apply, sub_neg_eq_add]
    linarith

/-- OneVarNovikovSeries forms a field. -/
noncomputable instance novikovField : Field (OneVarNovikovSeries Γ A) :=
  IsField.toField {
    exists_pair_ne := ⟨0, 1, fun h => by 
      have h1 : (1 : OneVarNovikovSeries Γ A) 0 = 1 := by
        change (novikovOne : NovikovSeries Γ Unit A) 0 = 1
        simp
      have h0 : (0 : OneVarNovikovSeries Γ A) 0 = 0 := rfl
      rw [← h] at h1
      rw [h0] at h1
      exact one_ne_zero h1.symm ⟩
    mul_comm := mul_comm
    mul_inv_cancel := fun {f} hf => by
      let d := minDegree f
      let a := leadingCoeff f
      let inv_d_val : Unit → Γ := fun () => ⟨- (d () : ℝ), NegMemClass.neg_mem (Subtype.mem (d ()))⟩
      let g := 1 - (novikovMonomial a⁻¹ inv_d_val * f : OneVarNovikovSeries Γ A)
      let f_inv := (novikovMonomial a⁻¹ inv_d_val) * geometricSeries g (isPositive_one_sub_norm f hf)
      use f_inv
      have h_inv := geometricSeries_mul_inv g (isPositive_one_sub_norm f hf)
      have hg : 1 - g = novikovMonomial a⁻¹ inv_d_val * f := by
        ext d'
        simp [g, OneVarNovikovSeries]
      rw [show f * f_inv = 1 by
        dsimp [f_inv]
        rw [← mul_assoc, mul_comm f, ← hg, h_inv]]
  }

end Field

end Novikov
