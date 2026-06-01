import Novikov.Series.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open BigOperators
open Finset

/-!
# Functoriality in the set of variables

Given a map between two variable sets `f : ι → ι'`, there is a corresponding map
`NovikovSeries Γ ι A → NovikovSeries Γ ι' A` given by substituting the variables.
This construction is functorial and is a ring homomorphism when `A` is a ring.
-/

namespace Novikov

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']
variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S}

section Basic

variable {A : Type*} [AddCommGroup A]

/-- Pushforward of exponent vectors along a map of variable sets. -/
noncomputable def pushExponents (f : ι → ι') (g : ι → Γ) : ι' → Γ :=
  open Classical in
  fun j => Finset.sum (univ.filter (fun i => f i = j)) (fun i => g i)

/-- For a fixed `g' : ι' → Γ`, the set of `g : ι → Γ` such that `pushExponents f g = g'`
and `s g ≠ 0` is finite. -/
lemma finite_substitution_support (f : ι → ι') (s : NovikovSeries Γ ι A) (g' : ι' → Γ) :
    {g : ι → Γ | pushExponents f g = g' ∧ s g ≠ 0}.Finite := by
  let w : ι → ℝ := fun _ => 1
  have hw : ∀ i, 0 < w i := fun _ => zero_lt_one
  let C : ℝ := (∑ j, (g' j : ℝ)) + 1
  apply Set.Finite.subset (s.prop w hw C)
  intro g hg
  simp only [Set.mem_setOf_eq] at hg ⊢
  refine ⟨hg.2, ?_⟩
  have h_sum : ∑ i, (g i : ℝ) = ∑ j, (g' j : ℝ) := by
    classical
    rw [← sum_fiberwise univ f (fun i => (g i : ℝ))]
    apply sum_congr rfl
    intro j _
    simpa [pushExponents, AddSubmonoidClass.coe_finsetSum] using
      congrArg (fun f : ι' → Γ => (f j : ℝ)) hg.1
  simp only [w, one_mul]
  rw [h_sum]
  linarith

/-- Membership in the substitution support finset, unfolded to the explicit condition. -/
lemma mem_finite_substitution_support {f : ι → ι'} {s : NovikovSeries Γ ι A} {g' : ι' → Γ} {g} :
    g ∈ (finite_substitution_support f s g').toFinset ↔
    pushExponents f g = g' ∧ s g ≠ 0 := by
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]

/-- The underlying function of the substitution map. -/
noncomputable def substituteFun (f : ι → ι') (s : NovikovSeries Γ ι A) (g' : ι' → Γ) : A :=
  Finset.sum (finite_substitution_support f s g').toFinset (fun g => s g)

/-- The Novikov finiteness condition for the substituted series. -/
lemma is_novikov_series_substituteFun (f : ι → ι') (s : NovikovSeries Γ ι A) :
    isNovikovSeries (substituteFun f s) := by
  intro w' hw' C
  let w : ι → ℝ := fun i => w' (f i)
  have hw : ∀ i, 0 < w i := fun i => hw' (f i)
  let S := {g | s g ≠ 0 ∧ ∑ i, w i * (g i : ℝ) < C}
  have hS : S.Finite := s.prop w hw C
  let target := {g' | substituteFun f s g' ≠ 0 ∧ ∑ j, w' j * (g' j : ℝ) < C}
  have h_sub : target ⊆ pushExponents f '' S := by
    intro g' hg'
    obtain ⟨g, hg_mem, hg_nz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg'.1
    rw [mem_finite_substitution_support] at hg_mem
    refine ⟨g, ⟨hg_nz, ?_⟩, hg_mem.1⟩
    have h_eq : ∑ i, w i * (g i : ℝ) = ∑ j, w' j * (g' j : ℝ) := by
      rw [← hg_mem.1]
      simp only [pushExponents, w]
      classical
      rw [← sum_fiberwise univ f (fun i => w' (f i) * (g i : ℝ))]
      apply sum_congr rfl
      intro j _
      rw [AddSubmonoidClass.coe_finsetSum, mul_sum]
      apply sum_congr rfl
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      rw [hi]
    rw [h_eq]
    exact hg'.2
  exact hS.image (pushExponents f) |>.subset h_sub

/-- The map on Novikov series induced by a map of variable sets. -/
noncomputable def substitute (f : ι → ι') (s : NovikovSeries Γ ι A) : NovikovSeries Γ ι' A :=
  ⟨substituteFun f s, is_novikov_series_substituteFun f s⟩

/-- Substitution along the identity map is the identity. -/
lemma substitute_id (s : NovikovSeries Γ ι A) :
    substitute (id : ι → ι) s = s := by
  ext d
  simp only [substitute, substituteFun]
  have h_push (g : ι → Γ) : pushExponents (id : ι → ι) g = g := by
    funext j
    simp only [pushExponents, id_eq]
    apply sum_eq_single j
    · intro i hi hne
      simp only [mem_filter, mem_univ, true_and] at hi
      exact (hne hi).elim
    · intro h
      simp at h
  rw [sum_eq_single d]
  · intro g hg hne
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, h_push] at hg
    exact (hne hg.1).elim
  · intro h
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, h_push, true_and, ne_eq, not_not] at h
    exact h

lemma pushExponent_comp {ι'' : Type*} (f : ι → ι') (g : ι' → ι'') (d : ι → Γ) :
    pushExponents (g ∘ f) d = pushExponents g (pushExponents f d) := by
  funext k
  simp only [pushExponents]
  symm
  classical
  apply (sum_sigma (univ.filter (fun j => g j = k)) (fun j => univ.filter (fun i => f i = j)) (fun p => d p.2)).symm.trans
  apply sum_bij (fun p _ => p.2)
  · rintro ⟨j, i⟩ h; simp only [mem_sigma, mem_filter, mem_univ, true_and] at h; simp [h]
  · rintro ⟨j, i⟩ h1 ⟨j', i'⟩ h2 rfl
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at h1 h2
    rw [← h1.2, ← h2.2]
  · intro i hi; simp only [mem_filter, mem_univ, true_and] at hi; exact ⟨⟨f i, i⟩, mem_sigma.2 ⟨by simpa, by simp⟩, rfl⟩
  · simp

/-- Substitution is functorial. -/
lemma substitute_comp {ι'' : Type*} [Fintype ι''] (f : ι → ι') (g : ι' → ι'') (s : NovikovSeries Γ ι A) :
    substitute (g ∘ f) s = substitute g (substitute f s) := by
  classical
  ext d''
  unfold substitute substituteFun
  simp only
  simp only [pushExponent_comp]
  set S_total := (finite_substitution_support (g ∘ f) s d'').toFinset with hS_total
  set S_h : (ι' → Γ) → Finset (ι → Γ) :=
    fun x => (finite_substitution_support f s x).toFinset with hS_h
  set S_g := (finite_substitution_support g (substitute f s) d'').toFinset with hS_g
  let S_x_large := S_total.image (pushExponents f)
  have h1 : ∑ h ∈ S_total, s h = ∑ x ∈ S_x_large, ∑ h ∈ S_h x, s h := by
    have h_maps : ∀ h ∈ S_total, pushExponents f h ∈ S_x_large :=
      fun h hh => Finset.mem_image.mpr ⟨h, hh, rfl⟩
    rw [← Finset.sum_fiberwise_of_maps_to h_maps (fun h => s h)]
    refine Finset.sum_congr rfl fun x hx => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext h
    simp only [S_h, S_total, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    refine ⟨fun ⟨⟨_, h_snz⟩, h_fh⟩ => ⟨h_fh, h_snz⟩,
      fun ⟨h_fh, h_snz⟩ => ⟨⟨?_, h_snz⟩, h_fh⟩⟩
    simp only [S_x_large, Finset.mem_image, S_total, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq] at hx
    obtain ⟨h0, ⟨h0_gf, _⟩, h0_fh⟩ := hx
    rw [pushExponent_comp, h_fh, ← h0_fh, ← pushExponent_comp]
    exact h0_gf
  have h2 : ∑ x ∈ S_g, ∑ h ∈ S_h x, s h = ∑ x ∈ S_x_large, ∑ h ∈ S_h x, s h := by
    apply Finset.sum_subset
    · intro x hx
      simp only [S_g, mem_finite_substitution_support, S_x_large, mem_image, S_total] at hx ⊢
      obtain ⟨g, hg_mem, hg_nz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx.2
      rw [mem_finite_substitution_support] at hg_mem
      refine ⟨g, ⟨?_, hg_nz⟩, hg_mem.1⟩
      rw [pushExponent_comp, hg_mem.1, hx.1]
    · intro x hx hnx
      rw [hS_g, mem_finite_substitution_support] at hnx
      obtain ⟨h, hh_mem, hh_push⟩ := mem_image.1 hx
      simp only [S_total, mem_finite_substitution_support] at hh_mem
      have h_push_g : pushExponents g x = d'' := by
        rw [← hh_push, ← pushExponent_comp, hh_mem.1]
      have : (substitute f s) x = 0 := by
        contrapose! hnx
        exact ⟨h_push_g, hnx⟩
      simpa [substitute, substituteFun, hS_h] using this
  rw [hS_total] at h1
  rw [hS_g] at h2
  simp_rw [hS_h] at h2
  convert h1.trans h2.symm
  simp [pushExponent_comp]

end Basic

section Ring

variable {A : Type*} [CommRing A]

lemma substitute_one (f : ι → ι') :
    substitute f (1 : NovikovSeries Γ ι A) = (1 : NovikovSeries Γ ι' A) := by
  ext d'
  simp only [substitute, substituteFun, ne_eq]
  have h (g : ι → Γ) : (1 : NovikovSeries Γ ι A) g = if g = 0 then 1 else 0 := novikovOne_val g
  have h' (g : ι' → Γ) : (1 : NovikovSeries Γ ι' A) g = if g = 0 then 1 else 0 := novikovOne_val g
  simp_rw [h, h']
  have h_p0 : pushExponents f (0 : ι → Γ) = 0 := by funext j; simp [pushExponents]
  by_cases hd' : d' = 0
  · subst hd'
    rw [sum_eq_single 0]
    · simp
    · intro g hg hg0
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg
      split_ifs at hg with h_1
      · exact (hg0 h_1).elim
      · exact (hg.2 rfl).elim
    · intro h0
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, h_p0] at h0
      by_cases h1 : (1 : A) = 0
      · simp_all only [ite_self, ↓reduceIte, not_true_eq_false, and_false, not_false_eq_true]
      · simp [h1] at h0
  · simp only [hd', ite_false]
    apply sum_eq_zero
    intro g hg
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg
    have hg0 : g = 0 := by
      split_ifs at hg with h_1
      · exact h_1
      · exact (hg.2 rfl).elim
    subst hg0
    simp [h_p0] at hg
    simp_all only [not_true_eq_false]

lemma substitute_add (f : ι → ι') (s1 s2 : NovikovSeries Γ ι A) :
    substitute f (s1 + s2) = substitute f s1 + substitute f s2 := by
  ext g'
  simp only [substitute, substituteFun, AddSubgroup.coe_add, Pi.add_apply, Subtype.coe_mk]
  let S1 := (finite_substitution_support f s1 g').toFinset
  let S2 := (finite_substitution_support f s2 g').toFinset
  let S12 := (finite_substitution_support f (s1 + s2) g').toFinset
  have h_push : ∀ x ∈ S1 ∪ S2, pushExponents f x = g' := by
    intro x hx
    simp only [S1, S2, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    rcases hx with h | h <;> exact h.1
  have eq12 : ∑ g ∈ S12, (s1.val g + s2.val g) = ∑ g ∈ S1 ∪ S2, (s1.val g + s2.val g) := by
    apply Finset.sum_subset
    · intro x hx
      simp only [S12, S1, S2, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
      simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      by_cases hs1 : s1.val x = 0
      · right; refine ⟨hx.1, ?_⟩; by_contra h; apply hx.2; simp [hs1, h]
      · left; exact ⟨hx.1, hs1⟩
    · intro x hx hnx
      simp only [S12, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hnx
      by_contra h_nz
      exact hnx ⟨h_push x hx, h_nz⟩
  have eq1 : ∑ g ∈ S1, s1.val g = ∑ g ∈ S1 ∪ S2, s1.val g := by
    apply Finset.sum_subset Finset.subset_union_left
    intro x hx hnx
    simp only [S1, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hnx
    by_contra h_nz
    exact hnx ⟨h_push x hx, h_nz⟩
  have eq2 : ∑ g ∈ S2, s2.val g = ∑ g ∈ S1 ∪ S2, s2.val g := by
    apply Finset.sum_subset Finset.subset_union_right
    intro x hx hnx
    simp only [S2, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hnx
    by_contra h_nz
    exact hnx ⟨h_push x hx, h_nz⟩
  rw [eq12, eq1, eq2, ← Finset.sum_add_distrib]

omit [Fintype ι'] in lemma pushExponents_add (f : ι → ι') (g1 g2 : ι → Γ) :
    pushExponents f (g1 + g2) = pushExponents f g1 + pushExponents f g2 := by
  funext j
  simp [pushExponents, Pi.add_apply, sum_add_distrib]

lemma finite_substitute_mul_support (f : ι → ι') (s1 s2 : NovikovSeries Γ ι A) (g' : ι' → Γ) :
    {p : (ι → Γ) × (ι → Γ) | pushExponents f (p.1 + p.2) = g' ∧ s1 p.1 ≠ 0 ∧ s2 p.2 ≠ 0}.Finite := by
  let w : ι → ℝ := fun _ => 1
  have hw : ∀ i, 0 < w i := fun _ => zero_lt_one
  let T : ℝ := ∑ j, (g' j : ℝ)
  let Sf : Set (ι → Γ) := {g | s1 g ≠ 0 ∧ ∑ i, w i * (g i : ℝ) < T + 1}
  let Sg : Set (ι → Γ) := {g | s2 g ≠ 0 ∧ ∑ i, w i * (g i : ℝ) < 0}
  have hSf : Sf.Finite := s1.prop w hw _
  have hSg : Sg.Finite := s2.prop w hw _
  let P1 : Set ((ι → Γ) × (ι → Γ)) := ⋃ g1 ∈ Sf, (fun g2 => (g1, g2)) ''
    {g2 : ι → Γ | s2 g2 ≠ 0 ∧ ∑ i, w i * (g2 i : ℝ) < T + 1 - ∑ i, w i * (g1 i : ℝ)}
  let P2 : Set ((ι → Γ) × (ι → Γ)) := ⋃ g2 ∈ Sg, (fun g1 => (g1, g2)) ''
    {g1 : ι → Γ | s1 g1 ≠ 0 ∧ ∑ i, w i * (g1 i : ℝ) < T + 1 - ∑ i, w i * (g2 i : ℝ)}
  have hP1 : P1.Finite := by
    apply Set.Finite.biUnion hSf
    intro g1 _
    exact Set.Finite.image _ (s2.prop w hw _)
  have hP2 : P2.Finite := by
    apply Set.Finite.biUnion hSg
    intro g2 _
    exact Set.Finite.image _ (s1.prop w hw _)
  apply Set.Finite.subset (Set.Finite.union hP1 hP2)
  rintro ⟨g1, g2⟩ ⟨h_push, h1, h2⟩
  have h_sum_total : ∑ i, ((g1 + g2) i : ℝ) = T := by
    classical
    rw [← sum_fiberwise univ f (fun i => ((g1 + g2) i : ℝ))]
    apply sum_congr rfl
    intro j _
    simpa [pushExponents, AddSubmonoidClass.coe_finsetSum] using
      congrArg (fun f : ι' → Γ => (f j : ℝ)) h_push
  have h_split : ∑ i, w i * (g1 i : ℝ) + ∑ i, w i * (g2 i : ℝ) = T := by
    simp only [w, one_mul]
    rw [← Finset.sum_add_distrib]
    rw [show (∑ i, ((g1 i : ℝ) + (g2 i : ℝ))) = ∑ i, ((g1 + g2) i : ℝ) from
      sum_congr rfl (fun i _ => by simp [Pi.add_apply])]
    exact h_sum_total
  by_cases hcase : ∑ i, w i * (g1 i : ℝ) < T + 1
  · left
    simp only [P1, Set.mem_iUnion]
    refine ⟨g1, ⟨h1, hcase⟩, g2, ⟨h2, ?_⟩, rfl⟩
    linarith
  · right
    push Not at hcase
    have hg2_neg : ∑ i, w i * (g2 i : ℝ) < 0 := by linarith
    simp only [P2, Set.mem_iUnion]
    refine ⟨g2, ⟨h2, hg2_neg⟩, g1, ⟨h1, ?_⟩, rfl⟩
    linarith

lemma substitute_mul_LHS (f : ι → ι') (s1 s2 : NovikovSeries Γ ι A) (g' : ι' → Γ) :
    substitute f (s1 * s2) g' = ∑ p ∈ (finite_substitute_mul_support f s1 s2 g').toFinset, s1 p.1 * s2 p.2 := by
  let F := (finite_substitute_mul_support f s1 s2 g').toFinset
  have hF_mem : ∀ {p : (ι → Γ) × (ι → Γ)}, p ∈ F ↔
      pushExponents f (p.1 + p.2) = g' ∧ s1 p.1 ≠ 0 ∧ s2 p.2 ≠ 0 := fun {p} => by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  unfold substitute substituteFun
  let S := (finite_substitution_support f (s1 * s2) g').toFinset
  let G := F.image (fun p => p.1 + p.2)
  have h_subset : S ⊆ G := by
    intro g hg
    rw [mem_finite_substitution_support] at hg
    obtain ⟨p, hp, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg.2
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
    simp only [G, Finset.mem_image]
    refine ⟨p, ?_, hp.1⟩
    rw [hF_mem]
    exact ⟨by rw [hp.1, hg.1], hp.2.1, hp.2.2⟩
  change ∑ g ∈ S, (s1 * s2) g = _
  rw [Finset.sum_subset h_subset]
  swap
  · intro g hg_in hg_not
    rw [mem_finite_substitution_support] at hg_not
    push Not at hg_not
    have h_push : pushExponents f g = g' := by
      simp only [G, Finset.mem_image] at hg_in
      rcases hg_in with ⟨p, hp, rfl⟩
      exact (hF_mem.1 hp).1
    exact hg_not h_push
  simp only [novikovMul_val, novikovMulFun]
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun σ _ => σ.2)
  · rintro ⟨g, p⟩ hσ
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hσ
    rw [hF_mem]
    have h_push : pushExponents f g = g' := by
      simp only [G, Finset.mem_image] at hσ
      rcases hσ.1 with ⟨p', hp', rfl⟩
      exact (hF_mem.1 hp').1
    exact ⟨by rw [hσ.2.1, h_push], hσ.2.2.1, hσ.2.2.2⟩
  · rintro ⟨g, p⟩ hσ ⟨g', p'⟩ hτ (h_eq : p = p')
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hσ hτ
    rcases hσ with ⟨_, hσ_p⟩; rcases hτ with ⟨_, hτ_p⟩
    subst h_eq
    have : g = g' := by rw [← hσ_p.1, ← hτ_p.1]
    subst this; rfl
  · rintro p hp
    have hp' := hF_mem.1 hp
    refine ⟨⟨p.1 + p.2, p⟩, ?_, rfl⟩
    · simp only [Finset.mem_sigma, G, Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨⟨p, hp, rfl⟩, trivial, hp'.2.1, hp'.2.2⟩
  · rintro ⟨g, p⟩ _; rfl

lemma substitute_mul_RHS (f : ι → ι') (s1 s2 : NovikovSeries Γ ι A) (g' : ι' → Γ) :
    (substitute f s1 * substitute f s2) g' = ∑ p ∈ (finite_substitute_mul_support f s1 s2 g').toFinset, s1 p.1 * s2 p.2 := by
  let F := (finite_substitute_mul_support f s1 s2 g').toFinset
  have hF_mem : ∀ {p : (ι → Γ) × (ι → Γ)}, p ∈ F ↔
      pushExponents f (p.1 + p.2) = g' ∧ s1 p.1 ≠ 0 ∧ s2 p.2 ≠ 0 := fun {p} => by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  simp only [novikovMul_val, novikovMulFun, substitute, substituteFun]
  simp_rw [sum_mul, mul_sum]
  let S_conv := (finite_pair_sum_eq (T1 := fnSupport (substitute f s1).val) (T2 := fnSupport (substitute f s2).val) (substitute f s1).prop (substitute f s2).prop g').toFinset
  let G1 := F.image (fun p => pushExponents f p.1)
  let G2 := F.image (fun p => pushExponents f p.2)
  let BigG := S_conv ∪ ((G1 ×ˢ G2).filter (fun p => p.1 + p.2 = g'))
  let inner_sum (q : (ι' → Γ) × (ι' → Γ)) :=
    ∑ g1 ∈ (finite_substitution_support f s1 q.1).toFinset,
    ∑ g2 ∈ (finite_substitution_support f s2 q.2).toFinset, s1 g1 * s2 g2
  have h_outer_extend : ∑ q ∈ S_conv, inner_sum q = ∑ q ∈ BigG, inner_sum q := by
    apply Finset.sum_subset Finset.subset_union_left
    intro q hq_in hq_out
    have hq_in' := hq_in
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, S_conv, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq_in'
    have hq_push : q.1 + q.2 = g' := by
      rcases hq_in' with h|h
      · exact h.1
      · exact h.2
    by_cases h1 : (∑ g ∈ (finite_substitution_support f s1 q.1).toFinset, s1 g) = 0
    · change inner_sum q = 0
      simp_rw [inner_sum, ← Finset.mul_sum, ← Finset.sum_mul, h1, zero_mul]
    · have h2 : (∑ g ∈ (finite_substitution_support f s2 q.2).toFinset, s2 g) = 0 := by
        contrapose! hq_out
        simp only [S_conv, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        exact ⟨hq_push, h1, hq_out⟩
      change inner_sum q = 0
      simp_rw [inner_sum, ← Finset.mul_sum, ← Finset.sum_mul, h2, mul_zero]
  change ∑ q ∈ S_conv, inner_sum q = _
  rw [h_outer_extend, Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun σ _ => (σ.1.2, σ.2))
  · rintro ⟨⟨q, g1⟩, g2⟩ hσ
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hσ
    rw [hF_mem]
    refine ⟨?_, hσ.1.2.2, hσ.2.2⟩
    rw [pushExponents_add, hσ.1.2.1, hσ.2.1]
    simp only [BigG, Finset.mem_union, Finset.mem_filter, Finset.mem_product] at hσ
    rcases hσ.1.1 with h|h
    · simp only [S_conv, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h; exact h.1
    · exact h.2
  · rintro ⟨⟨q, g1⟩, g2⟩ hσ ⟨⟨q', g1'⟩, g2'⟩ hτ (h_eq : (g1, g2) = (g1', g2'))
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hσ hτ
    rcases h_eq with ⟨rfl, rfl⟩
    have hq1 : q.1 = q'.1 := by rw [← hσ.1.2.1, ← hτ.1.2.1]
    have hq2 : q.2 = q'.2 := by rw [← hσ.2.1, ← hτ.2.1]
    have : q = q' := Prod.ext hq1 hq2
    subst this
    rfl
  · rintro p hp
    have hp' := hF_mem.1 hp
    refine ⟨⟨⟨(pushExponents f p.1, pushExponents f p.2), p.1⟩, p.2⟩, ?_, rfl⟩
    · simp only [Finset.mem_sigma, BigG, Finset.mem_union, Finset.mem_filter, Finset.mem_product, G1, G2, Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨⟨Or.inr ⟨⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩, by rw [← pushExponents_add, hp'.1]⟩, trivial, hp'.2.1⟩, trivial, hp'.2.2⟩
  · rintro ⟨⟨q, g1⟩, g2⟩ _; rfl

lemma substitute_mul (f : ι → ι') (s1 s2 : NovikovSeries Γ ι A) :
    substitute f (s1 * s2) = substitute f s1 * substitute f s2 := by
  ext g'
  rw [substitute_mul_LHS, substitute_mul_RHS]

lemma substitute_zero (f : ι → ι') :
    substitute f (0 : NovikovSeries Γ ι A) = 0 := by
  ext d'
  simp only [substitute, substituteFun, AddSubgroup.coe_zero, Pi.zero_apply]
  apply sum_eq_zero
  intro g hg
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq,
    not_true_eq_false, and_false] at hg

lemma substitute_algebraMap (f : ι → ι') (a : A) :
    substitute f (algebraMapNovikov a : NovikovSeries Γ ι A) =
      (algebraMapNovikov a : NovikovSeries Γ ι' A) := by
  have h_push0 : pushExponents f (0 : ι → Γ) = 0 := by
    ext j; simp [pushExponents]
  ext d'
  simp only [substitute, substituteFun, algebraMapNovikov, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk]
  by_cases hd' : d' = 0
  · subst hd'
    rw [Finset.sum_eq_single 0]
    · simp
    · intro g hg hg0
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg
      have : g ≠ 0 := hg0
      simp [this]
    · intro h0
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_and] at h0
      simp only [ite_true]
      exact not_not.mp (h0 h_push0)
  · simp only [hd', ↓reduceIte]
    apply Finset.sum_eq_zero
    intro g hg
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg
    have hg0 : g ≠ 0 := by
      intro hg0; exact hd' (by rw [← hg.1, hg0, h_push0])
    simp [hg0]

/-- Substitution is a ring homomorphism. -/
noncomputable def substituteRingHom (f : ι → ι') :
    NovikovSeries Γ ι A →+* NovikovSeries Γ ι' A where
  toFun := substitute f
  map_one' := substitute_one f
  map_mul' := substitute_mul f
  map_zero' := substitute_zero f
  map_add' := substitute_add f

/-- Substitution as an algebra homomorphism. -/
noncomputable def substituteAlgHom (f : ι → ι') :
    NovikovSeries Γ ι A →ₐ[A] NovikovSeries Γ ι' A :=
  AlgHom.mk' (substituteRingHom f) (fun a x => by
    change substitute f (a • x) = a • substitute f x
    have h1 : a • x = algebraMapNovikov a * x := by
      rw [Algebra.smul_def]; rfl
    have h2 : a • substitute f x = algebraMapNovikov a * substitute f x := by
      rw [Algebra.smul_def]; rfl
    rw [h1, h2]
    change (substituteRingHom f) (algebraMapNovikov a * x) = _
    rw [(substituteRingHom f).map_mul]
    congr 1
    exact substitute_algebraMap f a)

end Ring

end Novikov
