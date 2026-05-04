
import Novikov.Series.Basic
import Novikov.Series.Finite
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
    have h_push := congr_fun hg.1 j
    simp only [pushExponents] at h_push
    rw [← h_push]
    simp only [AddSubmonoidClass.coe_finset_sum]
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
lemma isNovikov_substituteFun (f : ι → ι') (s : NovikovSeries Γ ι A) :
    isNovikovSeries (substituteFun f s) := by
  intro w' hw' C
  let w : ι → ℝ := fun i => w' (f i)
  have hw : ∀ i, 0 < w i := fun i => hw' (f i)
  let S := {g | s g ≠ 0 ∧ ∑ i, w i * (g i : ℝ) < C}
  have hS : S.Finite := s.prop w hw C
  let target := {g' | substituteFun f s g' ≠ 0 ∧ ∑ j, w' j * (g' j : ℝ) < C}
  have h_sub : target ⊆ pushExponents f '' S := by
    intro g' hg'
    have h_nz : ∃ g, pushExponents f g = g' ∧ s g ≠ 0 := by
      by_contra h_none
      simp only [not_exists, not_and, ne_eq, not_not] at h_none
      have : substituteFun f s g' = 0 := by
        unfold substituteFun
        apply sum_eq_zero
        intro g hg
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg
        exact h_none g hg.1
      exact hg'.1 this
    rcases h_nz with ⟨g, h_push, h_snz⟩
    refine ⟨g, ⟨h_snz, ?_⟩, h_push⟩
    have h_eq : ∑ i, w i * (g i : ℝ) = ∑ j, w' j * (g' j : ℝ) := by
      rw [← h_push]
      simp only [pushExponents, w]
      classical
      rw [← sum_fiberwise univ f (fun i => w' (f i) * (g i : ℝ))]
      apply sum_congr rfl
      intro j _
      rw [AddSubmonoidClass.coe_finset_sum, mul_sum]
      apply sum_congr rfl
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      rw [hi]
    rw [h_eq]
    exact hg'.2
  exact hS.image (pushExponents f) |>.subset h_sub

/-- The map on Novikov series induced by a map of variable sets. -/
noncomputable def substitute (f : ι → ι') (s : NovikovSeries Γ ι A) : NovikovSeries Γ ι' A :=
  ⟨substituteFun f s, isNovikov_substituteFun f s⟩

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

lemma pushExponent_comp {ι'' : Type*} (f : ι → ι') (g : ι' → ι'') (d : ι → Γ) : pushExponents (g ∘ f) d = pushExponents g (pushExponents f d) := by
  funext k
  simp only [pushExponents]
  symm
  classical
  apply (Finset.sum_sigma (univ.filter (fun j => g j = k)) (fun j => univ.filter (fun i => f i = j)) (fun p => d p.2)).symm.trans
  apply sum_bij (fun p _ => p.2)
  · rintro ⟨j, i⟩ h_sig
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at h_sig
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply]
    rw [← h_sig.1, h_sig.2]
  · rintro ⟨j, i⟩ h_sig
    intro a₂ ha₂ a
    subst a
    simp_all only [mem_sigma, mem_filter, mem_univ, true_and]
    obtain ⟨fst, snd⟩ := a₂
    obtain ⟨left, right⟩ := h_sig
    subst left right
    simp_all only
  · intro b a
    simp_all only [Function.comp_apply, mem_filter, mem_univ, true_and, mem_sigma, exists_prop, Sigma.exists,
    exists_eq_right, exists_eq_right']
  · intro i hT
    simp_all only [mem_sigma, mem_filter, mem_univ, true_and]

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
      simp only [S_g] at hx
      simp only [S_x_large, mem_image, S_total]
      have ⟨h, hfh, hsnz⟩ : ∃ h, pushExponents f h = x ∧ s h ≠ 0 := by
        contrapose! hx
        simp only [ne_eq, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_and, Decidable.not_not]
        intro hd
        unfold substitute substituteFun
        subst hd
        simp_all only [ne_eq, S_h, S_total, S_g, S_x_large]
        obtain ⟨val, property⟩ := s
        simp_all only
        apply Finset.sum_eq_zero
        intro x_1 a
        simp_all only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] 
      subst hfh
      simp_all only [ne_eq, Set.Finite.mem_toFinset, Set.mem_setOf_eq, S_total, S_h, S_g, S_x_large]
      obtain ⟨val, property⟩ := s
      obtain ⟨left, right⟩ := hx
      subst left
      simp_all only
      apply Exists.intro
      · apply And.intro
        on_goal 2 => { rfl
        }
        · simp_all only [not_false_eq_true, and_true]
          apply Novikov.pushExponent_comp
    · intro x hx h_nz
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, S_g] at h_nz
      contrapose! h_nz
      constructor
      · simp only [S_x_large, Finset.mem_image, S_total, Set.Finite.mem_toFinset,
          Set.mem_setOf_eq] at hx
        obtain ⟨h, ⟨hgf, _⟩, hfh⟩ := hx
        rw [← hfh, ← pushExponent_comp, hgf]
      · exact h_nz
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
  let F := S1 ∪ S2 ∪ S12
  have h_push : ∀ g ∈ F, pushExponents f g = g' := by
    intro g hg
    simp only [F, mem_union] at hg
    rcases hg with (hg | hg) | hg
    · simp only [S1, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg; exact hg.1
    · simp only [S2, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg; exact hg.1
    · simp only [S12, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg; exact hg.1
  have h_in1 : S1 ⊆ F := by intro g hg; simp only [F, mem_union, hg, true_or]
  have h_in2 : S2 ⊆ F := by intro g hg; simp only [F, mem_union, hg, true_or, or_true]
  have h_in12 : S12 ⊆ F := by intro g hg; simp only [F, mem_union, hg, or_true]
  rw [Finset.sum_subset h_in12, Finset.sum_subset h_in1, Finset.sum_subset h_in2]
  · rw [Finset.sum_add_distrib]
  · intro g hg_in hg_out
    simp only [S2, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg_out
    have : pushExponents f g = g' := h_push g hg_in
    simp only [this, true_and, ne_eq, not_not] at hg_out
    exact hg_out
  · intro g hg_in hg_out
    simp_all [F, S1, S2, S12]
  · intro g hg_in hg_out
    simp only [S12, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg_out
    have : pushExponents f g = g' := h_push g hg_in
    simp only [this, true_and, ne_eq, not_not] at hg_out
    exact hg_out

omit [Fintype ι'] in lemma pushExponents_add (f : ι → ι') (g1 g2 : ι → Γ) :
    pushExponents f (g1 + g2) = pushExponents f g1 + pushExponents f g2 := by
  funext j
  simp [pushExponents, Pi.add_apply, sum_add_distrib]

lemma substitute_mul (f : ι → ι') (s1 s2 : NovikovSeries Γ ι A) :
    substitute f (s1 * s2) = substitute f s1 * substitute f s2 := by
  ext g'
  let BigSupport := {p : (ι → Γ) × (ι → Γ) | pushExponents f (p.1 + p.2) = g' ∧ s1 p.1 ≠ 0 ∧ s2 p.2 ≠ 0}
  have h_finite : BigSupport.Finite := by
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
      have h_push_fun := congr_fun h_push j
      simp only [pushExponents] at h_push_fun
      rw [← h_push_fun, AddSubmonoidClass.coe_finset_sum]
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
  let F := h_finite.toFinset
  -- Auxiliary: bijection from F to a sigma over F.image(·.1+·.2) and conv_supp.
  let G_large := F.image (fun p => p.1 + p.2)
  have hF_mem : ∀ {p : (ι → Γ) × (ι → Γ)}, p ∈ F ↔
      pushExponents f (p.1 + p.2) = g' ∧ s1 p.1 ≠ 0 ∧ s2 p.2 ≠ 0 := by
    intro p
    simp only [F, Set.Finite.mem_toFinset, BigSupport, Set.mem_setOf_eq]
  have h_LHS : substitute f (s1 * s2) g' = ∑ p ∈ F, s1 p.1 * s2 p.2 := by
    have hLHS_unfold : substitute f (s1 * s2) g'
        = ∑ g ∈ (finite_substitution_support f (s1 * s2) g').toFinset,
          ∑ p ∈ (finite_convolution_support s1 s2 g).toFinset, s1 p.1 * s2 p.2 := rfl
    rw [hLHS_unfold]
    have h_sub : (finite_substitution_support f (s1 * s2) g').toFinset ⊆ G_large := by
      intro g hg
      rw [mem_finite_substitution_support] at hg
      obtain ⟨hg_push, hne⟩ := hg
      have hex : ∃ p : (ι → Γ) × (ι → Γ), p.1 + p.2 = g ∧ s1 p.1 ≠ 0 ∧ s2 p.2 ≠ 0 := by
        by_contra h_none
        push Not at h_none
        apply hne
        change ∑ p ∈ (finite_convolution_support s1 s2 g).toFinset, s1 p.1 * s2 p.2 = 0
        apply Finset.sum_eq_zero
        intro p hp_conv
        rw [mem_finite_convolution_support] at hp_conv
        have h2 : s2 p.2 = 0 := h_none p hp_conv.1 hp_conv.2.1
        rw [h2, mul_zero]
      obtain ⟨p, hp_sum, hp1, hp2⟩ := hex
      simp only [G_large, Finset.mem_image]
      exact ⟨p, hF_mem.mpr ⟨by rw [hp_sum]; exact hg_push, hp1, hp2⟩, hp_sum⟩
    have h_extend : ∑ g ∈ (finite_substitution_support f (s1 * s2) g').toFinset,
          ∑ p ∈ (finite_convolution_support s1 s2 g).toFinset, s1 p.1 * s2 p.2
        = ∑ g ∈ G_large,
          ∑ p ∈ (finite_convolution_support s1 s2 g).toFinset, s1 p.1 * s2 p.2 := by
      apply Finset.sum_subset h_sub
      intro g hg_in hg_out
      rw [mem_finite_substitution_support] at hg_out
      push Not at hg_out
      have hpush : pushExponents f g = g' := by
        simp only [G_large, Finset.mem_image] at hg_in
        obtain ⟨p, hp, hpg⟩ := hg_in
        rw [← hpg]; exact (hF_mem.mp hp).1
      have h0 : (s1 * s2) g = 0 := hg_out hpush
      exact h0
    rw [h_extend]
    rw [Finset.sum_sigma']
    apply Finset.sum_bij (fun σ _ => σ.2)
    -- hi: σ.2 ∈ F
    · rintro ⟨g, p⟩ hσ
      simp only [Finset.mem_sigma] at hσ
      obtain ⟨hg_in, hp_conv⟩ := hσ
      rw [mem_finite_convolution_support] at hp_conv
      simp only [G_large, Finset.mem_image] at hg_in
      obtain ⟨q, hq_F, hq_eq⟩ := hg_in
      have hq_push := (hF_mem.mp hq_F).1
      rw [hF_mem]
      refine ⟨?_, hp_conv.2.1, hp_conv.2.2⟩
      rw [hp_conv.1, ← hq_eq]; exact hq_push
    -- i_inj
    · rintro ⟨g, p⟩ hσ ⟨g', p'⟩ hτ h_eq
      simp only [Finset.mem_sigma] at hσ hτ
      rw [mem_finite_convolution_support] at hσ hτ
      simp only at h_eq
      have hgg : g = g' := by rw [← hσ.2.1, ← hτ.2.1, h_eq]
      subst hgg
      subst h_eq
      rfl
    -- i_surj
    · rintro p hp
      refine ⟨⟨p.1 + p.2, p⟩, ?_, rfl⟩
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · simp only [G_large, Finset.mem_image]; exact ⟨p, hp, rfl⟩
      · rw [mem_finite_convolution_support]
        exact ⟨rfl, (hF_mem.mp hp).2.1, (hF_mem.mp hp).2.2⟩
    -- h: function value
    · rintro ⟨g, p⟩ _; rfl
  have h_RHS : (substitute f s1 * substitute f s2) g' = ∑ p ∈ F, s1 p.1 * s2 p.2 := by
    have hRHS_unfold : (substitute f s1 * substitute f s2) g'
        = ∑ q ∈ (finite_convolution_support (substitute f s1) (substitute f s2) g').toFinset,
          (substitute f s1) q.1 * (substitute f s2) q.2 := rfl
    rw [hRHS_unfold]
    -- Each substitute s_i q_i = ∑ over fiber.
    have h_unfold_q1 (q1 : ι' → Γ) :
        (substitute f s1) q1 = ∑ g ∈ (finite_substitution_support f s1 q1).toFinset, s1 g := rfl
    have h_unfold_q2 (q2 : ι' → Γ) :
        (substitute f s2) q2 = ∑ g ∈ (finite_substitution_support f s2 q2).toFinset, s2 g := rfl
    simp_rw [h_unfold_q1, h_unfold_q2, Finset.sum_mul, Finset.mul_sum]
    -- BigG = S_conv ∪ extras to capture all push-pairs
    let G1 := F.image (fun p => pushExponents f p.1)
    let G2 := F.image (fun p => pushExponents f p.2)
    let S_conv := (finite_convolution_support (substitute f s1) (substitute f s2) g').toFinset
    let BigG := S_conv ∪ ((G1 ×ˢ G2).filter (fun p => p.1 + p.2 = g'))
    have h_sub_conv : S_conv ⊆ BigG := Finset.subset_union_left
    have h_outer_extend : ∑ q ∈ S_conv,
          ∑ g1 ∈ (finite_substitution_support f s1 q.1).toFinset,
            ∑ g2 ∈ (finite_substitution_support f s2 q.2).toFinset, s1 g1 * s2 g2
        = ∑ q ∈ BigG,
          ∑ g1 ∈ (finite_substitution_support f s1 q.1).toFinset,
            ∑ g2 ∈ (finite_substitution_support f s2 q.2).toFinset, s1 g1 * s2 g2 := by
      apply Finset.sum_subset h_sub_conv
      intro q hq_in hq_out
      simp only [S_conv, mem_finite_convolution_support, not_and, not_not] at hq_out
      simp only [BigG, Finset.mem_union, Finset.mem_filter, Finset.mem_product, S_conv,
        mem_finite_convolution_support] at hq_in
      have hq_push : q.1 + q.2 = g' := by
        rcases hq_in with hq_in | hq_in
        · exact hq_in.1
        · exact hq_in.2
      have h_zero : (substitute f s1) q.1 * (substitute f s2) q.2 = 0 := by
        by_cases h1 : (substitute f s1) q.1 = 0
        · rw [h1, zero_mul]
        · rw [hq_out hq_push h1, mul_zero]
      rw [h_unfold_q1, h_unfold_q2, Finset.sum_mul] at h_zero
      simp_rw [Finset.mul_sum] at h_zero
      exact h_zero
    apply h_outer_extend.trans
    -- Now bijection: BigG sigma sigma → F.
    rw [Finset.sum_sigma', Finset.sum_sigma']
    apply Finset.sum_bij (fun σ (_ : σ ∈ _) => (σ.1.2, σ.2))
    -- hi
    · rintro ⟨⟨q, g1⟩, g2⟩ hσ
      simp only [Finset.mem_sigma] at hσ
      obtain ⟨⟨hq_in, hg1⟩, hg2⟩ := hσ
      rw [mem_finite_substitution_support] at hg1 hg2
      simp only [BigG, Finset.mem_union, Finset.mem_filter, Finset.mem_product, S_conv,
        mem_finite_convolution_support] at hq_in
      have hq_push : q.1 + q.2 = g' := by
        rcases hq_in with hq_in | hq_in
        · exact hq_in.1
        · exact hq_in.2
      rw [hF_mem]
      refine ⟨?_, hg1.2, hg2.2⟩
      rw [pushExponents_add, hg1.1, hg2.1, hq_push]
    -- i_inj
    · rintro ⟨⟨q, g1⟩, g2⟩ hσ ⟨⟨q', g1'⟩, g2'⟩ hτ h_eq
      simp only [Finset.mem_sigma] at hσ hτ
      obtain ⟨⟨_, hg1⟩, hg2⟩ := hσ
      obtain ⟨⟨_, hg1'⟩, hg2'⟩ := hτ
      rw [mem_finite_substitution_support] at hg1 hg2 hg1' hg2'
      simp only [Prod.mk.injEq] at h_eq
      obtain ⟨hgg1, hgg2⟩ := h_eq
      subst hgg1 hgg2
      have hq1 : q.1 = q'.1 := by rw [← hg1.1, ← hg1'.1]
      have hq2 : q.2 = q'.2 := by rw [← hg2.1, ← hg2'.1]
      have hqq : q = q' := Prod.ext hq1 hq2
      subst hqq
      rfl
    -- i_surj
    · rintro p hp
      have hp' := hF_mem.mp hp
      refine ⟨⟨⟨(pushExponents f p.1, pushExponents f p.2), p.1⟩, p.2⟩, ?_, ?_⟩
      · refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
        · refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
          · simp only [BigG, Finset.mem_union, Finset.mem_filter, Finset.mem_product, S_conv,
              mem_finite_convolution_support, G1, G2, Finset.mem_image]
            right
            refine ⟨⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩, ?_⟩
            rw [← pushExponents_add]; exact hp'.1
          · rw [mem_finite_substitution_support]; exact ⟨rfl, hp'.2.1⟩
        · rw [mem_finite_substitution_support]; exact ⟨rfl, hp'.2.2⟩
      · rfl
    -- h
    · rintro ⟨⟨q, g1⟩, g2⟩ _; rfl
  rw [h_LHS, h_RHS]



lemma substitute_zero (f : ι → ι') :
    substitute f (0 : NovikovSeries Γ ι A) = 0 := by
  ext d'
  simp only [substitute, substituteFun, AddSubgroup.coe_zero, Pi.zero_apply]
  apply sum_eq_zero
  intro g hg
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq,
    not_true_eq_false, and_false] at hg

/-- Substitution is a ring homomorphism. -/
noncomputable def substituteRingHom (f : ι → ι') :
    NovikovSeries Γ ι A →+* NovikovSeries Γ ι' A where
  toFun := substitute f
  map_one' := substitute_one f
  map_mul' := substitute_mul f
  map_zero' := substitute_zero f
  map_add' := substitute_add f

end Ring

end Novikov
