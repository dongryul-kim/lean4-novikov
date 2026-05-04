import Novikov.Series.Basic
import Novikov.Series.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace Novikov

variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S}
variable {ι : Type*} [Fintype ι]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

noncomputable def novikovSeriesMulFun
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B)
    (α : A →+ B →+ C) (d : ι → Γ) : C :=
  let S : Finset ((ι → Γ) × (ι → Γ)) := (finite_convolution_support f g d).toFinset
  Finset.sum S fun p : (ι → Γ) × (ι → Γ) => α (f p.1) (g p.2)

lemma novikovSeriesMul_largerSum
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B)
    (α : A →+ B →+ C) (d : ι → Γ) (S : Finset ((ι → Γ) × (ι → Γ)))
    (hs : (finite_convolution_support f g d).toFinset ⊆ S)
    (h_sum : ∀ p ∈ S, p.1 + p.2 = d) :
    novikovSeriesMulFun f g α d = 
    Finset.sum S fun p : (ι → Γ) × (ι → Γ) => α (f p.1) (g p.2) := by
  simp only [novikovSeriesMulFun]
  apply Finset.sum_subset hs
  intro p hp hnot
  rw [mem_finite_convolution_support] at hnot
  have h_eq := h_sum p hp
  simp only [h_eq, true_and] at hnot
  by_cases hf : f p.1 = 0
  · rw [hf, map_zero, AddMonoidHom.zero_apply]
  · have hg : g p.2 = 0 := by
      contrapose! hnot
      exact ⟨hf, hnot⟩
    rw [hg, map_zero]

lemma isNovikov_novikovSeriesMulFun
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B)
    (α : A →+ B →+ C) : isNovikovSeries (novikovSeriesMulFun f g α) := by
  intro s hs L
  let Sf := {d1 : ι → Γ | f d1 ≠ 0 ∧ ∑ i, s i * (d1 i : ℝ) < L + 1}
  let Sg := {d2 : ι → Γ | g d2 ≠ 0 ∧ ∑ i, s i * (d2 i : ℝ) < 0}
  have hf : Sf.Finite := f.prop s hs (L + 1)
  have hg : Sg.Finite := g.prop s hs 0
  let T1 := ⋃ d1 ∈ Sf, (fun d2 => d1 + d2) '' {d2 : ι → Γ | g d2 ≠ 0 ∧ ∑ i, s i * (d2 i : ℝ) < L - ∑ i, s i * (d1 i : ℝ)}
  let T2 := ⋃ d2 ∈ Sg, (fun d1 => d1 + d2) '' {d1 : ι → Γ | f d1 ≠ 0 ∧ ∑ i, s i * (d1 i : ℝ) < L - ∑ i, s i * (d2 i : ℝ)}
  have hT1 : T1.Finite := by
    have h' : ∀ d1 ∈ Sf, ((fun d2 => d1 + d2) '' {d2 : ι → Γ | g d2 ≠ 0 ∧ ∑ i, s i * (d2 i : ℝ) < L - ∑ i, s i * (d1 i : ℝ)}).Finite := by
      intro d1 _
      have hfin : {d2 : ι → Γ | g d2 ≠ 0 ∧ ∑ i, s i * (d2 i : ℝ) < L - ∑ i, s i * (d1 i : ℝ)}.Finite := g.prop s hs (L - ∑ i, s i * (d1 i : ℝ))
      exact Set.Finite.image (fun d2 => d1 + d2) hfin
    exact Set.Finite.biUnion hf h'
  have hT2 : T2.Finite := by
    have h' : ∀ d2 ∈ Sg, ((fun d1 => d1 + d2) '' {d1 : ι → Γ | f d1 ≠ 0 ∧ ∑ i, s i * (d1 i : ℝ) < L - ∑ i, s i * (d2 i : ℝ)}).Finite := by
      intro d2 _
      have hfin : {d1 : ι → Γ | f d1 ≠ 0 ∧ ∑ i, s i * (d1 i : ℝ) < L - ∑ i, s i * (d2 i : ℝ)}.Finite := f.prop s hs (L - ∑ i, s i * (d2 i : ℝ))
      exact Set.Finite.image (fun d1 => d1 + d2) hfin
    exact Set.Finite.biUnion hg h'
  have h_sub : {d : ι → Γ | novikovSeriesMulFun f g α d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < L} ⊆ T1 ∪ T2 := by
    intro d hd
    rcases hd with ⟨hne, hlt⟩
    have hsum_nz : ∃ p ∈ (finite_convolution_support f g d).toFinset, α (f p.1) (g p.2) ≠ 0 := by
      by_contra h
      push Not at h
      have : novikovSeriesMulFun f g α d = 0 := by
        simp only [novikovSeriesMulFun, ne_eq]
        apply Finset.sum_eq_zero
        intro p hp
        have h0 : α (f p.1) (g p.2) = 0 := by
          by_contra hne
          simp_all only [ne_eq, Set.mem_setOf_eq, Set.Finite.mem_toFinset, and_imp, Prod.forall, not_false_eq_true,
            not_true_eq_false, Sf, Sg, T1, T2]
        simp only [h0]
      contradiction
    rcases hsum_nz with ⟨⟨d1, d2⟩, hp, hprod⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
    obtain ⟨hsum, hf1, hg2⟩ := hp
    have hL : ∑ i, s i * (d i : ℝ) = ∑ i, s i * (d1 i : ℝ) + ∑ i, s i * (d2 i : ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have h_eq : (d i : ℝ) = (d1 i : ℝ) + (d2 i : ℝ) := by
        have h := congr_fun hsum i
        simp only [Pi.add_apply] at h
        rw [← h]
        rfl
      rw [h_eq]
      ring
    by_cases h : ∑ i, s i * (d1 i : ℝ) < L + 1
    · left
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, exists_prop, T1]
      exact ⟨d1, ⟨hf1, h⟩, d2, ⟨hg2, by linarith⟩, hsum⟩
    · right
      have hgd2 : ∑ i, s i * (d2 i : ℝ) < 0 := by linarith
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, exists_prop, T2]
      exact ⟨d2, ⟨hg2, hgd2⟩, d1, ⟨hf1, by linarith⟩, hsum⟩
  exact Set.Finite.subset (Set.Finite.union hT1 hT2) h_sub

noncomputable def novikovSeriesMul
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B)
    (α : A →+ B →+ C) : NovikovSeries Γ ι C :=
  ⟨novikovSeriesMulFun f g α, isNovikov_novikovSeriesMulFun f g α⟩

lemma novikovSeriesMul_zero_mul
    (f : NovikovSeries Γ ι B) (α : A →+ B →+ C) : novikovSeriesMul 0 f α = 0 := by
  refine Subtype.ext (funext (fun d => ?_))
  simp only [novikovSeriesMul, novikovSeriesMulFun, ZeroMemClass.coe_zero, Pi.zero_apply,
    ne_eq, not_true_eq_false, false_and, and_false, Set.setOf_false, Set.toFinite_toFinset, Set.toFinset_empty]
  simp_all only [Finset.sum_empty]

lemma novikovSeriesMul_mul_zero
    (f : NovikovSeries Γ ι A) (α : A →+ B →+ C) : novikovSeriesMul f 0 α = 0 := by
  refine Subtype.ext (funext (fun d => ?_))
  simp only [novikovSeriesMul, novikovSeriesMulFun, ne_eq, ZeroMemClass.coe_zero, Pi.zero_apply,
    not_true_eq_false, and_false, Set.setOf_false, Set.toFinite_toFinset, Set.toFinset_empty]
  simp_all only [Finset.sum_empty]

lemma novikovSeriesMul_left_distrib
    (f g : NovikovSeries Γ ι A) (h : NovikovSeries Γ ι B) (α : A →+ B →+ C) :
    novikovSeriesMul (f + g) h α = novikovSeriesMul f h α + novikovSeriesMul g h α := by
  refine Subtype.ext (funext (fun d => ?_))
  simp only [novikovSeriesMul, novikovSeriesMulFun, AddSubgroup.coe_add, Pi.add_apply, ne_eq]
  have hS : ∑ p ∈ (finite_convolution_support (f + g) h d).toFinset,
              α (f p.1 + g p.1) (h p.2) =
            ∑ p ∈ (finite_convolution_support f h d).toFinset ∪ (finite_convolution_support g h d).toFinset,
              α (f p.1 + g p.1) (h p.2) := by
    apply Finset.sum_subset
    · intro p hp
      rw [mem_finite_convolution_support] at hp
      apply Finset.mem_union.mpr
      have hdisj : f p.1 ≠ 0 ∨ g p.1 ≠ 0 := by
        by_contra h
        simp only [ne_eq, not_or, not_not] at h
        have : f p.1 + g p.1 = 0 := by simp only [h.1, h.2, add_zero]
        simp_all only [AddSubgroup.coe_add, Pi.add_apply, add_zero, ne_eq, not_true_eq_false, false_and, and_false]
      rcases hdisj with h | h
      · left; rw [mem_finite_convolution_support]; exact ⟨hp.1, h, hp.2.2⟩
      · right; rw [mem_finite_convolution_support]; exact ⟨hp.1, h, hp.2.2⟩
    · intro p hp hnot
      have h_term : α (f p.1 + g p.1) (h p.2) = 0 := by
        by_contra hne
        rw [Finset.mem_union] at hp
        rcases hp with hsf | hsg
        · rw [mem_finite_convolution_support] at hsf
          have h0 : f p.1 + g p.1 = 0 := by
            by_contra hne'
            rw [mem_finite_convolution_support] at hnot
            exact hnot ⟨hsf.1, hne', hsf.2.2⟩
          simp_all only [AddSubgroup.coe_add, Pi.add_apply, ne_eq, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
            not_true_eq_false, not_false_eq_true, and_true, and_false, map_zero, AddMonoidHom.zero_apply]
        · rw [mem_finite_convolution_support] at hsg
          have h0 : f p.1 + g p.1 = 0 := by
            by_contra hne'
            rw [mem_finite_convolution_support] at hnot
            exact hnot ⟨hsg.1, hne', hsg.2.2⟩
          simp_all only [AddSubgroup.coe_add, Pi.add_apply, ne_eq, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
            not_true_eq_false, not_false_eq_true, and_true, and_false, map_zero, AddMonoidHom.zero_apply]
      simp only [h_term]
  have hSf : ∑ p ∈ (finite_convolution_support f h d).toFinset, α (f p.1) (h p.2) =
             ∑ p ∈ (finite_convolution_support f h d).toFinset ∪ (finite_convolution_support g h d).toFinset,
               α (f p.1) (h p.2) := by
    apply Finset.sum_subset
    · intro p hp; apply Finset.mem_union.mpr; left; exact hp
    · intro p hp hnot
      have h_term : α (f p.1) (h p.2) = 0 := by
        by_contra hne
        rw [Finset.mem_union] at hp
        rcases hp with hsf | hsg
        · contradiction
        · rw [mem_finite_convolution_support] at hsg
          have h0 : f p.1 = 0 := by
            by_contra hne'
            rw [mem_finite_convolution_support] at hnot
            exact hnot ⟨hsg.1, hne', hsg.2.2⟩
          simp_all only [AddSubgroup.coe_add, Pi.add_apply, ne_eq, map_add, AddMonoidHom.add_apply,
            Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_true_eq_false, not_false_eq_true, and_true, and_false,
            map_zero, AddMonoidHom.zero_apply]
      simp only [h_term]
  have hSg : ∑ p ∈ (finite_convolution_support g h d).toFinset, α (g p.1) (h p.2) =
             ∑ p ∈ (finite_convolution_support f h d).toFinset ∪ (finite_convolution_support g h d).toFinset,
               α (g p.1) (h p.2) := by
    apply Finset.sum_subset
    · intro p hp; apply Finset.mem_union.mpr; right; exact hp
    · intro p hp hnot
      have h_term : α (g p.1) (h p.2) = 0 := by
        by_contra hne
        rw [Finset.mem_union] at hp
        rcases hp with hsf | hsg
        · rw [mem_finite_convolution_support] at hsf
          have h0 : g p.1 = 0 := by
            by_contra hne'
            rw [mem_finite_convolution_support] at hnot
            exact hnot ⟨hsf.1, hne', hsf.2.2⟩
          simp_all only [AddSubgroup.coe_add, Pi.add_apply, ne_eq, map_add, AddMonoidHom.add_apply,
            Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_true_eq_false, not_false_eq_true, and_true, and_false,
            map_zero, AddMonoidHom.zero_apply]
        · contradiction
      simp only [h_term]
  rw [hS, hSf, hSg, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp_all only [AddSubgroup.coe_add, Pi.add_apply, ne_eq, map_add, AddMonoidHom.add_apply, Finset.mem_union,
    Set.Finite.mem_toFinset, Set.mem_setOf_eq]

lemma novikovSeriesMul_right_distrib
    (f : NovikovSeries Γ ι A) (g h : NovikovSeries Γ ι B) (α : A →+ B →+ C) :
    novikovSeriesMul f (g + h) α = novikovSeriesMul f g α + novikovSeriesMul f h α := by
  refine Subtype.ext (funext (fun d => ?_))
  simp only [novikovSeriesMul, novikovSeriesMulFun, ne_eq, AddSubgroup.coe_add, Pi.add_apply]
  let Sg := (finite_convolution_support f g d).toFinset
  let Sh := (finite_convolution_support f h d).toFinset
  let T := Sg ∪ Sh
  have hS : ∑ p ∈ (finite_convolution_support f (g + h) d).toFinset,
              α (f p.1) (g p.2 + h p.2) =
            ∑ p ∈ T, α (f p.1) (g p.2 + h p.2) := by
    apply Finset.sum_subset
    · intro p hp
      rw [mem_finite_convolution_support] at hp
      apply Finset.mem_union.mpr
      have hdisj : g p.2 ≠ 0 ∨ h p.2 ≠ 0 := by
        by_contra h
        simp only [ne_eq, not_or, not_not] at h
        simp_all only [ne_eq, AddSubgroup.coe_add, Pi.add_apply, add_zero, not_true_eq_false, and_false]
      rcases hdisj with h | h
      · left
        rw [mem_finite_convolution_support]
        exact ⟨hp.1, hp.2.1, h⟩
      · right
        rw [mem_finite_convolution_support]
        exact ⟨hp.1, hp.2.1, h⟩
    · intro p hp hnot
      have h_term : α (f p.1) (g p.2 + h p.2) = 0 := by
        by_contra hne
        have hp' : p ∈ Sg ∨ p ∈ Sh := Finset.mem_union.mp hp
        rcases hp' with hsg | hsh
        · have hsg' : p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ g p.2 ≠ 0 := by
            rw [mem_finite_convolution_support] at hsg
            exact hsg
          have h0 : g p.2 + h p.2 = 0 := by
            by_contra hne'
            simp_all only [ne_eq, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_false_eq_true,
              and_self, true_and, true_or, AddSubgroup.coe_add, Pi.add_apply, not_true_eq_false, T, Sg, Sh]
          simp_all only [ne_eq, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_false_eq_true,
            true_and, true_or, AddSubgroup.coe_add, Pi.add_apply, not_true_eq_false, and_false, map_zero, T,
            Sg, Sh]
        · have hsh' : p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ h p.2 ≠ 0 := by
            rw [mem_finite_convolution_support] at hsh
            exact hsh
          have h0 : g p.2 + h p.2 = 0 := by
            by_contra hne'
            simp_all only [ne_eq, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_false_eq_true,
              true_and, and_self, or_true, AddSubgroup.coe_add, Pi.add_apply, not_true_eq_false, T, Sg, Sh]
          simp_all only [ne_eq, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_false_eq_true,
            true_and, or_true, AddSubgroup.coe_add, Pi.add_apply, not_true_eq_false, and_false, T, Sg, Sh]
          simp_all only [map_zero, not_true_eq_false]
      simp only [h_term]
  have hSg : ∑ p ∈ Sg, α (f p.1) (g p.2) =
             ∑ p ∈ T, α (f p.1) (g p.2) := by
    apply Finset.sum_subset
    · intro p hp; apply Finset.mem_union.mpr; left; exact hp
    · intro p hp hnot
      have h_term : α (f p.1) (g p.2) = 0 := by
        by_contra hne
        have hp' : p ∈ Sg ∨ p ∈ Sh := Finset.mem_union.mp hp
        rcases hp' with hsg | hsh
        · contradiction
        · have hsh' : p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ h p.2 ≠ 0 := by
            rw [mem_finite_convolution_support] at hsh
            exact hsh
          have h0 : g p.2 = 0 := by
            by_contra hne'
            simp_all only [ne_eq, AddSubgroup.coe_add, Pi.add_apply, Finset.mem_union, Set.Finite.mem_toFinset,
              Set.mem_setOf_eq, not_false_eq_true, and_self, not_true_eq_false, T, Sg, Sh]
          simp_all only [ne_eq, AddSubgroup.coe_add, Pi.add_apply, map_add, Finset.mem_union, Set.Finite.mem_toFinset,
            Set.mem_setOf_eq, not_false_eq_true, not_true_eq_false, and_false, or_true, map_zero, T, Sg, Sh]
      simp only [h_term]
  have hSh : ∑ p ∈ Sh, α (f p.1) (h p.2) =
             ∑ p ∈ T, α (f p.1) (h p.2) := by
    apply Finset.sum_subset
    · intro p hp; apply Finset.mem_union.mpr; right; exact hp
    · intro p hp hnot
      have h_term : α (f p.1) (h p.2) = 0 := by
        by_contra hne
        have hp' : p ∈ Sg ∨ p ∈ Sh := Finset.mem_union.mp hp
        rcases hp' with hsg | hsh
        · have hsg' : p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ g p.2 ≠ 0 := by
            rw [mem_finite_convolution_support] at hsg
            exact hsg
          have h0 : h p.2 = 0 := by
            by_contra hne'
            simp_all only [ne_eq, AddSubgroup.coe_add, Pi.add_apply, Finset.mem_union, Set.Finite.mem_toFinset,
              Set.mem_setOf_eq, not_false_eq_true, and_self, not_true_eq_false, T, Sg, Sh]
          simp_all only [ne_eq, AddSubgroup.coe_add, Pi.add_apply, map_add, Finset.mem_union, Set.Finite.mem_toFinset,
            Set.mem_setOf_eq, not_false_eq_true, not_true_eq_false, and_false, or_false, map_zero, T, Sg, Sh]
        · contradiction
      simp only [h_term]
  rw [hS, hSg, hSh, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp_all only [ne_eq, AddSubgroup.coe_add, Pi.add_apply, map_add, Finset.mem_union, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq, T, Sg, Sh]

/-- Auxiliary: the iterated product `(f * g) * h` evaluated at `d` rewrites as a sum over the
finite triple support of `(f, g, h)` at `d`. -/
private lemma novikovSeriesMul_left_eq_triple_sum {A B C D F : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup F]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (h : NovikovSeries Γ ι C)
    (α : A →+ B →+ D) (β : D →+ C →+ F) (d : ι → Γ) :
    (novikovSeriesMul (novikovSeriesMul f g α) h β) d =
    ∑ t ∈ (finite_triple_support f g h d).toFinset,
      β (α (f t.1) (g t.2.1)) (h t.2.2) := by
  classical
  set T := (finite_triple_support f g h d).toFinset with hT_def
  set P := (finite_convolution_support (novikovSeriesMul f g α) h d).toFinset with hP_def
  set Q := T.image (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1 + t.2.1, t.2.2)) with hQ_def
  -- (f * g)(p) is the convolution sum.
  have hfg_def : ∀ p : ι → Γ, (novikovSeriesMul f g α) p =
      ∑ q ∈ (finite_convolution_support f g p).toFinset, α (f q.1) (g q.2) := by
    intro p; rfl
  -- Step 1: P ⊆ Q.
  have hPQ : P ⊆ Q := by
    intro p hp
    rw [hP_def, mem_finite_convolution_support] at hp
    obtain ⟨hp_sum, hp_fg, hp_h⟩ := hp
    have hFCS_ne : (finite_convolution_support f g p.1).toFinset.Nonempty := by
      by_contra h_emp
      rw [Finset.not_nonempty_iff_eq_empty] at h_emp
      apply hp_fg
      rw [hfg_def, h_emp, Finset.sum_empty]
    obtain ⟨q, hq⟩ := hFCS_ne
    rw [mem_finite_convolution_support] at hq
    obtain ⟨hq_sum, hq_f, hq_g⟩ := hq
    rw [hQ_def, Finset.mem_image]
    refine ⟨(q.1, q.2, p.2), ?_, ?_⟩
    · rw [hT_def, mem_finite_triple_support]
      refine ⟨?_, hq_f, hq_g, hp_h⟩
      change q.1 + q.2 + p.2 = d
      rw [hq_sum]; exact hp_sum
    · change (q.1 + q.2, p.2) = p
      rw [hq_sum]
  -- Step 2: Sum over P equals sum over Q (extra terms vanish).
  have hPQ_sum : (∑ p ∈ P, β ((novikovSeriesMul f g α) p.1) (h p.2)) =
      ∑ p ∈ Q, β ((novikovSeriesMul f g α) p.1) (h p.2) := by
    apply Finset.sum_subset hPQ
    intro q hqQ hqnotP
    rw [hQ_def, Finset.mem_image] at hqQ
    obtain ⟨t, htT, hteq⟩ := hqQ
    rw [hT_def, mem_finite_triple_support] at htT
    have hh_q : h q.2 ≠ 0 := by rw [← hteq]; exact htT.2.2.2
    have hsum_q : q.1 + q.2 = d := by
      rw [← hteq]; change t.1 + t.2.1 + t.2.2 = d; exact htT.1
    have hfg_zero : (novikovSeriesMul f g α) q.1 = 0 := by
      by_contra hne
      apply hqnotP
      rw [hP_def, mem_finite_convolution_support]
      exact ⟨hsum_q, hne, hh_q⟩
    rw [hfg_zero, map_zero, AddMonoidHom.zero_apply]
  -- Step 3: Expand inner convolution and flatten via sum_sigma + bijection.
  change ∑ p ∈ P, β ((novikovSeriesMul f g α) p.1) (h p.2) = _
  rw [hPQ_sum]
  have hexp : ∀ q ∈ Q,
      β ((novikovSeriesMul f g α) q.1) (h q.2) =
      ∑ pq ∈ (finite_convolution_support f g q.1).toFinset,
        β (α (f pq.1) (g pq.2)) (h q.2) := by
    intro q _
    rw [hfg_def]
    have key := map_sum (β.flip (h q.2))
        (fun pq : (ι → Γ) × (ι → Γ) => α (f pq.1) (g pq.2))
        (finite_convolution_support f g q.1).toFinset
    simp only [AddMonoidHom.flip_apply] at key
    exact key
  rw [Finset.sum_congr rfl hexp]
  rw [← Finset.sum_sigma (s := Q)
      (t := fun q => (finite_convolution_support f g q.1).toFinset)
      (f := fun σ : (q : (ι → Γ) × (ι → Γ)) × ((ι → Γ) × (ι → Γ)) =>
        β (α (f σ.2.1) (g σ.2.2)) (h σ.1.2))]
  -- Bijection from `Σ q ∈ Q, FCS(f, g, q.1)` to `T`.
  refine Finset.sum_nbij'
    (i := fun σ => (σ.2.1, σ.2.2, σ.1.2))
    (j := fun t => ⟨(t.1 + t.2.1, t.2.2), (t.1, t.2.1)⟩)
    ?_ ?_ ?_ ?_ ?_
  · -- forward maps into T
    intro σ hσ
    rw [Finset.mem_sigma] at hσ
    obtain ⟨hq, hpq⟩ := hσ
    rw [hQ_def, Finset.mem_image] at hq
    obtain ⟨t0, ht0T, ht0eq⟩ := hq
    rw [hT_def, mem_finite_triple_support] at ht0T
    have hh : h σ.1.2 ≠ 0 := by rw [← ht0eq]; exact ht0T.2.2.2
    have hsum_q : σ.1.1 + σ.1.2 = d := by
      rw [← ht0eq]; change t0.1 + t0.2.1 + t0.2.2 = d; exact ht0T.1
    rw [mem_finite_convolution_support] at hpq
    obtain ⟨hpq_sum, hpq_f, hpq_g⟩ := hpq
    rw [hT_def, mem_finite_triple_support]
    refine ⟨?_, hpq_f, hpq_g, hh⟩
    change σ.2.1 + σ.2.2 + σ.1.2 = d
    rw [hpq_sum]; exact hsum_q
  · -- inverse maps into source
    intro t ht
    rw [hT_def, mem_finite_triple_support] at ht
    obtain ⟨ht_sum, ht_f, ht_g, ht_h⟩ := ht
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [hQ_def, Finset.mem_image]
      refine ⟨t, ?_, rfl⟩
      rw [hT_def, mem_finite_triple_support]
      exact ⟨ht_sum, ht_f, ht_g, ht_h⟩
    · rw [mem_finite_convolution_support]
      exact ⟨rfl, ht_f, ht_g⟩
  · -- left_inv: j (i σ) = σ
    intro σ hσ
    rw [Finset.mem_sigma] at hσ
    obtain ⟨_, hpq⟩ := hσ
    rw [mem_finite_convolution_support] at hpq
    obtain ⟨hpq_sum, _, _⟩ := hpq
    -- σ = ⟨σ.1, σ.2⟩, j (i σ) = ⟨(σ.2.1+σ.2.2, σ.1.2), (σ.2.1, σ.2.2)⟩
    -- need σ.1 = (σ.2.1+σ.2.2, σ.1.2) and σ.2 = (σ.2.1, σ.2.2)
    obtain ⟨q, pq⟩ := σ
    obtain ⟨q1, q2⟩ := q
    obtain ⟨pq1, pq2⟩ := pq
    simp only at hpq_sum
    simp only [hpq_sum]
  · -- right_inv: i (j t) = t
    intro t _
    obtain ⟨t1, t2, t3⟩ := t
    rfl
  · -- function values match
    intro σ _
    rfl

/-- Auxiliary: the iterated product `f * (g * h)` evaluated at `d` rewrites as a sum over the
finite triple support of `(f, g, h)` at `d`. -/
private lemma novikovSeriesMul_right_eq_triple_sum {A B C E F : Type*}
    [Fintype ι] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [AddCommGroup F]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (h : NovikovSeries Γ ι C)
    (γ : B →+ C →+ E) (δ : A →+ E →+ F) (d : ι → Γ) :
    (novikovSeriesMul f (novikovSeriesMul g h γ) δ) d =
    ∑ t ∈ (finite_triple_support f g h d).toFinset,
      δ (f t.1) (γ (g t.2.1) (h t.2.2)) := by
  classical
  set T := (finite_triple_support f g h d).toFinset with hT_def
  set P := (finite_convolution_support f (novikovSeriesMul g h γ) d).toFinset with hP_def
  set Q := T.image (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1, t.2.1 + t.2.2)) with hQ_def
  have hgh_def : ∀ p : ι → Γ, (novikovSeriesMul g h γ) p =
      ∑ q ∈ (finite_convolution_support g h p).toFinset, γ (g q.1) (h q.2) := by
    intro p; rfl
  have hPQ : P ⊆ Q := by
    intro p hp
    rw [hP_def, mem_finite_convolution_support] at hp
    obtain ⟨hp_sum, hp_f, hp_gh⟩ := hp
    have hFCS_ne : (finite_convolution_support g h p.2).toFinset.Nonempty := by
      by_contra h_emp
      rw [Finset.not_nonempty_iff_eq_empty] at h_emp
      apply hp_gh
      rw [hgh_def, h_emp, Finset.sum_empty]
    obtain ⟨q, hq⟩ := hFCS_ne
    rw [mem_finite_convolution_support] at hq
    obtain ⟨hq_sum, hq_g, hq_h⟩ := hq
    rw [hQ_def, Finset.mem_image]
    refine ⟨(p.1, q.1, q.2), ?_, ?_⟩
    · rw [hT_def, mem_finite_triple_support]
      refine ⟨?_, hp_f, hq_g, hq_h⟩
      change p.1 + q.1 + q.2 = d
      rw [add_assoc, hq_sum]; exact hp_sum
    · change (p.1, q.1 + q.2) = p
      rw [hq_sum]
  have hPQ_sum : (∑ p ∈ P, δ (f p.1) ((novikovSeriesMul g h γ) p.2)) =
      ∑ p ∈ Q, δ (f p.1) ((novikovSeriesMul g h γ) p.2) := by
    apply Finset.sum_subset hPQ
    intro q hqQ hqnotP
    rw [hQ_def, Finset.mem_image] at hqQ
    obtain ⟨t, htT, hteq⟩ := hqQ
    rw [hT_def, mem_finite_triple_support] at htT
    have hf_q : f q.1 ≠ 0 := by rw [← hteq]; exact htT.2.1
    have hsum_q : q.1 + q.2 = d := by
      rw [← hteq]; change t.1 + (t.2.1 + t.2.2) = d
      rw [← add_assoc]; exact htT.1
    have hgh_zero : (novikovSeriesMul g h γ) q.2 = 0 := by
      by_contra hne
      apply hqnotP
      rw [hP_def, mem_finite_convolution_support]
      exact ⟨hsum_q, hf_q, hne⟩
    rw [hgh_zero, map_zero]
  change ∑ p ∈ P, δ (f p.1) ((novikovSeriesMul g h γ) p.2) = _
  rw [hPQ_sum]
  have hexp : ∀ q ∈ Q,
      δ (f q.1) ((novikovSeriesMul g h γ) q.2) =
      ∑ pq ∈ (finite_convolution_support g h q.2).toFinset,
        δ (f q.1) (γ (g pq.1) (h pq.2)) := by
    intro q _
    rw [hgh_def, map_sum]
  rw [Finset.sum_congr rfl hexp]
  rw [← Finset.sum_sigma (s := Q)
      (t := fun q => (finite_convolution_support g h q.2).toFinset)
      (f := fun σ : (q : (ι → Γ) × (ι → Γ)) × ((ι → Γ) × (ι → Γ)) =>
        δ (f σ.1.1) (γ (g σ.2.1) (h σ.2.2)))]
  refine Finset.sum_nbij'
    (i := fun σ => (σ.1.1, σ.2.1, σ.2.2))
    (j := fun t => ⟨(t.1, t.2.1 + t.2.2), (t.2.1, t.2.2)⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [Finset.mem_sigma] at hσ
    obtain ⟨hq, hpq⟩ := hσ
    rw [hQ_def, Finset.mem_image] at hq
    obtain ⟨t0, ht0T, ht0eq⟩ := hq
    rw [hT_def, mem_finite_triple_support] at ht0T
    have hf : f σ.1.1 ≠ 0 := by rw [← ht0eq]; exact ht0T.2.1
    have hsum_q : σ.1.1 + σ.1.2 = d := by
      rw [← ht0eq]; change t0.1 + (t0.2.1 + t0.2.2) = d
      rw [← add_assoc]; exact ht0T.1
    rw [mem_finite_convolution_support] at hpq
    obtain ⟨hpq_sum, hpq_g, hpq_h⟩ := hpq
    rw [hT_def, mem_finite_triple_support]
    refine ⟨?_, hf, hpq_g, hpq_h⟩
    change σ.1.1 + σ.2.1 + σ.2.2 = d
    rw [add_assoc, hpq_sum]; exact hsum_q
  · intro t ht
    rw [hT_def, mem_finite_triple_support] at ht
    obtain ⟨ht_sum, ht_f, ht_g, ht_h⟩ := ht
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [hQ_def, Finset.mem_image]
      refine ⟨t, ?_, rfl⟩
      rw [hT_def, mem_finite_triple_support]
      exact ⟨ht_sum, ht_f, ht_g, ht_h⟩
    · rw [mem_finite_convolution_support]
      exact ⟨rfl, ht_g, ht_h⟩
  · intro σ hσ
    rw [Finset.mem_sigma] at hσ
    obtain ⟨_, hpq⟩ := hσ
    rw [mem_finite_convolution_support] at hpq
    obtain ⟨hpq_sum, _, _⟩ := hpq
    obtain ⟨q, pq⟩ := σ
    obtain ⟨q1, q2⟩ := q
    obtain ⟨pq1, pq2⟩ := pq
    simp only at hpq_sum
    simp only [hpq_sum]
  · intro t _
    obtain ⟨t1, t2, t3⟩ := t
    rfl
  · intro σ _
    rfl

lemma novikovSeriesMul_assoc {A B C D E F : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (h : NovikovSeries Γ ι C)
    (α : A →+ B →+ D) (β : D →+ C →+ F) (γ : B →+ C →+ E) (δ : A →+ E →+ F)
    (hass : ∀ (a : A) (b : B) (c : C), β (α a b) c = δ a (γ b c)) :
    novikovSeriesMul (novikovSeriesMul f g α) h β = novikovSeriesMul f (novikovSeriesMul g h γ) δ := by
  refine Subtype.ext (funext (fun d => ?_))
  rw [novikovSeriesMul_left_eq_triple_sum f g h α β d,
      novikovSeriesMul_right_eq_triple_sum f g h γ δ d]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  exact hass _ _ _

lemma novikovSeriesMul_left_monomial
    (a : A) (f : NovikovSeries Γ ι B) (α : A →+ B →+ C) (d e : ι → Γ) : (novikovSeriesMul (novikovMonomial a d) f α) (d + e) = α a (f e) := by
  simp only [novikovSeriesMul, novikovSeriesMulFun, ne_eq]
  set P := (finite_convolution_support (novikovMonomial a d) f (d+e)).toFinset
  by_cases ha : a = 0
  · have : novikovMonomial a d = 0 := by
      rw [novikovMonomial]
      simp_all only [ite_self]
      rfl
    rw [this]
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply, map_zero, AddMonoidHom.zero_apply,
      Finset.sum_const_zero]
    simp_all only [map_zero, AddMonoidHom.zero_apply]
  · have hp : P ⊆ {(d, e)} := by
      intro p hp
      simp_all only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, P]
      rcases hp with ⟨hsum, hl, hr⟩
      rw [novikovMonomial] at hl
      have hp1 : p.1 = d := by simp_all only [ne_eq, ite_eq_right_iff, imp_false, Decidable.not_not]
      have hp2 : p.2 = e := by subst hp1; simp_all only [add_right_inj]
      subst hp1 hp2
      simp_all only [Finset.mem_singleton]
    by_cases hpem : P = ∅
    · rw [hpem, Finset.sum_empty]
      have nel : (d, e) ∉ P := by simp_all only [Finset.notMem_empty, not_false_eq_true, P]
      simp only [Set.Finite.mem_toFinset, Set.notMem_setOf_iff, P] at nel
      push Not at nel
      rw [novikovMonomial] at nel
      simp_all only [ne_eq, ↓reduceIte, not_false_eq_true, map_zero]
    · have : P = {(d, e)} := by simp_all only [ne_eq, Finset.subset_singleton_iff, false_or, P]
      rw [this, Finset.sum_singleton, novikovMonomial]
      simp only [↓reduceIte]

lemma novikovSeriesMul_right_monomial
    (f : NovikovSeries Γ ι A) (b : B) (α : A →+ B →+ C) (d e : ι → Γ) : (novikovSeriesMul f (novikovMonomial b d) α) (e + d) = α (f e) b  := by
  simp only [novikovSeriesMul, novikovSeriesMulFun, ne_eq]
  set P := (finite_convolution_support f (novikovMonomial b d) (e+d)).toFinset
  by_cases hb : b = 0
  · have : novikovMonomial b d = 0 := by
      rw [novikovMonomial]
      simp_all only [ite_self]
      rfl
    rw [this]
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero]
    simp_all only [map_zero]
  · have hp : P ⊆ {(e, d)} := by
      intro p hp
      simp_all only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, P]
      rcases hp with ⟨hsum, hl, hr⟩
      rw [novikovMonomial] at hr
      have hp1 : p.2 = d := by simp_all only [ne_eq, ite_eq_right_iff, imp_false, Decidable.not_not]
      have hp2 : p.1 = e := by
        subst hp1
        simp_all only [add_left_inj, ↓reduceIte]
      subst hp1 hp2
      simp_all only [Finset.mem_singleton]
    by_cases hpem : P = ∅
    · rw [hpem, Finset.sum_empty]
      have nel : (e, d) ∉ P := by simp_all only [Finset.notMem_empty, not_false_eq_true, P]
      simp only [Set.Finite.mem_toFinset, Set.notMem_setOf_iff, P] at nel
      push Not at nel
      rw [novikovMonomial] at nel
      simp_all only [ne_eq, ↓reduceIte, imp_false, not_not,
        map_zero, AddMonoidHom.zero_apply]
    · have : P = {(e, d)} := by simp_all only [ne_eq, Finset.subset_singleton_iff, false_or, P]
      rw [this, Finset.sum_singleton, novikovMonomial]
      simp only [↓reduceIte]


end Novikov
