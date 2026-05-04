
import Novikov.Series.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Finite.Lattice

/-! # Some finiteness lemmas used to define and prove basic properties
  of the product structure -/

namespace Novikov

variable {ι A B C : Type*} [Fintype ι] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S}

section Finiteness

/-- Restatement of the defining Novikov finiteness condition for readability. -/
lemma finite_support_below (f : NovikovSeries Γ ι A) (s : ι → ℝ)
    (hs : ∀ i, 0 < s i) (C : ℝ) :
    {d : ι → Γ | f d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C}.Finite :=
  f.prop s hs C

/-- For a fixed `d : ι → Γ`, the set of pairs `(d1, d2)` with `d1 + d2 = d`,
`f(d1) ≠ 0`, and `g(d2) ≠ 0` is finite. -/
lemma finite_convolution_support (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (d : ι → Γ) :
    {p : (ι → Γ) × (ι → Γ) | p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ g p.2 ≠ 0}.Finite := by
  let s : ι → ℝ := fun _ => 1
  have hs : ∀ i, 0 < s i := fun i => zero_lt_one
  let L : ℝ := ∑ i, s i * (d i : ℝ)
  let Sf := {d1 : ι → Γ | f d1 ≠ 0 ∧ ∑ i, s i * (d1 i : ℝ) < L + 1}
  let Sg := {d2 : ι → Γ | g d2 ≠ 0 ∧ ∑ i, s i * (d2 i : ℝ) < 0}
  have hf : Sf.Finite := finite_support_below f s hs (L + 1)
  have hg : Sg.Finite := finite_support_below g s hs 0
  let P := {p : (ι → Γ) × (ι → Γ) | p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ g p.2 ≠ 0}
  let P1 := {p : (ι → Γ) × (ι → Γ) | p.1 ∈ Sf ∧ p.1 + p.2 = d ∧ g p.2 ≠ 0}
  let P2 := {p : (ι → Γ) × (ι → Γ) | p.2 ∈ Sg ∧ p.1 + p.2 = d ∧ f p.1 ≠ 0}
  have h_sub : P ⊆ P1 ∪ P2 := by
    rintro ⟨d1, d2⟩ ⟨hsum, hf1, hg2⟩
    by_cases h : d1 ∈ Sf
    · left
      exact ⟨h, hsum, hg2⟩
    · right
      simp only [ne_eq, Set.mem_setOf_eq, not_and, not_lt, Sf] at h
      have hgd2 : d2 ∈ Sg := by
        refine ⟨hg2, ?_⟩
        have hL : L = ∑ i, s i * (d1 i : ℝ) + ∑ i, s i * (d2 i : ℝ) := by
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
        have h_d1_ge : L + 1 ≤ ∑ i, s i * (d1 i : ℝ) := h hf1
        nlinarith
      exact ⟨hgd2, hsum, hf1⟩
  have hP1 : P1.Finite := by
    have h_inj : Set.InjOn Prod.fst P1 := by
      rintro ⟨d1, d2⟩ ⟨hd1, hsum, _⟩ ⟨d1', d2'⟩ ⟨hd1', hsum', _⟩ h_eq
      simp only at h_eq
      have h_d2 : d2 = d2' := by
        funext i
        have h := congr_fun hsum i
        have h' := congr_fun hsum' i
        simp only [Pi.add_apply] at h h'
        have h_eq_i : d1 i = d1' i := by
          rw [h_eq]
        have h_eq2_i : d2 i = d2' i := by
          subst hsum h_eq
          simp_all only [zero_lt_one, implies_true, ne_eq, one_mul, Pi.add_apply,
            Set.mem_setOf_eq, not_false_eq_true, and_self, add_right_inj, s, Sg, Sf, L, P, P1, P2]
        exact h_eq2_i
      subst hsum h_eq h_d2
      simp_all only [zero_lt_one, implies_true, ne_eq, one_mul, not_false_eq_true, Pi.add_apply,
        Set.mem_setOf_eq, and_self, s, Sg, Sf, L, P, P1, P2]
    have h_image : (Prod.fst '' P1).Finite := by
      apply Set.Finite.subset hf
      rintro d1 ⟨d2, ⟨hd1, _, _⟩, rfl⟩
      exact hd1
    exact Set.Finite.of_finite_image h_image h_inj
  have hP2 : P2.Finite := by
    have h_inj : Set.InjOn Prod.snd P2 := by
      rintro ⟨d1, d2⟩ ⟨_, hsum, _⟩ ⟨d1', d2'⟩ ⟨_, hsum', _⟩ h_eq
      simp only at h_eq
      have h_d1 : d1 = d1' := by
        funext i
        have h := congr_fun hsum i
        have h' := congr_fun hsum' i
        simp only [Pi.add_apply] at h h'
        have h_eq_i : d2 i = d2' i := by
          rw [h_eq]
        have h2 : d1 i + d2 i = d1' i + d2' i := by rw [h, h']
        rw [h_eq_i] at h2
        exact add_right_cancel h2
      simp only [h_d1, h_eq]
    have h_image : (Prod.snd '' P2).Finite := by
      apply Set.Finite.subset hg
      rintro d2 ⟨d1, ⟨hd1, _, _⟩, rfl⟩
      exact hd1
    exact Set.Finite.of_finite_image h_image h_inj
  exact Set.Finite.subset (Set.Finite.union hP1 hP2) h_sub

/-- Variant of `finite_convolution_support` where the sum condition is `d0 + p.1 + p.2 = d`. -/
lemma finite_convolution_support_three (f : NovikovSeries Γ ι A)
    (g : NovikovSeries Γ ι B)
    (d d0 : ι → Γ) :
    {p : (ι → Γ) × (ι → Γ) | d0 + p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ g p.2 ≠ 0}.Finite := by
  let s : ι → ℝ := fun _ => 1
  have hs : ∀ i, 0 < s i := fun i => zero_lt_one
  let L : ℝ := ∑ i, s i * (d i : ℝ) - ∑ i, s i * (d0 i : ℝ)
  let Sf := {d1 : ι → Γ | f d1 ≠ 0 ∧ ∑ i, s i * (d1 i : ℝ) < L + 1}
  let Sg := {d2 : ι → Γ | g d2 ≠ 0 ∧ ∑ i, s i * (d2 i : ℝ) < 0}
  have hf : Sf.Finite := finite_support_below f s hs (L + 1)
  have hg : Sg.Finite := finite_support_below g s hs 0
  let P := {p : (ι → Γ) × (ι → Γ) | d0 + p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ g p.2 ≠ 0}
  let P1 := {p : (ι → Γ) × (ι → Γ) | p.1 ∈ Sf ∧ d0 + p.1 + p.2 = d ∧ g p.2 ≠ 0}
  let P2 := {p : (ι → Γ) × (ι → Γ) | p.2 ∈ Sg ∧ d0 + p.1 + p.2 = d ∧ f p.1 ≠ 0}
  have h_sub : P ⊆ P1 ∪ P2 := by
    rintro ⟨d1, d2⟩ ⟨hsum, hf1, hg2⟩
    by_cases h : d1 ∈ Sf
    · left
      exact ⟨h, hsum, hg2⟩
    · right
      simp only [ne_eq, Set.mem_setOf_eq, not_and, not_lt, Sf] at h
      have hgd2 : d2 ∈ Sg := by
        refine ⟨hg2, ?_⟩
        have hL : L = ∑ i, s i * (d1 i : ℝ) + ∑ i, s i * (d2 i : ℝ) := by
          have h_eq : ∑ i, s i * (d i : ℝ) = ∑ i, s i * (d0 i : ℝ) + ∑ i, s i * (d1 i : ℝ) + ∑ i, s i * (d2 i : ℝ) := by
            have h_eq_i : ∀ i, (d i : ℝ) = (d0 i : ℝ) + (d1 i : ℝ) + (d2 i : ℝ) := by
              intro i
              have h := congr_fun hsum i
              simp only [Pi.add_apply] at h
              rw [← h]
              rfl
            rw [Finset.sum_congr rfl (fun i _ => by rw [h_eq_i i])]
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [show L = ∑ i, s i * (d i : ℝ) - ∑ i, s i * (d0 i : ℝ) by rfl, h_eq]
          ring
        have h_d1_ge : L + 1 ≤ ∑ i, s i * (d1 i : ℝ) := h hf1
        nlinarith
      exact ⟨hgd2, hsum, hf1⟩
  have hP1 : P1.Finite := by
    have h_inj : Set.InjOn Prod.fst P1 := by
      rintro ⟨d1, d2⟩ ⟨hd1, hsum, _⟩ ⟨d1', d2'⟩ ⟨hd1', hsum', _⟩ h_eq
      simp only at h_eq
      have h_d2 : d2 = d2' := by
        funext i
        have h := congr_fun hsum i
        have h' := congr_fun hsum' i
        simp only [Pi.add_apply] at h h'
        have h_eq_i : d1 i = d1' i := by
          rw [h_eq]
        have h2 : d0 i + d1 i + d2 i = d0 i + d1' i + d2' i := by rw [h, h']
        rw [h_eq_i] at h2
        grind only
      simp only [h_d2, h_eq]
    have h_image : (Prod.fst '' P1).Finite := by
      apply Set.Finite.subset hf
      rintro d1 ⟨d2, ⟨hd1, _, _⟩, rfl⟩
      exact hd1
    exact Set.Finite.of_finite_image h_image h_inj
  have hP2 : P2.Finite := by
    have h_inj : Set.InjOn Prod.snd P2 := by
      rintro ⟨d1, d2⟩ ⟨_, hsum, _⟩ ⟨d1', d2'⟩ ⟨_, hsum', _⟩ h_eq
      simp only at h_eq
      have h_d1 : d1 = d1' := by
        funext i
        have h := congr_fun hsum i
        have h' := congr_fun hsum' i
        simp only [Pi.add_apply] at h h'
        have h_eq_i : d2 i = d2' i := by
          rw [h_eq]
        have h2 : d0 i + d1 i + d2 i = d0 i + d1' i + d2' i := by rw [h, h']
        rw [h_eq_i] at h2
        grind only
      simp only [h_d1, h_eq]
    have h_image : (Prod.snd '' P2).Finite := by
      apply Set.Finite.subset hg
      rintro d2 ⟨d1, ⟨hd1, _, _⟩, rfl⟩
      exact hd1
    exact Set.Finite.of_finite_image h_image h_inj
  exact Set.Finite.subset (Set.Finite.union hP1 hP2) h_sub

/-- For a fixed `d : ι → Γ`, the set of triples `(d1, d2, d3)` with `d1 + d2 + d3 = d`,
`f(d1) ≠ 0`, `g(d2) ≠ 0`, and `h(d3) ≠ 0` is finite. -/
lemma finite_triple_support (f : NovikovSeries Γ ι A)
  (g : NovikovSeries Γ ι B) (h : NovikovSeries Γ ι C)
  (d : ι → Γ) :
    {t : (ι → Γ) × (ι → Γ) × (ι → Γ) |
      t.1 + t.2.1 + t.2.2 = d ∧ f t.1 ≠ 0 ∧ g t.2.1 ≠ 0 ∧ h t.2.2 ≠ 0}.Finite := by
  let s : ι → ℝ := fun _ => 1
  have hs : ∀ i, 0 < s i := fun i => zero_lt_one
  let L : ℝ := ∑ i, s i * (d i : ℝ)
  let Sf := {d1 : ι → Γ | f d1 ≠ 0 ∧ ∑ i, s i * (d1 i : ℝ) < L + 1}
  let Sg := {d2 : ι → Γ | g d2 ≠ 0 ∧ ∑ i, s i * (d2 i : ℝ) < 0}
  let Sh := {d3 : ι → Γ | h d3 ≠ 0 ∧ ∑ i, s i * (d3 i : ℝ) < 0}
  have hf : Sf.Finite := finite_support_below f s hs (L + 1)
  have hg : Sg.Finite := finite_support_below g s hs 0
  have hh : Sh.Finite := finite_support_below h s hs 0
  let T := {t : (ι → Γ) × (ι → Γ) × (ι → Γ) |
    t.1 + t.2.1 + t.2.2 = d ∧ f t.1 ≠ 0 ∧ g t.2.1 ≠ 0 ∧ h t.2.2 ≠ 0}
  -- Case 1: d1 has weighted sum < L + 1
  let T1 := {t ∈ T | t.1 ∈ Sf}
  -- Case 2: d1 is large, so d2 + d3 has negative weighted sum; then either d2 or d3 is negative
  let T2 := {t ∈ T | t.2.1 ∈ Sg}
  let T3 := {t ∈ T | t.2.2 ∈ Sh}
  have h_sub : T ⊆ T1 ∪ T2 ∪ T3 := by
    rintro ⟨d1, d2, d3⟩ ⟨hsum, hf1, hg2, hh3⟩
    by_cases h : d1 ∈ Sf
    · left; left
      exact ⟨⟨hsum, hf1, hg2, hh3⟩, h⟩
    · -- d1 not in Sf, so ∑(d1) ≥ L + 1, thus ∑(d2) + ∑(d3) = L - ∑(d1) < 0
      simp only [Set.mem_setOf_eq, not_and, not_lt, Sf] at h
      have hL : L = ∑ i, s i * (d1 i : ℝ) + ∑ i, s i * (d2 i : ℝ) + ∑ i, s i * (d3 i : ℝ) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        have h_eq : (d i : ℝ) = (d1 i : ℝ) + (d2 i : ℝ) + (d3 i : ℝ) := by
          have h := congr_fun hsum i
          simp only [Pi.add_apply] at h
          rw [← h]
          rfl
        rw [h_eq]
        ring
      have h_d1_ge : L + 1 ≤ ∑ i, s i * (d1 i : ℝ) := h hf1
      have h_d2_d3_neg : ∑ i, s i * (d2 i : ℝ) + ∑ i, s i * (d3 i : ℝ) < 0 := by nlinarith
      by_cases h2 : d2 ∈ Sg
      · left; right
        exact ⟨⟨hsum, hf1, hg2, hh3⟩, h2⟩
      · -- d2 not in Sg, so ∑(d2) ≥ 0, thus ∑(d3) < 0
        simp only [Set.mem_setOf_eq, not_and, not_lt, Sg] at h2
        have h_d2_ge : 0 ≤ ∑ i, s i * (d2 i : ℝ) := h2 hg2
        have h_d3_neg : ∑ i, s i * (d3 i : ℝ) < 0 := by linarith
        have hd3 : d3 ∈ Sh := ⟨hh3, h_d3_neg⟩
        right
        exact ⟨⟨hsum, hf1, hg2, hh3⟩, hd3⟩
  -- T1 is finite
  have hT1 : T1.Finite := by
    have h_inj : Set.InjOn (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.2.1, t.2.2)) T1 := by
      rintro ⟨d1, d2, d3⟩ ⟨ht, _⟩ ⟨d1', d2', d3'⟩ ⟨ht', _⟩ h_eq
      simp only [Prod.mk.injEq] at h_eq
      have h_d1 : d1 = d1' := by
        funext i
        have h := congr_fun ht.1 i
        have h' := congr_fun ht'.1 i
        simp only [Pi.add_apply] at h h'
        rw [h_eq.1, h_eq.2] at h
        grind only
      simp_all only
    have h_image : ((fun t => (t.2.1, t.2.2)) '' T1).Finite := by
      have h_sub' : (fun t => (t.2.1, t.2.2)) '' T1 ⊆ ⋃ d1 ∈ Sf,
          {p : (ι → Γ) × (ι → Γ) | d1 + p.1 + p.2 = d ∧ g p.1 ≠ 0 ∧ h p.2 ≠ 0} := by
        rintro ⟨d2, d3⟩ ⟨⟨d1, d2', d3'⟩, ⟨ht, hd1⟩, h_eq⟩
        simp only [Set.mem_iUnion, exists_prop]
        refine ⟨d1, hd1, ?_⟩
        simp_all only [zero_lt_one, implies_true, ne_eq, one_mul, Set.mem_setOf_eq, Prod.mk.eta, Prod.mk.injEq,
          not_false_eq_true, true_and, and_self, s, Sf, L, Sg, Sh, T, T1, T2, T3]
      apply Set.Finite.subset _ h_sub'
      exact Set.Finite.biUnion hf (fun d1 _ => finite_convolution_support_three g h d d1)
    exact Set.Finite.of_finite_image h_image h_inj
  -- T2 is finite
  have hT2 : T2.Finite := by
    have h_inj : Set.InjOn (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1, t.2.2)) T2 := by
      rintro ⟨d1, d2, d3⟩ ⟨ht, _⟩ ⟨d1', d2', d3'⟩ ⟨ht', _⟩ h_eq
      simp only at h_eq
      have h_d1 : d2 = d2' := by
        funext i
        have h := congr_fun ht.1 i
        have h' := congr_fun ht'.1 i
        simp only [Pi.add_apply] at h h'
        grind only
      simp_all only [Prod.mk.injEq, s, Sf, L, Sg, Sh, T, T1, T2, T3]
    have h_image : ((fun t => (t.1, t.2.2)) '' T2).Finite := by
      have h_sub' : (fun t => (t.1, t.2.2)) '' T2 ⊆ ⋃ d2 ∈ Sg,
          {p : (ι → Γ) × (ι → Γ) | d2 + p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ h p.2 ≠ 0} := by
        rintro ⟨d1, d3⟩ ⟨⟨d1', d2, d3'⟩, ⟨ht, hd2⟩, h_eq⟩
        simp only [Set.mem_iUnion, exists_prop]
        refine ⟨d2, hd2, ?_⟩
        simp_all only [zero_lt_one, implies_true, ne_eq, one_mul, Set.mem_setOf_eq, Prod.mk.injEq, not_false_eq_true,
          true_and, and_self, s, Sf, L, Sg, Sh, T, T1, T2, T3]
        grind only
      apply Set.Finite.subset _ h_sub'
      exact Set.Finite.biUnion hg (fun d2 _ => finite_convolution_support_three f h d d2)
    exact Set.Finite.of_finite_image h_image h_inj
  -- T3 is finite
  have hT3 : T3.Finite := by
    have h_inj : Set.InjOn (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1, t.2.1)) T3 := by
      rintro ⟨d1, d2, d3⟩ ⟨ht, _⟩ ⟨d1', d2', d3'⟩ ⟨ht', _⟩ h_eq
      simp only at h_eq
      have h_d1 : d3 = d3' := by
        funext i
        have h := congr_fun ht.1 i
        have h' := congr_fun ht'.1 i
        simp only [Pi.add_apply] at h h'
        grind only
      simp_all only [Prod.mk.injEq]
    have h_image : ((fun t => (t.1, t.2.1)) '' T3).Finite := by
      have h_sub' : (fun t => (t.1, t.2.1)) '' T3 ⊆ ⋃ d3 ∈ Sh,
          {p : (ι → Γ) × (ι → Γ) | d3 + p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ g p.2 ≠ 0} := by
        rintro ⟨d1, d2⟩ ⟨⟨d1', d2', d3⟩, ⟨ht, hd3⟩, h_eq⟩
        simp only [Set.mem_iUnion, exists_prop]
        refine ⟨d3, hd3, ?_⟩
        simp_all only [zero_lt_one, implies_true, ne_eq, one_mul, Set.mem_setOf_eq, Prod.mk.injEq, not_false_eq_true,
          true_and, and_self, s, Sf, L, Sg, Sh, T, T1, T2, T3]
        grind only
      apply Set.Finite.subset _ h_sub'
      exact Set.Finite.biUnion hh (fun d3 _ => finite_convolution_support_three f g d d3)
    exact Set.Finite.of_finite_image h_image h_inj
  exact Set.Finite.subset (Set.Finite.union (Set.Finite.union hT1 hT2) hT3) h_sub

/-- Membership in the convolution support finset, unfolded to the explicit condition. -/
lemma mem_finite_convolution_support {f : NovikovSeries Γ ι A} {g : NovikovSeries Γ ι B} {d : ι → Γ} {p} :
    p ∈ (finite_convolution_support f g d).toFinset ↔
    p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ g p.2 ≠ 0 := by
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]

/-- Membership in the triple support finset, unfolded to the explicit condition. -/
lemma mem_finite_triple_support {f : NovikovSeries Γ ι A} {g : NovikovSeries Γ ι B} {h : NovikovSeries Γ ι C} {d : ι → Γ} {t} :
    t ∈ (finite_triple_support f g h d).toFinset ↔
    t.1 + t.2.1 + t.2.2 = d ∧ f t.1 ≠ 0 ∧ g t.2.1 ≠ 0 ∧ h t.2.2 ≠ 0 := by
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]

end Finiteness

end Novikov
