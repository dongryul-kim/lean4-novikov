
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Finiteness conditions on subsets of `ι → Γ`.

This file is independent of `NovikovSeries`: it isolates the analytic
finiteness condition that the support of a Novikov series is required to
satisfy and proves stability properties (subsets, finite unions, and the
convolution-style closure properties needed for the multiplication of
Novikov series). -/

namespace Novikov

variable {ι : Type*} [Fintype ι]
variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S}

/-- A subset of `ι → Γ` has *Novikov finiteness* if, for any positive weight vector
`s : ι → ℝ` and any cutoff `C`, the elements of the set whose `s`-weighted real
coordinate sum is less than `C` form a finite set. -/
def hasNovikovFiniteness (T : Set (ι → Γ)) : Prop :=
  ∀ (s : ι → ℝ) (_ : ∀ i, 0 < s i) (C : ℝ),
    {d ∈ T | ∑ i, s i * (d i : ℝ) < C}.Finite

/-- Extract the degree-coordinate equality `(d1 i : ℝ) + (d2 i : ℝ) = (d i : ℝ)` from
a Pi addition equality `d1 + d2 = d`. -/
lemma coe_add_apply {d1 d2 d : ι → Γ} (h : d1 + d2 = d) (i : ι) : (d1 i : ℝ) + (d2 i : ℝ) = (d i : ℝ) := by
  simpa [Pi.add_apply] using congrArg (fun f : ι → Γ => (f i : ℝ)) h

/-- Variant with an offset: `(d0 i : ℝ) + (d1 i : ℝ) + (d2 i : ℝ) = (d i : ℝ)` from
`d0 + d1 + d2 = d`. -/
lemma coe_add_apply_offset {d0 d1 d2 d : ι → Γ} (h : d0 + d1 + d2 = d) (i : ι) :
    (d0 i : ℝ) + (d1 i : ℝ) + (d2 i : ℝ) = (d i : ℝ) := by
  simpa [Pi.add_apply, add_assoc] using congrArg (fun f : ι → Γ => (f i : ℝ)) h

/-- The support of a function `f : (ι → Γ) → A` valued in a type with `Zero`. -/
abbrev fnSupport {A : Type*} [Zero A] (f : (ι → Γ) → A) : Set (ι → Γ) := {d | f d ≠ 0}

lemma mem_fnSupport {A : Type*} [Zero A] {f : (ι → Γ) → A} {d : ι → Γ} :
    d ∈ fnSupport f ↔ f d ≠ 0 := Iff.rfl

/-- Novikov finiteness is preserved by subsets. -/
lemma hasNovikovFiniteness.subset {T T' : Set (ι → Γ)}
    (hT : hasNovikovFiniteness T) (h : T' ⊆ T) : hasNovikovFiniteness T' := by
  intro s hs C
  exact Set.Finite.subset (hT s hs C) (fun d hd => ⟨h hd.1, hd.2⟩)

/-- The empty set has Novikov finiteness. -/
lemma hasNovikovFiniteness_empty : hasNovikovFiniteness (∅ : Set (ι → Γ)) :=
  fun _ _ _ => Set.Finite.subset Set.finite_empty (fun _ hd => hd.1.elim)

/-- A union of two Novikov-finite subsets is Novikov-finite. -/
lemma hasNovikovFiniteness.union {T1 T2 : Set (ι → Γ)}
    (h1 : hasNovikovFiniteness T1) (h2 : hasNovikovFiniteness T2) :
    hasNovikovFiniteness (T1 ∪ T2) := by
  intro s hs C
  have hsub : {d ∈ T1 ∪ T2 | ∑ i, s i * (d i : ℝ) < C} ⊆
      {d ∈ T1 | ∑ i, s i * (d i : ℝ) < C} ∪ {d ∈ T2 | ∑ i, s i * (d i : ℝ) < C} := by
    rintro d ⟨hT, hlt⟩
    rcases hT with hT1 | hT2
    · exact Or.inl ⟨hT1, hlt⟩
    · exact Or.inr ⟨hT2, hlt⟩
  exact Set.Finite.subset (Set.Finite.union (h1 s hs C) (h2 s hs C)) hsub

section Convolution

/-- Convolution-style finiteness for pairs: if `T1` and `T2` are Novikov-finite,
the set of pairs `(d1, d2) ∈ T1 × T2` whose weighted coordinatewise sum is less
than `L` is finite. -/
lemma finite_pair_lt {T1 T2 : Set (ι → Γ)}
    (h1 : hasNovikovFiniteness T1) (h2 : hasNovikovFiniteness T2)
    (s : ι → ℝ) (hs : ∀ i, 0 < s i) (L : ℝ) :
    {p : (ι → Γ) × (ι → Γ) | p.1 ∈ T1 ∧ p.2 ∈ T2 ∧
        ∑ i, s i * (p.1 i + p.2 i : ℝ) < L}.Finite := by
  let B1 : Set (ι → Γ) := {d1 | d1 ∈ T1 ∧ ∑ i, s i * (d1 i : ℝ) < L + 1}
  let B2 : Set (ι → Γ) := {d2 | d2 ∈ T2 ∧ ∑ i, s i * (d2 i : ℝ) < 0}
  have hB1 : B1.Finite := h1 s hs (L + 1)
  have hB2 : B2.Finite := h2 s hs 0
  let U1 := ⋃ d1 ∈ B1, (fun d2 => (d1, d2)) ''
    {d2 : ι → Γ | d2 ∈ T2 ∧ ∑ i, s i * (d2 i : ℝ) < L - ∑ i, s i * (d1 i : ℝ)}
  let U2 := ⋃ d2 ∈ B2, (fun d1 => (d1, d2)) ''
    {d1 : ι → Γ | d1 ∈ T1 ∧ ∑ i, s i * (d1 i : ℝ) < L - ∑ i, s i * (d2 i : ℝ)}
  have hU1 : U1.Finite :=
    Set.Finite.biUnion hB1 (fun d1 _ =>
      (h2 s hs (L - ∑ i, s i * (d1 i : ℝ))).image _)
  have hU2 : U2.Finite :=
    Set.Finite.biUnion hB2 (fun d2 _ =>
      (h1 s hs (L - ∑ i, s i * (d2 i : ℝ))).image _)
  refine Set.Finite.subset (hU1.union hU2) (fun ⟨d1, d2⟩ ⟨hT1, hT2, hlt⟩ => ?_)
  dsimp only [U1, U2, B1, B2]
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, exists_prop]
  have h_val (i : ι) : (d1 i + d2 i : ℝ) = (d1 i : ℝ) + (d2 i : ℝ) := by simp
  have hlt' : ∑ i, s i * (d1 i : ℝ) + ∑ i, s i * (d2 i : ℝ) < L := by
    have h_eq : ∑ i, s i * (d1 i + d2 i : ℝ)
        = ∑ i, s i * (d1 i : ℝ) + ∑ i, s i * (d2 i : ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [h_val i, mul_add]
    rwa [h_eq] at hlt
  by_cases hcase : ∑ i, s i * (d1 i : ℝ) < L + 1
  · left
    refine ⟨d1, ⟨hT1, hcase⟩, d2, ⟨hT2, by linarith⟩, rfl⟩
  · right
    have hd2lt : ∑ i, s i * (d2 i : ℝ) < 0 := by linarith
    refine ⟨d2, ⟨hT2, hd2lt⟩, d1, ⟨hT1, by linarith⟩, rfl⟩

/-- For Novikov-finite `T1, T2` and a target `d`, the set of pairs `(d1, d2) ∈ T1 × T2`
with `d1 + d2 = d` is finite. -/
lemma finite_pair_sum_eq {T1 T2 : Set (ι → Γ)}
    (h1 : hasNovikovFiniteness T1) (h2 : hasNovikovFiniteness T2) (d : ι → Γ) :
    {p : (ι → Γ) × (ι → Γ) | p.1 + p.2 = d ∧ p.1 ∈ T1 ∧ p.2 ∈ T2}.Finite := by
  let s : ι → ℝ := fun _ => 1
  have hs : ∀ i, 0 < s i := fun _ => zero_lt_one
  let L := ∑ i, s i * (d i : ℝ)
  refine Set.Finite.subset (finite_pair_lt h1 h2 s hs (L + 1)) (fun p hp => ?_)
  simp only [Set.mem_setOf_eq] at hp ⊢
  refine ⟨hp.2.1, hp.2.2, ?_⟩
  have h_sum_i (i : ι) : (p.1 i : ℝ) + (p.2 i : ℝ) = (d i : ℝ) :=
    coe_add_apply hp.1 i
  rw [Finset.sum_congr rfl (fun i _ => by rw [h_sum_i i])]
  linarith

/-- Variant of `finite_pair_sum_eq` with an offset: pairs `(d1, d2) ∈ T1 × T2`
with `d0 + d1 + d2 = d`. -/
lemma finite_pair_sum_eq_offset {T1 T2 : Set (ι → Γ)}
    (h1 : hasNovikovFiniteness T1) (h2 : hasNovikovFiniteness T2) (d d0 : ι → Γ) :
    {p : (ι → Γ) × (ι → Γ) | d0 + p.1 + p.2 = d ∧ p.1 ∈ T1 ∧ p.2 ∈ T2}.Finite := by
  let s : ι → ℝ := fun _ => 1
  have hs : ∀ i, 0 < s i := fun _ => zero_lt_one
  let L : ℝ := ∑ i, s i * (d i : ℝ) - ∑ i, s i * (d0 i : ℝ)
  refine Set.Finite.subset (finite_pair_lt h1 h2 s hs (L + 1)) (fun p hp => ?_)
  simp only [Set.mem_setOf_eq] at hp ⊢
  refine ⟨hp.2.1, hp.2.2, ?_⟩
  have h_sum_i (i : ι) : (p.1 i : ℝ) + (p.2 i : ℝ) = (d i : ℝ) - (d0 i : ℝ) := by
    have h_eq : (d0 i : ℝ) + (p.1 i : ℝ) + (p.2 i : ℝ) = (d i : ℝ) :=
      coe_add_apply_offset hp.1 i
    linarith
  rw [Finset.sum_congr rfl (fun i _ => by rw [h_sum_i i])]
  have h_sub_distrib : ∑ i, s i * ((d i : ℝ) - (d0 i : ℝ))
      = ∑ i, (s i * (d i : ℝ) - s i * (d0 i : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h_sub_distrib, Finset.sum_sub_distrib]
  linarith

/-- For Novikov-finite `T1, T2, T3` and a target `d`, the set of triples
`(d1, d2, d3) ∈ T1 × T2 × T3` with `d1 + d2 + d3 = d` is finite. -/
lemma finite_triple_sum_eq {T1 T2 T3 : Set (ι → Γ)}
    (h1 : hasNovikovFiniteness T1) (h2 : hasNovikovFiniteness T2)
    (h3 : hasNovikovFiniteness T3) (d : ι → Γ) :
    {t : (ι → Γ) × (ι → Γ) × (ι → Γ) |
      t.1 + t.2.1 + t.2.2 = d ∧ t.1 ∈ T1 ∧ t.2.1 ∈ T2 ∧ t.2.2 ∈ T3}.Finite := by
  let s : ι → ℝ := fun _ => 1
  have hs : ∀ i, 0 < s i := fun _ => zero_lt_one
  let L : ℝ := ∑ i, s i * (d i : ℝ)
  let B1 : Set (ι → Γ) := {d1 | d1 ∈ T1 ∧ ∑ i, s i * (d1 i : ℝ) < L + 1}
  let B2 : Set (ι → Γ) := {d2 | d2 ∈ T2 ∧ ∑ i, s i * (d2 i : ℝ) < 0}
  let B3 : Set (ι → Γ) := {d3 | d3 ∈ T3 ∧ ∑ i, s i * (d3 i : ℝ) < 0}
  have hB1 : B1.Finite := h1 s hs (L + 1)
  have hB2 : B2.Finite := h2 s hs 0
  have hB3 : B3.Finite := h3 s hs 0
  let S : Set ((ι → Γ) × (ι → Γ) × (ι → Γ)) :=
    {t | t.1 + t.2.1 + t.2.2 = d ∧ t.1 ∈ T1 ∧ t.2.1 ∈ T2 ∧ t.2.2 ∈ T3}
  let S1 := {t ∈ S | t.1 ∈ B1}
  let S2 := {t ∈ S | t.2.1 ∈ B2}
  let S3 := {t ∈ S | t.2.2 ∈ B3}
  have h_sub : S ⊆ S1 ∪ S2 ∪ S3 := by
    rintro ⟨d1, d2, d3⟩ ⟨hsum, hT1, hT2, hT3⟩
    by_contra! hbad
    have ht : ((d1, d2, d3) : (ι → ↥Γ) × (ι → ↥Γ) × (ι → ↥Γ)) ∈ S :=
      ⟨hsum, hT1, hT2, hT3⟩
    simp only [Set.mem_setOf_eq, Set.sep_and, Set.mem_union, Set.mem_inter_iff, ht,
      hT1, and_self, true_and, hT2, hT3, not_or, not_lt,
      S1, B1, S2, B2, S3, B3] at hbad
    have h_sum_i (i : ι) : (d i : ℝ) = (d1 i : ℝ) + (d2 i : ℝ) + (d3 i : ℝ) :=
      (coe_add_apply_offset hsum i).symm
    have hL : L = ∑ i, s i * (d1 i : ℝ) + ∑ i, s i * (d2 i : ℝ)
        + ∑ i, s i * (d3 i : ℝ) := by
      simp only [L, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [h_sum_i i]; ring
    linarith
  have hS1 : S1.Finite := by
    have h_inj : Set.InjOn (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.2.1, t.2.2)) S1 := by
      rintro ⟨d1, d2, d3⟩ ⟨ht, _⟩ ⟨d1', d2', d3'⟩ ⟨ht', _⟩ heq
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      have h_d1 : d1 = d1' := by
        have h1 : d1 + d2 + d3 = d := by simpa using ht.1
        have h2 : d1' + d2 + d3 = d := by simpa using ht'.1
        have h_eq : (d1 + d2) + d3 = (d1' + d2) + d3 := by simpa [add_assoc] using h1.trans h2.symm
        exact add_right_cancel (add_right_cancel h_eq)
      rw [h_d1]
    have h_image : ((fun t => (t.2.1, t.2.2)) '' S1).Finite := by
      have h_sub' : (fun t => (t.2.1, t.2.2)) '' S1 ⊆ ⋃ d1 ∈ B1,
          {p : (ι → Γ) × (ι → Γ) | d1 + p.1 + p.2 = d ∧ p.1 ∈ T2 ∧ p.2 ∈ T3} := by
        rintro ⟨d2, d3⟩ ⟨⟨d1, d2', d3'⟩, ⟨ht, hd1⟩, heq⟩
        simp only [Set.mem_iUnion, exists_prop]
        refine ⟨d1, hd1, ?_⟩
        simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact ⟨ht.1, ht.2.2.1, ht.2.2.2⟩
      apply Set.Finite.subset _ h_sub'
      exact Set.Finite.biUnion hB1 (fun d1 _ => finite_pair_sum_eq_offset h2 h3 d d1)
    exact Set.Finite.of_finite_image h_image h_inj
  have hS2 : S2.Finite := by
    have h_inj : Set.InjOn (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1, t.2.2)) S2 := by
      rintro ⟨d1, d2, d3⟩ ⟨ht, _⟩ ⟨d1', d2', d3'⟩ ⟨ht', _⟩ heq
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      have h_d2 : d2 = d2' := by
        have h1 : d1 + d2 + d3 = d := by simpa using ht.1
        have h2 : d1 + d2' + d3 = d := by simpa using ht'.1
        have h_eq : d2 + (d1 + d3) = d2' + (d1 + d3) := by
          simpa [add_comm, add_left_comm, add_assoc] using h1.trans h2.symm
        exact add_right_cancel h_eq
      rw [h_d2]
    have h_image : ((fun t => (t.1, t.2.2)) '' S2).Finite := by
      have h_sub' : (fun t => (t.1, t.2.2)) '' S2 ⊆ ⋃ d2 ∈ B2,
          {p : (ι → Γ) × (ι → Γ) | d2 + p.1 + p.2 = d ∧ p.1 ∈ T1 ∧ p.2 ∈ T3} := by
        rintro ⟨d1, d3⟩ ⟨⟨d1', d2, d3'⟩, ⟨ht, hd2⟩, heq⟩
        simp only [Set.mem_iUnion, exists_prop]
        refine ⟨d2, hd2, ?_⟩
        simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        refine ⟨by simpa [add_comm, add_left_comm, add_assoc] using ht.1, ht.2.1, ht.2.2.2⟩
      apply Set.Finite.subset _ h_sub'
      exact Set.Finite.biUnion hB2 (fun d2 _ => finite_pair_sum_eq_offset h1 h3 d d2)
    exact Set.Finite.of_finite_image h_image h_inj
  have hS3 : S3.Finite := by
    have h_inj : Set.InjOn (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1, t.2.1)) S3 := by
      rintro ⟨d1, d2, d3⟩ ⟨ht, _⟩ ⟨d1', d2', d3'⟩ ⟨ht', _⟩ heq
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      have h_d3 : d3 = d3' := by
        have h1 : d1 + d2 + d3 = d := by simpa using ht.1
        have h2 : d1 + d2 + d3' = d := by simpa using ht'.1
        have h_eq : d3 + (d1 + d2) = d3' + (d1 + d2) := by
          simpa [add_comm, add_left_comm, add_assoc] using h1.trans h2.symm
        exact add_right_cancel h_eq
      rw [h_d3]
    have h_image : ((fun t => (t.1, t.2.1)) '' S3).Finite := by
      have h_sub' : (fun t => (t.1, t.2.1)) '' S3 ⊆ ⋃ d3 ∈ B3,
          {p : (ι → Γ) × (ι → Γ) | d3 + p.1 + p.2 = d ∧ p.1 ∈ T1 ∧ p.2 ∈ T2} := by
        rintro ⟨d1, d2⟩ ⟨⟨d1', d2', d3⟩, ⟨ht, hd3⟩, heq⟩
        simp only [Set.mem_iUnion, exists_prop]
        refine ⟨d3, hd3, ?_⟩
        simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        refine ⟨by simpa [add_comm, add_left_comm, add_assoc] using ht.1, ht.2.1, ht.2.2.1⟩
      apply Set.Finite.subset _ h_sub'
      exact Set.Finite.biUnion hB3 (fun d3 _ => finite_pair_sum_eq_offset h1 h2 d d3)
    exact Set.Finite.of_finite_image h_image h_inj
  exact Set.Finite.subset ((hS1.union hS2).union hS3) h_sub

end Convolution

end Novikov
