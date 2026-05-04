import Novikov.Series.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.Pointwise.Set.Basic

open Pointwise

namespace Novikov

variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S}
variable {ι : Type*} [Fintype ι]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

noncomputable def novikovSeriesMulFun
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B)
    (α : A →+ B →+ C) (d : ι → Γ) : C :=
  let S : Finset ((ι → Γ) × (ι → Γ)) := (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop d).toFinset
  Finset.sum S fun p : (ι → Γ) × (ι → Γ) => α (f p.1) (g p.2)

lemma novikovSeriesMul_largerSum
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B)
    (α : A →+ B →+ C) (d : ι → Γ) (S : Finset ((ι → Γ) × (ι → Γ)))
    (hs : (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop d).toFinset ⊆ S)
    (h_sum : ∀ p ∈ S, p.1 + p.2 = d) :
    novikovSeriesMulFun f g α d = 
    Finset.sum S fun p : (ι → Γ) × (ι → Γ) => α (f p.1) (g p.2) := by
  simp only [novikovSeriesMulFun]
  apply Finset.sum_subset hs
  intro p hp hnot
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hnot
  have h_eq := h_sum p hp
  simp only [h_eq, true_and] at hnot
  by_cases hf : f p.1 = 0
  · rw [hf, map_zero, AddMonoidHom.zero_apply]
  · have hg : g p.2 = 0 := by
      contrapose! hnot
      exact ⟨hf, hnot⟩
    rw [hg, map_zero]

lemma isNovikovSeries_mul {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (α : A →+ B →+ C) :
    isNovikovSeries (fun d => ∑ x ∈ (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop d).toFinset, α (f x.1) (g x.2)) := by
  intro s hs L
  let P := {p : (ι → Γ) × (ι → Γ) | f p.1 ≠ 0 ∧ g p.2 ≠ 0 ∧ ∑ i, s i * (p.1 i + p.2 i : ℝ) < L}
  have hP : P.Finite := finite_pair_lt (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop s hs L
  let f_sum : (ι → Γ) × (ι → Γ) → (ι → Γ) := fun p => p.1 + p.2
  refine Set.Finite.subset (hP.image f_sum) (fun d hd => ?_)
  rcases hd with ⟨hne, hlt⟩
  obtain ⟨p, hp, hprod_nz⟩ : ∃ p ∈ (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop d).toFinset, α (f p.1) (g p.2) ≠ 0 := by
    change (∑ x ∈ _, _) ≠ 0 at hne
    contrapose! hne
    exact Finset.sum_eq_zero hne
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hp
  refine ⟨p, ?_, hp.1⟩
  have h_sum_i : ∀ i, (p.1 i : ℝ) + (p.2 i : ℝ) = (d i : ℝ) := by
    intro i
    have h := congr_fun hp.1 i
    simp only [Pi.add_apply] at h
    have h_real := congr_arg (fun x : Γ => (x : ℝ)) h
    change (p.1 i : ℝ) + (p.2 i : ℝ) = (d i : ℝ) at h_real
    exact h_real
  have h_sum_eq : ∑ i, s i * ((p.1 i : ℝ) + (p.2 i : ℝ)) = ∑ i, s i * (d i : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [h_sum_i i]
  refine ⟨hp.2.1, hp.2.2, ?_⟩
  rwa [h_sum_eq]

lemma is_novikov_series_novikovSeriesMulFun
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B)
    (α : A →+ B →+ C) : isNovikovSeries (novikovSeriesMulFun f g α) :=
  isNovikovSeries_mul f g α

noncomputable def novikovSeriesMul
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B)
    (α : A →+ B →+ C) : NovikovSeries Γ ι C :=
  ⟨novikovSeriesMulFun f g α, is_novikov_series_novikovSeriesMulFun f g α⟩

lemma novikovSeriesMul_zero_mul
    (f : NovikovSeries Γ ι B) (α : A →+ B →+ C) : novikovSeriesMul 0 f α = 0 := by
  ext d
  simp only [novikovSeriesMul, novikovSeriesMulFun, ZeroMemClass.coe_zero, Pi.zero_apply,
    mem_fnSupport, ne_eq, not_true_eq_false, false_and, and_false, Set.setOf_false,
    Set.toFinite_toFinset, Set.toFinset_empty, Finset.sum_empty]

lemma novikovSeriesMul_mul_zero
    (f : NovikovSeries Γ ι A) (α : A →+ B →+ C) : novikovSeriesMul f 0 α = 0 := by
  ext d
  simp only [novikovSeriesMul, novikovSeriesMulFun, mem_fnSupport, ne_eq, ZeroMemClass.coe_zero,
    Pi.zero_apply, not_true_eq_false, and_false, Set.setOf_false, Set.toFinite_toFinset,
    Set.toFinset_empty, Finset.sum_empty]

lemma support_mul_subset (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (α : A →+ B →+ C) :
    (novikovSeriesMul f g α).support ⊆ f.support + g.support := by
  intro d hd
  rw [NovikovSeries.mem_support] at hd
  contrapose! hd
  simp only [NovikovSeries.mem_support, Set.mem_add] at hd
  apply Finset.sum_eq_zero
  intro p hp
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hp
  exfalso
  apply hd
  exact ⟨p.1, hp.2.1, p.2, hp.2.2, hp.1⟩

lemma novikovSeriesMul_right_distrib
    (f g : NovikovSeries Γ ι A) (h : NovikovSeries Γ ι B) (α : A →+ B →+ C) :
    novikovSeriesMul (f + g) h α = novikovSeriesMul f h α + novikovSeriesMul g h α := by
  ext d
  simp only [novikovSeriesMul, novikovSeriesMulFun, AddSubgroup.coe_add, Pi.add_apply]
  have hS : ∑ p ∈ (finite_pair_sum_eq (T1 := fnSupport (f + g).val) (T2 := fnSupport h.val) (f + g).prop h.prop d).toFinset,
              α (f p.1 + g p.1) (h p.2) =
            ∑ p ∈ (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport h.val) f.prop h.prop d).toFinset ∪ (finite_pair_sum_eq (T1 := fnSupport g.val) (T2 := fnSupport h.val) g.prop h.prop d).toFinset,
              α (f p.1 + g p.1) (h p.2) := by
    apply Finset.sum_subset
    · intro p hp
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hp
      apply Finset.mem_union.mpr
      have hdisj : f p.1 ≠ 0 ∨ g p.1 ≠ 0 := by
        by_contra h
        simp only [ne_eq, not_or, not_not] at h
        have : f p.1 + g p.1 = 0 := by simp only [h.1, h.2, add_zero]
        simp_all only [AddSubgroup.coe_add, Pi.add_apply, add_zero, not_true_eq_false, false_and, and_false]
      rcases hdisj with h | h
      · left; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]; exact ⟨hp.1, h, hp.2.2⟩
      · right; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]; exact ⟨hp.1, h, hp.2.2⟩
    · intro p hp hnot
      have h_term : α (f p.1 + g p.1) (h p.2) = 0 := by
        by_contra hne
        rw [Finset.mem_union] at hp
        rcases hp with hsf | hsg
        · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hsf
          have h0 : f p.1 + g p.1 = 0 := by
            by_contra hne'
            simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hnot
            exact hnot ⟨hsf.1, hne', hsf.2.2⟩
          simp_all only [AddSubgroup.coe_add, Pi.add_apply, ne_eq, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
            not_true_eq_false, not_false_eq_true, and_true, and_false, map_zero, AddMonoidHom.zero_apply]
        · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hsg
          have h0 : f p.1 + g p.1 = 0 := by
            by_contra hne'
            simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hnot
            exact hnot ⟨hsg.1, hne', hsg.2.2⟩
          simp_all only [AddSubgroup.coe_add, Pi.add_apply, ne_eq, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
            not_true_eq_false, not_false_eq_true, and_true, and_false, map_zero, AddMonoidHom.zero_apply]
      simp only [h_term]
  have hSf : ∑ p ∈ (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport h.val) f.prop h.prop d).toFinset, α (f p.1) (h p.2) =
             ∑ p ∈ (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport h.val) f.prop h.prop d).toFinset ∪ (finite_pair_sum_eq (T1 := fnSupport g.val) (T2 := fnSupport h.val) g.prop h.prop d).toFinset,
               α (f p.1) (h p.2) := by
    apply Finset.sum_subset
    · intro p hp; apply Finset.mem_union.mpr; left; exact hp
    · intro p hp hnot
      have h_term : α (f p.1) (h p.2) = 0 := by
        by_contra hne
        rw [Finset.mem_union] at hp
        rcases hp with hsf | hsg
        · contradiction
        · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hsg
          have h0 : f p.1 = 0 := by
            by_contra hne'
            simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hnot
            exact hnot ⟨hsg.1, hne', hsg.2.2⟩
          simp_all only [AddSubgroup.coe_add, Pi.add_apply, ne_eq, map_add, AddMonoidHom.add_apply,
            Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_true_eq_false, not_false_eq_true, and_true, and_false,
            map_zero, AddMonoidHom.zero_apply]
      simp only [h_term]
  have hSg : ∑ p ∈ (finite_pair_sum_eq (T1 := fnSupport g.val) (T2 := fnSupport h.val) g.prop h.prop d).toFinset, α (g p.1) (h p.2) =
             ∑ p ∈ (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport h.val) f.prop h.prop d).toFinset ∪ (finite_pair_sum_eq (T1 := fnSupport g.val) (T2 := fnSupport h.val) g.prop h.prop d).toFinset,
               α (g p.1) (h p.2) := by
    apply Finset.sum_subset
    · intro p hp; apply Finset.mem_union.mpr; right; exact hp
    · intro p hp hnot
      have h_term : α (g p.1) (h p.2) = 0 := by
        by_contra hne
        rw [Finset.mem_union] at hp
        rcases hp with hsf | hsg
        · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hsf
          have h0 : g p.1 = 0 := by
            by_contra hne'
            simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hnot
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

lemma novikovSeriesMul_left_distrib
    (f : NovikovSeries Γ ι A) (g h : NovikovSeries Γ ι B) (α : A →+ B →+ C) :
    novikovSeriesMul f (g + h) α = novikovSeriesMul f g α + novikovSeriesMul f h α := by
  ext d
  simp only [novikovSeriesMul, novikovSeriesMulFun, AddSubgroup.coe_add, Pi.add_apply]
  let Sg := (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop d).toFinset
  let Sh := (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport h.val) f.prop h.prop d).toFinset
  let T := Sg ∪ Sh
  have hS : ∑ p ∈ (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport (g + h).val) f.prop (g + h).prop d).toFinset,
              α (f p.1) (g p.2 + h p.2) =
            ∑ p ∈ T, α (f p.1) (g p.2 + h p.2) := by
    apply Finset.sum_subset
    · intro p hp
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hp
      apply Finset.mem_union.mpr
      have hdisj : g p.2 ≠ 0 ∨ h p.2 ≠ 0 := by
        by_contra h
        simp only [ne_eq, not_or, not_not] at h
        simp_all only [AddSubgroup.coe_add, Pi.add_apply, add_zero, not_true_eq_false, and_false]
      rcases hdisj with h | h
      · left
        simp only [Sg, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]
        exact ⟨hp.1, hp.2.1, h⟩
      · right
        simp only [Sh, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]
        exact ⟨hp.1, hp.2.1, h⟩
    · intro p hp hnot
      have h_term : α (f p.1) (g p.2 + h p.2) = 0 := by
        by_contra hne
        have hp' : p ∈ Sg ∨ p ∈ Sh := Finset.mem_union.mp hp
        rcases hp' with hsg | hsh
        · have hsg' : p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ g p.2 ≠ 0 := by
            simp only [Sg, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hsg
            exact hsg
          have h0 : g p.2 + h p.2 = 0 := by
            by_contra hne'
            simp_all only [ne_eq, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_false_eq_true,
              and_self, true_and, true_or, AddSubgroup.coe_add, Pi.add_apply, not_true_eq_false, T, Sg, Sh]
          simp_all only [ne_eq, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_false_eq_true,
            true_and, true_or, AddSubgroup.coe_add, Pi.add_apply, not_true_eq_false, and_false, map_zero, T,
            Sg, Sh]
        · have hsh' : p.1 + p.2 = d ∧ f p.1 ≠ 0 ∧ h p.2 ≠ 0 := by
            simp only [Sh, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hsh
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
            simp only [Sh, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hsh
            exact hsh
          have h0 : g p.2 = 0 := by
            by_contra hne'
            simp_all only [ne_eq, AddSubgroup.coe_add, Pi.add_apply, Finset.mem_union, Set.Finite.mem_toFinset,
              Set.mem_setOf_eq, not_false_eq_true, and_self, not_true_eq_false, T, Sg, Sh]
          simp_all only [ne_eq, AddSubgroup.coe_add, Pi.add_apply, map_add, Finset.mem_union, Set.Finite.mem_toFinset,
            Set.mem_setOf_eq, not_false_eq_true, not_true_eq_false, and_false, map_zero, T, Sg, Sh]
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
            simp only [Sg, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hsg
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

lemma novikovSeriesMul_comm {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (α : A →+ B →+ C) (α' : B →+ A →+ C)
    (hcomm : ∀ a b, α a b = α' b a) :
    novikovSeriesMul f g α = novikovSeriesMul g f α' := by
  ext d
  simp only [novikovSeriesMul, novikovSeriesMulFun]
  have hswap :
      (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop d).toFinset.image (fun p => (p.2, p.1)) =
      (finite_pair_sum_eq (T1 := fnSupport g.val) (T2 := fnSupport f.val) g.prop f.prop d).toFinset := by
    ext ⟨d1, d2⟩
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq,
      Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨a, b, ⟨hsum, hf, hg⟩, ⟨rfl, rfl⟩⟩
      rw [add_comm] at hsum
      exact ⟨hsum, hg, hf⟩
    · rintro ⟨hsum, hg, hf⟩
      use d2, d1
      rw [add_comm] at hsum
      exact ⟨⟨hsum, hf, hg⟩, rfl, rfl⟩
  rw [← hswap, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p _
    exact hcomm (f p.1) (g p.2)
  · intro p _ q _ h_eq
    simp only [Prod.mk.injEq] at h_eq
    exact Prod.ext h_eq.2 h_eq.1

/-- Naturality of `novikovSeriesMul` in both arguments: applying an
`AddMonoidHom` on the values of `novikovSeriesMul f s α` is the same as
multiplying transformed series `f', s'` under a compatible bilinear
operation `α'`. -/
lemma novikovSeriesMul_map {A' B' C' : Type*}
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (φa : A →+ A') (φb : B →+ B') (φc : C →+ C')
    (α : A →+ B →+ C) (α' : A' →+ B' →+ C')
    (hcompat : ∀ a b, φc (α a b) = α' (φa a) (φb b))
    (f : NovikovSeries Γ ι A) (s : NovikovSeries Γ ι B)
    (f' : NovikovSeries Γ ι A') (s' : NovikovSeries Γ ι B')
    (hf : ∀ d, f'.val d = φa (f.val d))
    (hs : ∀ d, s'.val d = φb (s.val d))
    (d : ι → Γ) :
    φc ((novikovSeriesMul f s α).val d) = (novikovSeriesMul f' s' α').val d := by
  set S : Finset ((ι → Γ) × (ι → Γ)) := (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport s.val) f.prop s.prop d).toFinset with hSdef
  have hLHS : (novikovSeriesMul f s α).val d
      = ∑ p ∈ S, α (f.val p.1) (s.val p.2) := rfl
  have hsub : (finite_pair_sum_eq (T1 := fnSupport f'.val) (T2 := fnSupport s'.val) f'.prop s'.prop d).toFinset ⊆ S := by
    intro p hp
    simp only [Set.Finite.mem_toFinset, hSdef] at hp ⊢
    refine ⟨hp.1, ?_, ?_⟩
    · intro h; apply hp.2.1; rw [hf, h, φa.map_zero]
    · intro h; apply hp.2.2; rw [hs, h, φb.map_zero]
  have hsum_S : ∀ p ∈ S, p.1 + p.2 = d := by
    intro p hp
    simp only [Set.Finite.mem_toFinset, hSdef] at hp
    exact hp.1
  have hRHS : (novikovSeriesMul f' s' α').val d
      = ∑ p ∈ S, α' (f'.val p.1) (s'.val p.2) :=
    novikovSeriesMul_largerSum f' s' α' d S hsub hsum_S
  rw [hLHS, hRHS, map_sum]
  exact Finset.sum_congr rfl fun p _ => by rw [hf, hs, hcompat]

lemma novikovSeriesMul_left_sum_subset {A B C D F : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup F]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (h : NovikovSeries Γ ι C)
    (α : A →+ B →+ D) (β : D →+ C →+ F) (d : ι → Γ) :
    let P := (finite_pair_sum_eq (T1 := fnSupport (novikovSeriesMul f g α).val) (T2 := fnSupport h.val) (novikovSeriesMul f g α).prop h.prop d).toFinset
    let Q := (finite_triple_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) (T3 := fnSupport h.val) f.prop g.prop h.prop d).toFinset.image (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1 + t.2.1, t.2.2))
    ∑ p ∈ P, β ((novikovSeriesMul f g α) p.1) (h p.2) =
    ∑ p ∈ Q, β ((novikovSeriesMul f g α) p.1) (h p.2) := by
  intro P Q
  have hfg_def : ∀ p : ι → Γ, (novikovSeriesMul f g α) p =
      ∑ q ∈ (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop p).toFinset, α (f q.1) (g q.2) := fun _ => rfl
  have hPQ : P ⊆ Q := by
    intro p hp
    simp only [P, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hp
    obtain ⟨hp_sum, hp_fg, hp_h⟩ := hp
    have hFCS_ne : (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop p.1).toFinset.Nonempty := by
      by_contra h_emp
      rw [Finset.not_nonempty_iff_eq_empty] at h_emp
      apply hp_fg
      rw [hfg_def, h_emp, Finset.sum_empty]
    obtain ⟨q, hq⟩ := hFCS_ne
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hq
    obtain ⟨hq_sum, hq_f, hq_g⟩ := hq
    rw [Finset.mem_image]
    refine ⟨(q.1, q.2, p.2), ?_, ?_⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]
      refine ⟨?_, hq_f, hq_g, hp_h⟩
      change q.1 + q.2 + p.2 = d
      rw [hq_sum]; exact hp_sum
    · change (q.1 + q.2, p.2) = p
      rw [hq_sum]
  apply Finset.sum_subset hPQ
  intro q hqQ hqnotP
  rw [Finset.mem_image] at hqQ
  obtain ⟨t, htT, hteq⟩ := hqQ
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at htT
  have hh_q : h q.2 ≠ 0 := by rw [← hteq]; exact htT.2.2.2
  have hsum_q : q.1 + q.2 = d := by
    rw [← hteq]; change t.1 + t.2.1 + t.2.2 = d; exact htT.1
  have hfg_zero : (novikovSeriesMul f g α) q.1 = 0 := by
    by_contra hne
    apply hqnotP
    simp only [P, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]
    exact ⟨hsum_q, hne, hh_q⟩
  rw [hfg_zero, map_zero, AddMonoidHom.zero_apply]

lemma sum_triple_support_left {A B C F : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup F]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (h : NovikovSeries Γ ι C)
    (d : ι → Γ) (W : (ι → Γ) × (ι → Γ) × (ι → Γ) → F) :
    ∑ σ ∈ ((finite_triple_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) (T3 := fnSupport h.val) f.prop g.prop h.prop d).toFinset.image (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1 + t.2.1, t.2.2))).sigma (fun q => (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop q.1).toFinset), W (σ.2.1, σ.2.2, σ.1.2) =
    ∑ t ∈ (finite_triple_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) (T3 := fnSupport h.val) f.prop g.prop h.prop d).toFinset, W t := by
  let T := (finite_triple_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) (T3 := fnSupport h.val) f.prop g.prop h.prop d).toFinset
  let Q := T.image (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1 + t.2.1, t.2.2))
  refine Finset.sum_nbij'
    (i := fun σ => (σ.2.1, σ.2.2, σ.1.2))
    (j := fun t => ⟨(t.1 + t.2.1, t.2.2), (t.1, t.2.1)⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [Finset.mem_sigma] at hσ
    obtain ⟨hq, hpq⟩ := hσ
    rw [Finset.mem_image] at hq
    obtain ⟨t0, ht0T, ht0eq⟩ := hq
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at ht0T
    have hh : h σ.1.2 ≠ 0 := by rw [← ht0eq]; exact ht0T.2.2.2
    have hsum_q : σ.1.1 + σ.1.2 = d := by
      rw [← ht0eq]; change t0.1 + t0.2.1 + t0.2.2 = d; exact ht0T.1
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hpq
    obtain ⟨hpq_sum, hpq_f, hpq_g⟩ := hpq
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]
    refine ⟨?_, hpq_f, hpq_g, hh⟩
    change σ.2.1 + σ.2.2 + σ.1.2 = d
    rw [hpq_sum]; exact hsum_q
  · intro t ht
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at ht
    obtain ⟨ht_sum, ht_f, ht_g, ht_h⟩ := ht
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_image]
      refine ⟨t, ?_, rfl⟩
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]
      exact ⟨ht_sum, ht_f, ht_g, ht_h⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]
      exact ⟨trivial, ht_f, ht_g⟩
  · intro σ hσ
    rw [Finset.mem_sigma] at hσ
    obtain ⟨_, hpq⟩ := hσ
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hpq
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

lemma novikovSeriesMul_right_sum_subset {A B C E F : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [AddCommGroup F]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (h : NovikovSeries Γ ι C)
    (γ : B →+ C →+ E) (δ : A →+ E →+ F) (d : ι → Γ) :
    let P := (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport (novikovSeriesMul g h γ).val) f.prop (novikovSeriesMul g h γ).prop d).toFinset
    let Q := (finite_triple_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) (T3 := fnSupport h.val) f.prop g.prop h.prop d).toFinset.image (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1, t.2.1 + t.2.2))
    ∑ p ∈ P, δ (f p.1) ((novikovSeriesMul g h γ) p.2) =
    ∑ p ∈ Q, δ (f p.1) ((novikovSeriesMul g h γ) p.2) := by
  intro P Q
  have hgh_def : ∀ p : ι → Γ, (novikovSeriesMul g h γ) p =
      ∑ q ∈ (finite_pair_sum_eq (T1 := fnSupport g.val) (T2 := fnSupport h.val) g.prop h.prop p).toFinset, γ (g q.1) (h q.2) := fun _ => rfl
  have hPQ : P ⊆ Q := by
    intro p hp
    simp only [P, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hp
    obtain ⟨hp_sum, hp_f, hp_gh⟩ := hp
    have hFCS_ne : (finite_pair_sum_eq (T1 := fnSupport g.val) (T2 := fnSupport h.val) g.prop h.prop p.2).toFinset.Nonempty := by
      by_contra h_emp
      rw [Finset.not_nonempty_iff_eq_empty] at h_emp
      apply hp_gh
      rw [hgh_def, h_emp, Finset.sum_empty]
    obtain ⟨q, hq⟩ := hFCS_ne
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hq
    obtain ⟨hq_sum, hq_g, hq_h⟩ := hq
    rw [Finset.mem_image]
    refine ⟨(p.1, q.1, q.2), ?_, ?_⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]
      refine ⟨?_, hp_f, hq_g, hq_h⟩
      change p.1 + q.1 + q.2 = d
      rw [add_assoc, hq_sum]; exact hp_sum
    · change (p.1, q.1 + q.2) = p
      rw [hq_sum]
  apply Finset.sum_subset hPQ
  intro q hqQ hqnotP
  rw [Finset.mem_image] at hqQ
  obtain ⟨t, htT, hteq⟩ := hqQ
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at htT
  have hf_q : f q.1 ≠ 0 := by rw [← hteq]; exact htT.2.1
  have hsum_q : q.1 + q.2 = d := by
    rw [← hteq]; change t.1 + (t.2.1 + t.2.2) = d
    rw [← add_assoc]; exact htT.1
  have hgh_zero : (novikovSeriesMul g h γ) q.2 = 0 := by
    by_contra hne
    apply hqnotP
    simp only [P, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]
    exact ⟨hsum_q, hf_q, hne⟩
  rw [hgh_zero, map_zero]

lemma sum_triple_support_right {A B C F : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup F]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (h : NovikovSeries Γ ι C)
    (d : ι → Γ) (W : (ι → Γ) × (ι → Γ) × (ι → Γ) → F) :
    ∑ σ ∈ ((finite_triple_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) (T3 := fnSupport h.val) f.prop g.prop h.prop d).toFinset.image (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1, t.2.1 + t.2.2))).sigma (fun q => (finite_pair_sum_eq (T1 := fnSupport g.val) (T2 := fnSupport h.val) g.prop h.prop q.2).toFinset), W (σ.1.1, σ.2.1, σ.2.2) =
    ∑ t ∈ (finite_triple_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) (T3 := fnSupport h.val) f.prop g.prop h.prop d).toFinset, W t := by
  let T := (finite_triple_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) (T3 := fnSupport h.val) f.prop g.prop h.prop d).toFinset
  let Q := T.image (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1, t.2.1 + t.2.2))
  refine Finset.sum_nbij'
    (i := fun σ => (σ.1.1, σ.2.1, σ.2.2))
    (j := fun t => ⟨(t.1, t.2.1 + t.2.2), (t.2.1, t.2.2)⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [Finset.mem_sigma] at hσ
    obtain ⟨hq, hpq⟩ := hσ
    rw [Finset.mem_image] at hq
    obtain ⟨t0, ht0T, ht0eq⟩ := hq
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at ht0T
    have hf : f σ.1.1 ≠ 0 := by rw [← ht0eq]; exact ht0T.2.1
    have hsum_q : σ.1.1 + σ.1.2 = d := by
      rw [← ht0eq]; change t0.1 + (t0.2.1 + t0.2.2) = d
      rw [← add_assoc]; exact ht0T.1
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hpq
    obtain ⟨hpq_sum, hpq_g, hpq_h⟩ := hpq
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]
    refine ⟨?_, hf, hpq_g, hpq_h⟩
    change σ.1.1 + σ.2.1 + σ.2.2 = d
    rw [add_assoc, hpq_sum]; exact hsum_q
  · intro t ht
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at ht
    obtain ⟨ht_sum, ht_f, ht_g, ht_h⟩ := ht
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_image]
      refine ⟨t, ?_, rfl⟩
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]
      exact ⟨ht_sum, ht_f, ht_g, ht_h⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq]
      exact ⟨trivial, ht_g, ht_h⟩
  · intro σ hσ
    rw [Finset.mem_sigma] at hσ
    obtain ⟨_, hpq⟩ := hσ
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq] at hpq
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

/-- Auxiliary: the iterated product `(f * g) * h` evaluated at `d` rewrites as a sum over the
finite triple support of `(f, g, h)` at `d`. -/
private lemma novikovSeriesMul_left_eq_triple_sum {A B C D F : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup F]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (h : NovikovSeries Γ ι C)
    (α : A →+ B →+ D) (β : D →+ C →+ F) (d : ι → Γ) :
    (novikovSeriesMul (novikovSeriesMul f g α) h β) d =
    ∑ t ∈ (finite_triple_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) (T3 := fnSupport h.val) f.prop g.prop h.prop d).toFinset,
      β (α (f t.1) (g t.2.1)) (h t.2.2) := by
  classical
  let T := (finite_triple_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) (T3 := fnSupport h.val) f.prop g.prop h.prop d).toFinset
  let P := (finite_pair_sum_eq (T1 := fnSupport (novikovSeriesMul f g α).val) (T2 := fnSupport h.val) (novikovSeriesMul f g α).prop h.prop d).toFinset
  let Q := T.image (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1 + t.2.1, t.2.2))
  have h_P_Q : ∑ p ∈ P, β ((novikovSeriesMul f g α) p.1) (h p.2) =
    ∑ p ∈ Q, β ((novikovSeriesMul f g α) p.1) (h p.2) :=
      novikovSeriesMul_left_sum_subset f g h α β d
  change ∑ p ∈ P, β ((novikovSeriesMul f g α) p.1) (h p.2) = _
  rw [h_P_Q]
  have hexp : ∀ q ∈ Q,
      β ((novikovSeriesMul f g α) q.1) (h q.2) =
      ∑ pq ∈ (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop q.1).toFinset,
        β (α (f pq.1) (g pq.2)) (h q.2) := by
    intro q _
    have hfg_def : ∀ p : ι → Γ, (novikovSeriesMul f g α) p =
        ∑ q ∈ (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop p).toFinset, α (f q.1) (g q.2) := fun _ => rfl
    rw [hfg_def]
    have key := map_sum (β.flip (h q.2))
        (fun pq : (ι → Γ) × (ι → Γ) => α (f pq.1) (g pq.2))
        (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop q.1).toFinset
    simp only [AddMonoidHom.flip_apply] at key
    exact key
  rw [Finset.sum_congr rfl hexp]
  rw [← Finset.sum_sigma (s := Q)
      (t := fun q => (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop q.1).toFinset)
      (f := fun σ : (q : (ι → Γ) × (ι → Γ)) × ((ι → Γ) × (ι → Γ)) =>
        β (α (f σ.2.1) (g σ.2.2)) (h σ.1.2))]
  exact sum_triple_support_left f g h d (fun t => β (α (f t.1) (g t.2.1)) (h t.2.2))

/-- Auxiliary: the iterated product `f * (g * h)` evaluated at `d` rewrites as a sum over the
finite triple support of `(f, g, h)` at `d`. -/
private lemma novikovSeriesMul_right_eq_triple_sum {A B C E F : Type*}
    [Fintype ι] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [AddCommGroup F]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (h : NovikovSeries Γ ι C)
    (γ : B →+ C →+ E) (δ : A →+ E →+ F) (d : ι → Γ) :
    (novikovSeriesMul f (novikovSeriesMul g h γ) δ) d =
    ∑ t ∈ (finite_triple_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) (T3 := fnSupport h.val) f.prop g.prop h.prop d).toFinset,
      δ (f t.1) (γ (g t.2.1) (h t.2.2)) := by
  classical
  let T := (finite_triple_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) (T3 := fnSupport h.val) f.prop g.prop h.prop d).toFinset
  let P := (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport (novikovSeriesMul g h γ).val) f.prop (novikovSeriesMul g h γ).prop d).toFinset
  let Q := T.image (fun t : (ι → Γ) × (ι → Γ) × (ι → Γ) => (t.1, t.2.1 + t.2.2))
  have h_P_Q : ∑ p ∈ P, δ (f p.1) ((novikovSeriesMul g h γ) p.2) =
    ∑ p ∈ Q, δ (f p.1) ((novikovSeriesMul g h γ) p.2) :=
      novikovSeriesMul_right_sum_subset f g h γ δ d
  change ∑ p ∈ P, δ (f p.1) ((novikovSeriesMul g h γ) p.2) = _
  rw [h_P_Q]
  have hexp : ∀ q ∈ Q,
      δ (f q.1) ((novikovSeriesMul g h γ) q.2) =
      ∑ pq ∈ (finite_pair_sum_eq (T1 := fnSupport g.val) (T2 := fnSupport h.val) g.prop h.prop q.2).toFinset,
        δ (f q.1) (γ (g pq.1) (h pq.2)) := by
    intro q _
    have hgh_def : ∀ p : ι → Γ, (novikovSeriesMul g h γ) p =
        ∑ q ∈ (finite_pair_sum_eq (T1 := fnSupport g.val) (T2 := fnSupport h.val) g.prop h.prop p).toFinset, γ (g q.1) (h q.2) := fun _ => rfl
    rw [hgh_def]
    exact map_sum (δ (f q.1))
        (fun pq : (ι → Γ) × (ι → Γ) => γ (g pq.1) (h pq.2))
        (finite_pair_sum_eq (T1 := fnSupport g.val) (T2 := fnSupport h.val) g.prop h.prop q.2).toFinset
  rw [Finset.sum_congr rfl hexp]
  rw [← Finset.sum_sigma (s := Q)
      (t := fun q => (finite_pair_sum_eq (T1 := fnSupport g.val) (T2 := fnSupport h.val) g.prop h.prop q.2).toFinset)
      (f := fun σ : (q : (ι → Γ) × (ι → Γ)) × ((ι → Γ) × (ι → Γ)) =>
        δ (f σ.1.1) (γ (g σ.2.1) (h σ.2.2)))]
  exact sum_triple_support_right f g h d (fun t => δ (f t.1) (γ (g t.2.1) (h t.2.2)))

lemma novikovSeriesMul_assoc {A B C D E F : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B) (h : NovikovSeries Γ ι C)
    (α : A →+ B →+ D) (β : D →+ C →+ F) (γ : B →+ C →+ E) (δ : A →+ E →+ F)
    (hass : ∀ (a : A) (b : B) (c : C), β (α a b) c = δ a (γ b c)) :
    novikovSeriesMul (novikovSeriesMul f g α) h β = novikovSeriesMul f (novikovSeriesMul g h γ) δ := by
  ext d
  rw [novikovSeriesMul_left_eq_triple_sum f g h α β d,
      novikovSeriesMul_right_eq_triple_sum f g h γ δ d]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  exact hass _ _ _

lemma novikovSeriesMul_left_monomial
    (a : A) (f : NovikovSeries Γ ι B) (α : A →+ B →+ C) (d e : ι → Γ) : (novikovSeriesMul (novikovMonomial a d) f α) (d + e) = α a (f e) := by
  simp only [novikovSeriesMul, novikovSeriesMulFun]
  set P := (finite_pair_sum_eq (T1 := fnSupport (novikovMonomial a d).val) (T2 := fnSupport f.val) (novikovMonomial a d).prop f.prop (d+e)).toFinset
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
      simp only [Set.Finite.mem_toFinset, Set.notMem_setOf_iff, mem_fnSupport, P] at nel
      push Not at nel
      rw [novikovMonomial] at nel
      simp_all only [ne_eq, ↓reduceIte, not_false_eq_true, map_zero]
    · have : P = {(d, e)} := by simp_all only [Finset.subset_singleton_iff, false_or, P]
      rw [this, Finset.sum_singleton, novikovMonomial]
      simp only [↓reduceIte]

lemma novikovSeriesMul_right_monomial
    (f : NovikovSeries Γ ι A) (b : B) (α : A →+ B →+ C) (d e : ι → Γ) : (novikovSeriesMul f (novikovMonomial b d) α) (e + d) = α (f e) b  := by
  simp only [novikovSeriesMul, novikovSeriesMulFun]
  set P := (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport (novikovMonomial b d).val) f.prop (novikovMonomial b d).prop (e+d)).toFinset
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
      simp only [Set.Finite.mem_toFinset, Set.notMem_setOf_iff, mem_fnSupport, P] at nel
      push Not at nel
      rw [novikovMonomial] at nel
      simp_all only [ne_eq, ↓reduceIte, imp_false, not_not,
        map_zero, AddMonoidHom.zero_apply]
    · have : P = {(e, d)} := by simp_all only [Finset.subset_singleton_iff, false_or, P]
      rw [this, Finset.sum_singleton, novikovMonomial]
      simp only [↓reduceIte]

end Novikov

