
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi

open Finset

namespace Novikov

variable {ι A : Type*} [Fintype ι] [AddCommGroup A]
variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S}

def isNovikovSeries (f : (ι → Γ) → A) : Prop :=
  ∀ (s : ι → ℝ) (_ : ∀ i, 0 < s i) (C : ℝ),
    {d : ι → Γ | f d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C}.Finite

lemma isNovikovSeries_zero : isNovikovSeries (0 : (ι → Γ) → A) := by
  intro s hs C
  have h_sub : {d : ι → Γ | (0 : (ι → Γ) → A) d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} ⊆ ∅ := by
    rintro d ⟨hd, _⟩
    exact hd rfl
  exact Set.Finite.subset Set.finite_empty h_sub

lemma isNovikovSeries_add {f g : (ι → Γ) → A} (hf : isNovikovSeries f) (hg : isNovikovSeries g) :
    isNovikovSeries (f + g) := by
  intro s hs C
  have h_sub : {d | (f + g) d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} ⊆
               {d | f d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} ∪
               {d | g d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} := by
    rintro d ⟨hd, hlt⟩
    by_contra h_union
    rw [Set.mem_union, not_or] at h_union
    have h1 : f d = 0 := by
      by_contra h
      exact h_union.1 ⟨h, hlt⟩
    have h2 : g d = 0 := by
      by_contra h
      exact h_union.2 ⟨h, hlt⟩
    change f d + g d ≠ 0 at hd
    rw [h1, h2, add_zero] at hd
    exact hd rfl
  exact Set.Finite.subset (Set.Finite.union (hf s hs C) (hg s hs C)) h_sub

lemma isNovikovSeries_neg {f : (ι → Γ) → A} (hf : isNovikovSeries f) :
    isNovikovSeries (-f) := by
  intro s hs C
  have h_sub : {d | (-f) d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} ⊆
               {d | f d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} := by
    rintro d ⟨hd, hlt⟩
    refine ⟨?_, hlt⟩
    intro h
    change -f d ≠ 0 at hd
    rw [h, neg_zero] at hd
    exact hd rfl
  exact Set.Finite.subset (hf s hs C) h_sub

def novikovSeriesAddSubgroup {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] (Γ : S) (ι A : Type*) [Fintype ι] [AddCommGroup A] : AddSubgroup ((ι → Γ) → A) where
  carrier := {f | isNovikovSeries f}
  zero_mem' := isNovikovSeries_zero
  add_mem' hf hg := isNovikovSeries_add hf hg
  neg_mem' hf := isNovikovSeries_neg hf

lemma isNovikovSeries_smul {R : Type*} [Semiring R] [Module R A] (r : R) {f : (ι → Γ) → A}
    (hf : isNovikovSeries f) : isNovikovSeries (r • f) := by
  intro s hs C
  have h_sub : {d | (r • f) d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} ⊆
               {d | f d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} := by
    rintro d ⟨hd, hlt⟩
    refine ⟨?_, hlt⟩
    intro h
    simp only [Pi.smul_apply, h, smul_zero, ne_eq, not_true_eq_false] at hd
  exact Set.Finite.subset (hf s hs C) h_sub

abbrev NovikovSeries (Γ : S) (ι A : Type*)
    [Fintype ι] [AddCommGroup A] : Type _ :=
  novikovSeriesAddSubgroup Γ (ι := ι) (A := A)

instance : CoeFun (NovikovSeries Γ ι A) (fun _ => (ι → Γ) → A) := ⟨fun f => f.val⟩

instance : Coe (NovikovSeries Γ ι A) ((ι → Γ) → A) := ⟨fun f => f.val⟩

instance {R : Type*} [Semiring R] [Module R A] : SMul R (NovikovSeries Γ ι A) where
  smul r f := ⟨r • f.val, isNovikovSeries_smul r f.prop⟩

instance {R : Type*} [Semiring R] [Module R A] : Module R (NovikovSeries Γ ι A) where
  one_smul f := Subtype.ext (one_smul R f.val)
  mul_smul r s f := Subtype.ext (mul_smul r s f.val)
  smul_add r f g := Subtype.ext (smul_add r f.val g.val)
  smul_zero r := Subtype.ext (smul_zero r)
  add_smul r s f := Subtype.ext (add_smul r s f.val)
  zero_smul f := Subtype.ext (zero_smul R f.val)

/-- The Novikov finiteness condition for a scalar multiple of a monomial.
Its support is a singleton, which is finite below any cutoff. -/
lemma isNovikov_monomial (a : A) (d0 : ι → Γ) :
    isNovikovSeries (fun d : ι → Γ => if d = d0 then a else 0) := by
  intro s hs C
  have h_sub : {d | (if d = d0 then a else 0) ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} ⊆ {d0} := by
    intro d hd
    simp_all only [ne_eq, ite_eq_right_iff, Classical.not_imp, Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact Set.Finite.subset (Set.finite_singleton d0) h_sub

/-- The monomial `t^d` as a Novikov series. -/
noncomputable def novikovMonomial (a : A) (d0 : ι → Γ) : NovikovSeries Γ ι A :=
  ⟨fun d => if d = d0 then a else 0, isNovikov_monomial a d0⟩

end Novikov
