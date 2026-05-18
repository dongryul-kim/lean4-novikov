import Novikov.Series.Finite
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
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
variable {S : Type*} [SetLike S ℝ] {Γ : S}

section WithAddSubmonoid
variable [AddSubmonoidClass S ℝ]

/-- A function `f : (ι → Γ) → A` is a Novikov series iff its support has the
Novikov finiteness property. -/
def isNovikovSeries (f : (ι → Γ) → A) : Prop := hasNovikovFiniteness (fnSupport f)

end WithAddSubmonoid

/-- The Novikov finiteness condition for a scalar multiple of a monomial.
Its support is a singleton, which is finite below any cutoff. -/
lemma is_novikov_series_monomial (a : A) (d0 : ι → Γ) :
    isNovikovSeries (fun d : ι → Γ => if d = d0 then a else 0) := by
  intro s hs C
  have h_sub : {d | (if d = d0 then a else 0) ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} ⊆ {d0} := by
    intro d hd
    simp_all only [ne_eq, ite_eq_right_iff, Classical.not_imp, Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact Set.Finite.subset (Set.finite_singleton d0) h_sub

lemma is_novikov_series_of_subset {B : Type*} [AddCommGroup B]
    {f : (ι → Γ) → A} {g : (ι → Γ) → B} (hg : isNovikovSeries g)
    (h_sub : ∀ d, f d ≠ 0 → g d ≠ 0) : isNovikovSeries f :=
  hg.subset h_sub

lemma is_novikov_series_zero : isNovikovSeries (0 : (ι → Γ) → A) :=
  hasNovikovFiniteness_empty.subset (fun _ hd => (hd rfl).elim)

lemma is_novikov_series_add {f g : (ι → Γ) → A} (hf : isNovikovSeries f) (hg : isNovikovSeries g) :
    isNovikovSeries (f + g) := by
  refine (hf.union hg).subset (fun d hd => ?_)
  simp only [Set.mem_union, Set.mem_setOf_eq, ne_eq] at hd ⊢
  by_cases hf0 : f d = 0
  · right; intro h; apply hd; rw [Pi.add_apply, hf0, h]; simp
  · left; exact hf0

lemma is_novikov_series_neg {f : (ι → Γ) → A} (hf : isNovikovSeries f) :
    isNovikovSeries (-f) := by
  apply is_novikov_series_of_subset hf
  intro d hd h
  rw [Pi.neg_apply, h, neg_zero] at hd
  exact hd rfl

lemma is_novikov_series_pi {ι' : Type*} {M : ι' → Type*} [∀ j, AddCommGroup (M j)]
    {f : (ι → Γ) → (∀ j, M j)} (hf : isNovikovSeries f) (j : ι') :
    isNovikovSeries (fun d => f d j) := by
  apply is_novikov_series_of_subset hf
  intro d hd h
  rw [h] at hd
  exact hd rfl

lemma is_novikov_series_pi_inv {ι' : Type*} [Fintype ι'] {M : ι' → Type*}
    [∀ j, AddCommGroup (M j)] {f : ∀ j, (ι → Γ) → M j}
    (hf : ∀ j, isNovikovSeries (f j)) :
    isNovikovSeries (fun d j => f j d) := by
  intro s hs C
  let S_j (j : ι') := {d | f j d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C}
  have h_fin : ∀ j, (S_j j).Finite := fun j => hf j s hs C
  have h_sub : {d | (fun d j => f j d) d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} ⊆ ⋃ j ∈ Set.univ, S_j j := by
    rintro d ⟨hd, hlt⟩
    simp only [Set.mem_iUnion, Set.mem_univ, true_and, exists_prop]
    have hex : ∃ j, f j d ≠ 0 := by
      contrapose! hd
      funext j
      exact hd j
    rcases hex with ⟨j, hj⟩
    exact ⟨j, hj, hlt⟩
  exact Set.Finite.subset (Set.Finite.biUnion Set.finite_univ (fun j _ => h_fin j)) h_sub

lemma is_novikov_series_smul {R : Type*} [Semiring R] [Module R A] (r : R) {f : (ι → Γ) → A}
    (hf : isNovikovSeries f) : isNovikovSeries (r • f) :=
  is_novikov_series_of_subset hf (fun d hd h_zero => hd (by simp [h_zero]))

section WithAddSubmonoid
variable [AddSubmonoidClass S ℝ]

def novikovSeriesAddSubgroup {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] (Γ : S) (ι A : Type*) [Fintype ι] [AddCommGroup A] : AddSubgroup ((ι → Γ) → A) where
  carrier := {f | isNovikovSeries f}
  zero_mem' := is_novikov_series_zero
  add_mem' hf hg := is_novikov_series_add hf hg
  neg_mem' hf := is_novikov_series_neg hf

abbrev NovikovSeries (Γ : S) (ι A : Type*)
    [Fintype ι] [AddCommGroup A] : Type _ :=
  novikovSeriesAddSubgroup Γ (ι := ι) (A := A)

instance : CoeFun (NovikovSeries Γ ι A) (fun _ => (ι → Γ) → A) := ⟨fun f => f.val⟩

instance : Coe (NovikovSeries Γ ι A) ((ι → Γ) → A) := ⟨fun f => f.val⟩

@[ext]
lemma NovikovSeries.ext {f g : NovikovSeries Γ ι A} (h : ∀ d, f.val d = g.val d) : f = g :=
  Subtype.ext (funext h)

def NovikovSeries.support (f : NovikovSeries Γ ι A) : Set (ι → Γ) :=
  {d | f d ≠ 0}

lemma NovikovSeries.mem_support (f : NovikovSeries Γ ι A) (d : ι → Γ) :
    d ∈ f.support ↔ f d ≠ 0 := Iff.rfl

instance {R : Type*} [Semiring R] [Module R A] : SMul R (NovikovSeries Γ ι A) where
  smul r f := ⟨r • f.val, is_novikov_series_smul r f.prop⟩

instance {R : Type*} [Semiring R] [Module R A] : Module R (NovikovSeries Γ ι A) where
  one_smul f := Subtype.ext (one_smul R f.val)
  mul_smul r s f := Subtype.ext (mul_smul r s f.val)
  smul_add r f g := Subtype.ext (smul_add r f.val g.val)
  smul_zero r := Subtype.ext (smul_zero r)
  add_smul r s f := Subtype.ext (add_smul r s f.val)
  zero_smul f := Subtype.ext (zero_smul R f.val)

/-- The `A`-scalar action on `NovikovSeries Γ ι M` is coefficient-wise. -/
@[simp]
lemma smul_val_apply {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]
    (a : R) (s : NovikovSeries Γ ι M) (d : ι → Γ) : (a • s).val d = a • s.val d := rfl

/-- The monomial `t^d` as a Novikov series. -/
noncomputable def novikovMonomial (a : A) (d0 : ι → Γ) : NovikovSeries Γ ι A :=
  ⟨fun d => if d = d0 then a else 0, is_novikov_series_monomial a d0⟩

end WithAddSubmonoid

end Novikov
