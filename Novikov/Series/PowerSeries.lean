import Novikov.Series.Field
import Novikov.Series.Frobenius
import Novikov.Series.Module
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Real Novikov power series

This file defines the filtration-zero subring `RealNovikovPowerSeries`, monomial
shifts of its submodules, and the ideal of series supported in strictly positive
degrees. The positive ideal lies in the Jacobson radical by the geometric-series
inverse.
-/

open Finset Topology

namespace Novikov

variable {A : Type*} [CommRing A]

/-- The subring of real Novikov series supported in nonnegative degrees. -/
def RealNovikovPowerSeries (A : Type*) [CommRing A] : Subring (RealNovikovSeries A) where
  carrier := filtration (⊤ : AddSubgroup ℝ) A 0
  zero_mem' := (filtration (⊤ : AddSubgroup ℝ) A 0).zero_mem
  one_mem' := by
    intro d hd
    change (if d = 0 then (1 : A) else 0) = 0
    rw [if_neg]
    intro h
    subst d
    norm_num at hd
  add_mem' := (filtration (⊤ : AddSubgroup ℝ) A 0).add_mem
  neg_mem' := (filtration (⊤ : AddSubgroup ℝ) A 0).neg_mem
  mul_mem' hx hy := filtration_mul_mono (D₁ := 0) (D₂ := 0) (D := 0)
    (by norm_num) hx hy

@[simp]
lemma mem_realNovikovPowerSeries {f : RealNovikovSeries A} :
    f ∈ RealNovikovPowerSeries A ↔
      f ∈ filtration (⊤ : AddSubgroup ℝ) A 0 :=
  Iff.rfl

/-- The scalar monomial `t^d` in the real Novikov ring. -/
noncomputable def realNovikovMonomial (A : Type*) [CommRing A] (d : ℝ) :
    RealNovikovSeries A :=
  novikovMonomial 1 (fun _ : Unit => ⟨d, AddSubgroup.mem_top _⟩)

@[simp]
lemma realNovikovMonomial_zero : realNovikovMonomial A 0 = 1 := by
  rfl

lemma realNovikovMonomial_mul (d e : ℝ) :
    realNovikovMonomial A d * realNovikovMonomial A e =
      realNovikovMonomial A (d + e) := by
  simpa [realNovikovMonomial] using
    novikovSeriesMul_monomial (1 : A) (1 : A) AddMonoidHom.mul
      (fun _ : Unit => ⟨d, AddSubgroup.mem_top _⟩)
      (fun _ : Unit => ⟨e, AddSubgroup.mem_top _⟩)

@[simp]
lemma realNovikovMonomial_neg_mul (d : ℝ) :
    realNovikovMonomial A (-d) * realNovikovMonomial A d = 1 := by
  rw [realNovikovMonomial_mul, neg_add_cancel, realNovikovMonomial_zero]

@[simp]
lemma realNovikovMonomial_mul_neg (d : ℝ) :
    realNovikovMonomial A d * realNovikovMonomial A (-d) = 1 := by
  rw [realNovikovMonomial_mul, add_neg_cancel, realNovikovMonomial_zero]

lemma frobenius_realNovikovMonomial {Λ : ℝ} [Fact (Λ > 0)] (d : ℝ) :
    frobenius Λ (realNovikovMonomial A d) =
      realNovikovMonomial A (Λ * d) := by
  rw [realNovikovMonomial, frobenius_monomial]
  congr 1
  funext i
  apply Subtype.ext
  simp [mul_comm]

namespace RealNovikovPowerSeries

/-- A nonnegative monomial, regarded as a real Novikov power series. -/
noncomputable def monomial (d : ℝ) (hd : 0 ≤ d) : RealNovikovPowerSeries A :=
  ⟨realNovikovMonomial A d, by
    intro e he
    change (if e = (fun _ : Unit => ⟨d, AddSubgroup.mem_top _⟩) then (1 : A) else 0) = 0
    rw [if_neg]
    intro h
    subst e
    simp at he
    linarith⟩

@[simp]
lemma coe_monomial (d : ℝ) (hd : 0 ≤ d) :
    ((monomial (A := A) d hd : RealNovikovPowerSeries A) : RealNovikovSeries A) =
      realNovikovMonomial A d :=
  rfl

end RealNovikovPowerSeries

section ModuleShift

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- Multiplication by `t^d` shifts filtration depth by `d`. -/
lemma realNovikovMonomial_smul_mem_filtration (x : RealNovikovSeries M)
    (d D : ℝ) (hx : x ∈ filtration (⊤ : AddSubgroup ℝ) M D) :
    realNovikovMonomial A d • x ∈
      filtration (⊤ : AddSubgroup ℝ) M (d + D) := by
  intro e he
  let dExp : Unit → (⊤ : AddSubgroup ℝ) :=
    fun _ => ⟨d, AddSubgroup.mem_top _⟩
  let eSub : Unit → (⊤ : AddSubgroup ℝ) :=
    fun _ => ⟨(e () : ℝ) - d, AddSubgroup.mem_top _⟩
  have hsum : dExp + eSub = e := by
    funext i
    rcases i
    apply Subtype.ext
    simp [dExp, eSub]
  have hmul := novikovSeriesMul_left_monomial
    (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
    (a := (1 : A)) (f := x) (α := Novikov.smulAddHom (A := A) (M := M))
    (d := dExp) (e := eSub)
  rw [hsum] at hmul
  change (realNovikovMonomial A d • x).val e = 0
  rw [show (realNovikovMonomial A d • x).val e = x.val eSub by
    change (novikovSeriesMul (novikovMonomial (1 : A) dExp) x
      (Novikov.smulAddHom (A := A) (M := M))).val e = x.val eSub
    simpa [Novikov.smulAddHom, _root_.smulAddHom_apply] using hmul]
  apply hx
  change (e () : ℝ) - d < D
  linarith

/-- A module-valued series lies in filtration `d` iff it is `t^d` times a
series in filtration zero. -/
lemma mem_filtration_iff_exists_realNovikovMonomial_smul
    (x : RealNovikovSeries M) (d : ℝ) :
    x ∈ filtration (⊤ : AddSubgroup ℝ) M d ↔
      ∃ y : RealNovikovSeries M,
        y ∈ filtration (⊤ : AddSubgroup ℝ) M 0 ∧
          x = realNovikovMonomial A d • y := by
  constructor
  · intro hx
    refine ⟨realNovikovMonomial A (-d) • x, ?_, ?_⟩
    · simpa using realNovikovMonomial_smul_mem_filtration
        (A := A) x (-d) d hx
    · rw [smul_smul, realNovikovMonomial_mul_neg, one_smul]
  · rintro ⟨y, hy, rfl⟩
    simpa using realNovikovMonomial_smul_mem_filtration
      (A := A) y d 0 hy

variable {N : Type*} [AddCommGroup N] [Module (RealNovikovSeries A) N]

private noncomputable def realNovikovMonomialLinearMap (d : ℝ) :
    N →ₗ[RealNovikovPowerSeries A] N where
  toFun x := realNovikovMonomial A d • x
  map_add' := smul_add _
  map_smul' p x := by
    change realNovikovMonomial A d • ((p : RealNovikovSeries A) • x) =
      (p : RealNovikovSeries A) • (realNovikovMonomial A d • x)
    rw [smul_smul, smul_smul, mul_comm]

/-- The shift `t^d L` of a power-series submodule inside a Novikov-series
module. -/
noncomputable def _root_.Submodule.realNovikovShift
    (L : Submodule (RealNovikovPowerSeries A) N) (d : ℝ) :
    Submodule (RealNovikovPowerSeries A) N :=
  L.map (realNovikovMonomialLinearMap (A := A) (N := N) d)

lemma _root_.Submodule.mem_realNovikovShift
    {L : Submodule (RealNovikovPowerSeries A) N} {d : ℝ} {x : N} :
    x ∈ L.realNovikovShift d ↔
      ∃ y : N, y ∈ L ∧ realNovikovMonomial A d • y = x :=
  Submodule.mem_map

@[simp]
lemma _root_.Submodule.realNovikovShift_zero
    (L : Submodule (RealNovikovPowerSeries A) N) :
    L.realNovikovShift 0 = L := by
  ext x
  simp only [Submodule.mem_realNovikovShift, realNovikovMonomial_zero, one_smul]
  exact ⟨fun ⟨y, hy, hxy⟩ => hxy ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

lemma _root_.Submodule.realNovikovShift_add
    (L : Submodule (RealNovikovPowerSeries A) N) (d e : ℝ) :
    (L.realNovikovShift d).realNovikovShift e =
      L.realNovikovShift (d + e) := by
  ext x
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y, hy, ?_⟩
    change realNovikovMonomial A (d + e) • y =
      realNovikovMonomial A e • (realNovikovMonomial A d • y)
    rw [smul_smul, mul_comm, realNovikovMonomial_mul]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨realNovikovMonomial A d • y, ⟨y, hy, rfl⟩, ?_⟩
    change realNovikovMonomial A e • (realNovikovMonomial A d • y) =
      realNovikovMonomial A (d + e) • y
    rw [smul_smul, mul_comm, realNovikovMonomial_mul]

lemma _root_.Submodule.realNovikovShift_le
    (L : Submodule (RealNovikovPowerSeries A) N) {d : ℝ} (hd : 0 ≤ d) :
    L.realNovikovShift d ≤ L := by
  rintro x ⟨y, hy, rfl⟩
  let p : RealNovikovPowerSeries A :=
    RealNovikovPowerSeries.monomial (A := A) d hd
  change (p : RealNovikovSeries A) • y ∈ L
  exact L.smul_mem p hy

lemma _root_.Submodule.realNovikovShift_mono
    (L : Submodule (RealNovikovPowerSeries A) N) {d e : ℝ} (hde : d ≤ e) :
    L.realNovikovShift e ≤ L.realNovikovShift d := by
  rintro x ⟨y, hy, rfl⟩
  let p : RealNovikovPowerSeries A :=
    RealNovikovPowerSeries.monomial (A := A) (e - d) (sub_nonneg.mpr hde)
  refine ⟨(p : RealNovikovPowerSeries A) • y, L.smul_mem p hy, ?_⟩
  change realNovikovMonomial A d • ((p : RealNovikovSeries A) • y) =
    realNovikovMonomial A e • y
  rw [show (p : RealNovikovSeries A) = realNovikovMonomial A (e - d) from rfl,
    smul_smul, realNovikovMonomial_mul]
  congr 2
  linarith

lemma _root_.Submodule.mem_realNovikovShift_iff
    (L : Submodule (RealNovikovPowerSeries A) N) (d : ℝ) (x : N) :
    x ∈ L.realNovikovShift d ↔ realNovikovMonomial A (-d) • x ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change realNovikovMonomial A (-d) •
      (realNovikovMonomial A d • y) ∈ L
    simpa [smul_smul] using hy
  · intro hx
    refine ⟨realNovikovMonomial A (-d) • x, hx, ?_⟩
    change realNovikovMonomial A d •
      (realNovikovMonomial A (-d) • x) = x
    simp [smul_smul]

end ModuleShift

/-- The geometric inverse of a positive series is supported in nonnegative
degrees. -/
lemma geometricSeries_mem_filtration_zero (g : RealNovikovSeries A)
    (hg : IsPositive g) :
    geometricSeries g hg ∈ filtration (⊤ : AddSubgroup ℝ) A 0 := by
  have hg0 : g ∈ filtration (⊤ : AddSubgroup ℝ) A 0 := by
    intro d hd
    exact hg d hd.le
  have hpow : ∀ n : ℕ, g ^ n ∈ filtration (⊤ : AddSubgroup ℝ) A 0 := by
    intro n
    induction n with
    | zero => exact (RealNovikovPowerSeries A).one_mem
    | succ n ih =>
      rw [pow_succ]
      exact filtration_mul_mono (D₁ := 0) (D₂ := 0) (D := 0)
        (by norm_num) ih hg0
  haveI : ContinuousAdd (RealNovikovSeries A) :=
    (is_topological_add_group (Γ := (⊤ : AddSubgroup ℝ)) (A := A)).toContinuousAdd
  have hopen :
      IsOpen (filtration (⊤ : AddSubgroup ℝ) A 0 : Set (RealNovikovSeries A)) :=
    (filtration (⊤ : AddSubgroup ℝ) A 0).isOpen_of_mem_nhds
      ((filtrationBasis (⊤ : AddSubgroup ℝ) A).mem_nhds_zero ⟨0, rfl⟩)
  have hclosed :
      IsClosed (filtration (⊤ : AddSubgroup ℝ) A 0 : Set (RealNovikovSeries A)) :=
    (filtration (⊤ : AddSubgroup ℝ) A 0).isClosed_of_isOpen hopen
  apply hclosed.mem_of_tendsto (geometric_summable g hg).tendsto_sum_tsum_nat
  exact Filter.Eventually.of_forall fun n =>
    AddSubgroup.sum_mem _ (fun i _ => hpow i)

namespace RealNovikovPowerSeries

/-- The ideal of real Novikov power series supported in strictly positive
degrees. -/
def positiveIdeal : Ideal (RealNovikovPowerSeries A) where
  carrier := {x | ∃ ε : ℝ, 0 < ε ∧
    (x : RealNovikovSeries A) ∈ filtration (⊤ : AddSubgroup ℝ) A ε}
  zero_mem' := ⟨1, zero_lt_one, (filtration _ _ _).zero_mem⟩
  add_mem' := by
    rintro x y ⟨ε, hε, hx⟩ ⟨δ, hδ, hy⟩
    refine ⟨min ε δ, lt_min hε hδ, ?_⟩
    exact (filtration _ _ _).add_mem
      (filtration_mono (min_le_left ε δ) hx)
      (filtration_mono (min_le_right ε δ) hy)
  smul_mem' := by
    rintro x y ⟨ε, hε, hy⟩
    refine ⟨ε, hε, ?_⟩
    exact filtration_mul_mono (D₁ := 0) (D₂ := ε) (D := ε)
      (by simp) x.property hy

@[simp]
lemma mem_positiveIdeal {x : RealNovikovPowerSeries A} :
    x ∈ positiveIdeal (A := A) ↔
      ∃ ε : ℝ, 0 < ε ∧
        (x : RealNovikovSeries A) ∈ filtration (⊤ : AddSubgroup ℝ) A ε :=
  Iff.rfl

lemma mem_positiveIdeal_iff_isPositive {x : RealNovikovPowerSeries A} :
    x ∈ positiveIdeal (A := A) ↔ IsPositive (x : RealNovikovSeries A) := by
  constructor
  · rintro ⟨ε, hε, hx⟩ d hd
    exact hx d (lt_of_le_of_lt hd hε)
  · intro hx
    by_cases hx0 : (x : RealNovikovSeries A) = 0
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [hx0]
      exact (filtration (⊤ : AddSubgroup ℝ) A 1).zero_mem
    · let ε := (minDegree (x : RealNovikovSeries A) () : ℝ)
      have hε : 0 < ε := support_has_min_pos (x : RealNovikovSeries A) hx0 hx
      refine ⟨ε, hε, ?_⟩
      intro d hd
      by_contra hxd
      have hle := minDegree_le (x : RealNovikovSeries A) hx0 d hxd
      exact (not_lt_of_ge hle) hd

/-- Frobenius minus the identity has strictly positive support on real Novikov
power series. -/
lemma frobenius_sub_self_isPositive {Λ : ℝ} [Fact (Λ > 0)]
    (x : RealNovikovPowerSeries A) :
    IsPositive (frobenius Λ (x : RealNovikovSeries A) -
      (x : RealNovikovSeries A)) := by
  have hF : frobenius Λ (x : RealNovikovSeries A) ∈
      filtration (⊤ : AddSubgroup ℝ) A 0 := by
    have h := frobenius_filtration (Λ := Λ)
      (x : RealNovikovSeries A) 0 x.property
    simpa using h
  have hsub : frobenius Λ (x : RealNovikovSeries A) -
      (x : RealNovikovSeries A) ∈
      filtration (⊤ : AddSubgroup ℝ) A 0 :=
    (filtration (⊤ : AddSubgroup ℝ) A 0).sub_mem hF x.property
  intro d hd
  rcases hd.lt_or_eq with hneg | hzero
  · exact hsub d hneg
  · have hd0 : d = (0 : Unit → (⊤ : AddSubgroup ℝ)) := by
      ext i
      cases i
      simpa using hzero
    subst d
    change (frobenius Λ (x : RealNovikovSeries A)) 0 -
      (x : RealNovikovSeries A) 0 = 0
    rw [frobenius_apply_zero, sub_self]

lemma monomial_mem_positiveIdeal (d : ℝ) (hd : 0 < d) :
    monomial (A := A) d hd.le ∈ positiveIdeal (A := A) := by
  refine ⟨d, hd, ?_⟩
  intro e he
  change (if e = (fun _ : Unit => ⟨d, AddSubgroup.mem_top _⟩) then
    (1 : A) else 0) = 0
  rw [if_neg]
  intro h
  subst e
  simp at he

lemma positiveIdeal_factorization {x : RealNovikovPowerSeries A}
    (hx : x ∈ positiveIdeal (A := A)) :
    ∃ d : ℝ, 0 < d ∧ ∃ y : RealNovikovPowerSeries A,
      (x : RealNovikovSeries A) =
        realNovikovMonomial A d * (y : RealNovikovSeries A) := by
  rcases hx with ⟨d, hd, hx⟩
  obtain ⟨y, hy, hxy⟩ :=
    (mem_filtration_iff_exists_realNovikovMonomial_smul
      (A := A) (M := A) (x : RealNovikovSeries A) d).mp hx
  refine ⟨d, hd, ⟨y, hy⟩, ?_⟩
  simpa [smul_eq_mul] using hxy

/-- The strictly positive ideal lies in the Jacobson radical. -/
theorem positiveIdeal_le_jacobson :
    positiveIdeal (A := A) ≤
      (⊥ : Ideal (RealNovikovPowerSeries A)).jacobson := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  rcases hx with ⟨ε, hε, hx⟩
  let z : RealNovikovSeries A := (x : RealNovikovSeries A) * y
  have hz : z ∈ filtration (⊤ : AddSubgroup ℝ) A ε :=
    filtration_mul_mono (D₁ := ε) (D₂ := 0) (D := ε)
      (by simp) hx y.property
  have hnegpos : IsPositive (-z) := by
    intro d hd
    change -z.val d = 0
    rw [neg_eq_zero]
    exact hz d (lt_of_le_of_lt hd hε)
  let invR : RealNovikovSeries A := geometricSeries (-z) hnegpos
  have hinvR : invR ∈ filtration (⊤ : AddSubgroup ℝ) A 0 :=
    geometricSeries_mem_filtration_zero (-z) hnegpos
  let invP : RealNovikovPowerSeries A := ⟨invR, hinvR⟩
  rw [isUnit_iff_exists]
  refine ⟨invP, ?_, ?_⟩
  · apply Subtype.ext
    change (((x : RealNovikovSeries A) * y + 1) * invR) = 1
    have h := geometricSeries_mul_inv (-z) hnegpos
    simpa [z, invR, add_comm] using h
  · rw [mul_comm]
    apply Subtype.ext
    change (((x : RealNovikovSeries A) * y + 1) * invR) = 1
    have h := geometricSeries_mul_inv (-z) hnegpos
    simpa [z, invR, add_comm] using h

end RealNovikovPowerSeries

section PositiveShift

variable {N : Type*} [AddCommGroup N] [Module (RealNovikovSeries A) N]

lemma _root_.Submodule.realNovikovShift_le_positiveIdeal_smul
    (L : Submodule (RealNovikovPowerSeries A) N) {d : ℝ} (hd : 0 < d) :
    L.realNovikovShift d ≤ RealNovikovPowerSeries.positiveIdeal (A := A) • L := by
  rintro x ⟨y, hy, hxy⟩
  let p : RealNovikovPowerSeries A :=
    RealNovikovPowerSeries.monomial (A := A) d hd.le
  have hp : p ∈ RealNovikovPowerSeries.positiveIdeal (A := A) :=
    RealNovikovPowerSeries.monomial_mem_positiveIdeal d hd
  have hpy : p • y ∈ RealNovikovPowerSeries.positiveIdeal (A := A) • L :=
    Submodule.smul_mem_smul hp hy
  rw [← hxy]
  exact hpy

/-- An element is in the positive-ideal multiple of a power-series submodule
iff it belongs to some strictly positive shift of that submodule. -/
lemma _root_.Submodule.mem_positiveIdeal_smul_iff_exists_realNovikovShift
    (L : Submodule (RealNovikovPowerSeries A) N) (x : N) :
    x ∈ RealNovikovPowerSeries.positiveIdeal (A := A) • L ↔
      ∃ d : ℝ, 0 < d ∧ x ∈ L.realNovikovShift d := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro p hp y hy
      obtain ⟨d, hd, z, hz⟩ :=
        RealNovikovPowerSeries.positiveIdeal_factorization hp
      refine ⟨d, hd, ?_⟩
      rw [Submodule.mem_realNovikovShift]
      refine ⟨z • y, L.smul_mem z hy, ?_⟩
      change realNovikovMonomial A d • ((z : RealNovikovSeries A) • y) =
        (p : RealNovikovSeries A) • y
      rw [smul_smul, hz.symm]
    · intro x y hx hy
      obtain ⟨d, hd, hxd⟩ := hx
      obtain ⟨e, he, hye⟩ := hy
      refine ⟨min d e, lt_min hd he, ?_⟩
      apply (L.realNovikovShift (min d e)).add_mem
      · exact L.realNovikovShift_mono (min_le_left d e) hxd
      · exact L.realNovikovShift_mono (min_le_right d e) hye
  · rintro ⟨d, hd, hx⟩
    exact L.realNovikovShift_le_positiveIdeal_smul hd hx

end PositiveShift

end Novikov
