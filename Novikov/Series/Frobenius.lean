import Novikov.Series.OneVar
import Novikov.Series.Ring
import Novikov.Series.Exact
import Mathlib.Algebra.Ring.CompTypeclasses

/-!
# Frobenius on Novikov series

This file collects Frobenius endomorphisms on real-exponent Novikov series.

The primary construction is the coordinate Frobenius
`coordinateFrobeniusRingHom`, which scales one chosen exponent coordinate by
`Λ`.  The usual one-variable Frobenius is then the `Unit`-coordinate
specialization `frobeniusRingHom`.

The inverse coordinate map is not part of the public API: use
`coordinateFrobeniusRingHomInv`, which is defined by replacing `Λ` with
`1 / Λ`.
-/

open Novikov
open Topology

namespace Novikov

variable {Λ : ℝ} [hΛ : Fact (Λ > 0)]

section CoordinateFrobenius

/-! ## Coordinate Frobenius -/

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup A]

/-- Scale the `j`-th exponent by `1 / Λ`. This is the coefficient-level
function underlying Frobenius in one coordinate. -/
noncomputable def scaleCoordinate (j : ι) (d : ι → ↥(⊤ : AddSubgroup ℝ)) :
    ι → ↥(⊤ : AddSubgroup ℝ) :=
  fun i => if i = j then ⟨(d i : ℝ) / Λ, AddSubgroup.mem_top _⟩ else d i

/-- Private inverse coordinate operation used in proofs: multiply the `j`-th
exponent by `Λ`. The public inverse Frobenius API is
`coordinateFrobeniusRingHomInv`, defined by replacing `Λ` with `1 / Λ`. -/
private noncomputable def unscaleCoordinate (j : ι) (d : ι → ↥(⊤ : AddSubgroup ℝ)) :
    ι → ↥(⊤ : AddSubgroup ℝ) :=
  fun i => if i = j then ⟨(d i : ℝ) * Λ, AddSubgroup.mem_top _⟩ else d i

omit [Fintype ι] in
@[simp]
private lemma scaleCoordinate_unscaleCoordinate (j : ι) (d : ι → ↥(⊤ : AddSubgroup ℝ)) :
    scaleCoordinate (Λ := Λ) j (unscaleCoordinate (Λ := Λ) j d) = d := by
  have hΛpos' : 0 < Λ := hΛ.out
  ext i
  by_cases hij : i = j
  · simp [scaleCoordinate, unscaleCoordinate, hij, hΛpos'.ne']
  · simp [scaleCoordinate, unscaleCoordinate, hij]

omit [Fintype ι] in
@[simp]
private lemma unscaleCoordinate_scaleCoordinate (j : ι) (d : ι → ↥(⊤ : AddSubgroup ℝ)) :
    unscaleCoordinate (Λ := Λ) j (scaleCoordinate (Λ := Λ) j d) = d := by
  have hΛpos' : 0 < Λ := hΛ.out
  ext i
  by_cases hij : i = j
  · simp [scaleCoordinate, unscaleCoordinate, hij, hΛpos'.ne']
  · simp [scaleCoordinate, unscaleCoordinate, hij]

omit [Fintype ι] in
@[simp]
private lemma scaleCoordinate_one_div (j : ι) (d : ι → ↥(⊤ : AddSubgroup ℝ)) :
    scaleCoordinate (Λ := 1 / Λ) j d = unscaleCoordinate (Λ := Λ) j d := by
  have hΛne : Λ ≠ 0 := hΛ.out.ne'
  ext i
  by_cases hij : i = j
  · simp [scaleCoordinate, unscaleCoordinate, hij]
  · simp [scaleCoordinate, unscaleCoordinate, hij]

omit [Fintype ι] in
/-- Coordinate scaling preserves and reflects the zero exponent vector. -/
lemma scaleCoordinate_eq_zero_iff (j : ι) (d : ι → ↥(⊤ : AddSubgroup ℝ)) :
    scaleCoordinate (Λ := Λ) j d = 0 ↔ d = 0 := by
  constructor
  · intro h
    ext i
    by_cases hij : i = j
    · subst i
      have hreal : (d j : ℝ) / Λ = 0 := by
        have hi := congr_fun h j
        simpa [scaleCoordinate] using Subtype.ext_iff.mp hi
      have hΛpos' : 0 < Λ := hΛ.out
      field_simp [hΛpos'.ne'] at hreal
      simpa using hreal
    · have hreal : (d i : ℝ) = 0 := by
        have hi := congr_fun h i
        simpa [scaleCoordinate, hij] using Subtype.ext_iff.mp hi
      simpa using hreal
  · intro h
    rw [h]
    ext i
    by_cases hij : i = j
    · simp [scaleCoordinate, hij]
    · simp [scaleCoordinate, hij]

/-- The function underlying coordinate Frobenius on multivariable Novikov
series. -/
noncomputable def coordinateFrobeniusFun (j : ι)
    (f : NovikovSeries (⊤ : AddSubgroup ℝ) ι A) :
    (ι → ↥(⊤ : AddSubgroup ℝ)) → A :=
  fun d => f (scaleCoordinate (Λ := Λ) j d)

/-- Coordinate Frobenius preserves the Novikov finiteness condition. -/
lemma isNovikovSeries_coordinateFrobenius (j : ι)
    (f : NovikovSeries (⊤ : AddSubgroup ℝ) ι A) :
    isNovikovSeries (coordinateFrobeniusFun (Λ := Λ) j f) := by
  intro s hs C
  let s' : ι → ℝ := fun i => if i = j then s i * Λ else s i
  have hΛpos' : 0 < Λ := hΛ.out
  have hs' : ∀ i, 0 < s' i := by
    intro i
    by_cases hij : i = j
    · simp only [s', hij, ↓reduceIte]
      exact mul_pos (hs j) hΛpos'
    · simp only [s', hij, ↓reduceIte]
      exact hs i
  let g : (ι → ↥(⊤ : AddSubgroup ℝ)) → (ι → ↥(⊤ : AddSubgroup ℝ)) :=
    scaleCoordinate (Λ := Λ) j
  have hg : Function.Injective g := by
    intro d₁ d₂ h
    ext i
    by_cases hij : i = j
    · subst i
      have hi := congr_fun h j
      simp [g, scaleCoordinate] at hi
      have hΛne : Λ ≠ 0 := hΛpos'.ne'
      field_simp [hΛne] at hi
      exact hi
    · have hi := congr_fun h i
      simp only [g, scaleCoordinate, hij, ↓reduceIte] at hi
      exact Subtype.ext_iff.mp hi
  have hsum (d : ι → ↥(⊤ : AddSubgroup ℝ)) :
      ∑ i, s' i * (g d i : ℝ) = ∑ i, s i * (d i : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : i = j
    · simp [s', g, scaleCoordinate, hij]
      field_simp [hΛpos'.ne']
    · simp [s', g, scaleCoordinate, hij]
  have h_S :
      {d | coordinateFrobeniusFun (Λ := Λ) j f d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C} =
        g ⁻¹' {d | f d ≠ 0 ∧ ∑ i, s' i * (d i : ℝ) < C} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_preimage, coordinateFrobeniusFun, g]
    rw [hsum d]
  change {d | coordinateFrobeniusFun (Λ := Λ) j f d ≠ 0 ∧ ∑ i, s i * (d i : ℝ) < C}.Finite
  rw [h_S]
  exact Set.Finite.preimage (fun _ _ _ _ h => hg h) (f.prop s' hs' C)

/-- Coordinate Frobenius as an additive endomorphism. -/
noncomputable def coordinateFrobeniusAddHom (j : ι) :
    NovikovSeries (⊤ : AddSubgroup ℝ) ι A →+ NovikovSeries (⊤ : AddSubgroup ℝ) ι A where
  toFun f := ⟨coordinateFrobeniusFun (Λ := Λ) j f,
    isNovikovSeries_coordinateFrobenius (Λ := Λ) j f⟩
  map_zero' := by
    ext d
    rfl
  map_add' f g := by
    ext d
    rfl

@[simp]
lemma coordinateFrobeniusAddHom_apply (j : ι)
    (f : NovikovSeries (⊤ : AddSubgroup ℝ) ι A) (d : ι → ↥(⊤ : AddSubgroup ℝ)) :
    coordinateFrobeniusAddHom (Λ := Λ) j f d = f (scaleCoordinate (Λ := Λ) j d) :=
  rfl

/-- Coordinate Frobenius preserves convolution products associated to a bilinear
additive map on coefficients. -/
lemma coordinateFrobenius_mul_bil {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] (j : ι)
    (f : NovikovSeries (⊤ : AddSubgroup ℝ) ι A)
    (g : NovikovSeries (⊤ : AddSubgroup ℝ) ι B) (α : A →+ B →+ C) :
    coordinateFrobeniusAddHom (Λ := Λ) j (novikovSeriesMul f g α) =
      novikovSeriesMul (coordinateFrobeniusAddHom (Λ := Λ) j f)
        (coordinateFrobeniusAddHom (Λ := Λ) j g) α := by
  ext d
  simp only [coordinateFrobeniusAddHom_apply, novikovSeriesMul, novikovSeriesMulFun]
  let h1 := (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val)
    f.prop g.prop (scaleCoordinate (Λ := Λ) j d)).toFinset
  let h2 := (finite_pair_sum_eq
    (T1 := fnSupport (coordinateFrobeniusAddHom (Λ := Λ) j f).val)
    (T2 := fnSupport (coordinateFrobeniusAddHom (Λ := Λ) j g).val)
    (coordinateFrobeniusAddHom (Λ := Λ) j f).prop
    (coordinateFrobeniusAddHom (Λ := Λ) j g).prop d).toFinset
  apply Finset.sum_bij
    (fun p _ => (unscaleCoordinate (Λ := Λ) j p.1, unscaleCoordinate (Λ := Λ) j p.2))
  · intro p hp
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp ⊢
    rcases hp with ⟨h_sum, hf, hg⟩
    refine ⟨?_, ?_, ?_⟩
    · ext i
      by_cases hij : i = j
      · subst i
        simp only [Pi.add_apply, unscaleCoordinate, ↓reduceIte]
        have hreal : (p.1 j : ℝ) + (p.2 j : ℝ) = (d j : ℝ) / Λ := by
          simpa [scaleCoordinate] using coe_add_apply h_sum j
        have hΛpos' : 0 < Λ := hΛ.out
        calc (p.1 j : ℝ) * Λ + (p.2 j : ℝ) * Λ
          _ = ((p.1 j : ℝ) + (p.2 j : ℝ)) * Λ := by ring
          _ = ((d j : ℝ) / Λ) * Λ := by rw [hreal]
          _ = (d j : ℝ) := div_mul_cancel₀ _ hΛpos'.ne'
      · simpa [Pi.add_apply, unscaleCoordinate, scaleCoordinate, hij] using coe_add_apply h_sum i
    · simpa only [coordinateFrobeniusAddHom_apply, scaleCoordinate_unscaleCoordinate] using hf
    · simpa only [coordinateFrobeniusAddHom_apply, scaleCoordinate_unscaleCoordinate] using hg
  · intro p₁ hp₁ p₂ hp₂ h
    simp only [Prod.mk.injEq] at h
    apply Prod.ext
    · have h' := congrArg (scaleCoordinate (Λ := Λ) j) h.1
      simpa only [scaleCoordinate_unscaleCoordinate] using h'
    · have h' := congrArg (scaleCoordinate (Λ := Λ) j) h.2
      simpa only [scaleCoordinate_unscaleCoordinate] using h'
  · intro q hq
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq
    rcases hq with ⟨h_sum, hf, hg⟩
    refine ⟨(scaleCoordinate (Λ := Λ) j q.1, scaleCoordinate (Λ := Λ) j q.2), ?_, ?_⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      refine ⟨?_, ?_, ?_⟩
      · ext i
        by_cases hij : i = j
        · subst i
          simp only [Pi.add_apply, scaleCoordinate, ↓reduceIte]
          have hreal : (q.1 j : ℝ) + (q.2 j : ℝ) = (d j : ℝ) :=
            coe_add_apply h_sum j
          calc (q.1 j : ℝ) / Λ + (q.2 j : ℝ) / Λ
            _ = ((q.1 j : ℝ) + (q.2 j : ℝ)) / Λ := by ring
            _ = (d j : ℝ) / Λ := by rw [hreal]
        · simpa [Pi.add_apply, scaleCoordinate, hij] using coe_add_apply h_sum i
      · simpa only [coordinateFrobeniusAddHom_apply] using hf
      · simpa only [coordinateFrobeniusAddHom_apply] using hg
    · simp only [unscaleCoordinate_scaleCoordinate]
  · intro p hp
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
    simp only [scaleCoordinate_unscaleCoordinate]

section Ring

/-! ## Coordinate Frobenius as a ring endomorphism -/

variable {R : Type*} [CommRing R]

lemma coordinateFrobenius_mul (j : ι)
    (f g : NovikovSeries (⊤ : AddSubgroup ℝ) ι R) :
    coordinateFrobeniusAddHom (Λ := Λ) j (f * g) =
      coordinateFrobeniusAddHom (Λ := Λ) j f * coordinateFrobeniusAddHom (Λ := Λ) j g :=
  coordinateFrobenius_mul_bil (Λ := Λ) j f g AddMonoidHom.mul

/-- Coordinate Frobenius as a ring endomorphism. -/
noncomputable def coordinateFrobeniusRingHom (j : ι) :
    NovikovSeries (⊤ : AddSubgroup ℝ) ι R →+* NovikovSeries (⊤ : AddSubgroup ℝ) ι R :=
  { coordinateFrobeniusAddHom (Λ := Λ) j with
    map_one' := by
      ext d
      change novikovOne (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) (A := R)
          (scaleCoordinate (Λ := Λ) j d) =
        novikovOne (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) (A := R) d
      simp [novikovOne_val, scaleCoordinate_eq_zero_iff]
    map_mul' := coordinateFrobenius_mul (Λ := Λ) j }

@[simp]
lemma coordinateFrobeniusRingHom_apply (j : ι)
    (f : NovikovSeries (⊤ : AddSubgroup ℝ) ι R) (d : ι → ↥(⊤ : AddSubgroup ℝ)) :
    coordinateFrobeniusRingHom (Λ := Λ) j f d = f (scaleCoordinate (Λ := Λ) j d) :=
  rfl

/-- The inverse coordinate Frobenius, obtained by replacing `Λ` with `1 / Λ`. -/
noncomputable def coordinateFrobeniusRingHomInv (j : ι) [Fact (1 / Λ > 0)] :
    NovikovSeries (⊤ : AddSubgroup ℝ) ι R →+* NovikovSeries (⊤ : AddSubgroup ℝ) ι R :=
  coordinateFrobeniusRingHom (Λ := 1 / Λ) (R := R) j

/-- Coordinate Frobenius and its inverse form an inverse pair of ring homomorphisms. -/
noncomputable instance coordinateFrobeniusRingHom_invPair (j : ι) [Fact (1 / Λ > 0)] :
    RingHomInvPair (coordinateFrobeniusRingHom (Λ := Λ) (R := R) j)
      (coordinateFrobeniusRingHomInv (Λ := Λ) (R := R) j) where
  comp_eq := by
    ext f d
    have h : scaleCoordinate (Λ := Λ) j (scaleCoordinate (Λ := 1 / Λ) j d) = d := by
      calc
        scaleCoordinate (Λ := Λ) j (scaleCoordinate (Λ := 1 / Λ) j d) =
            scaleCoordinate (Λ := Λ) j (unscaleCoordinate (Λ := Λ) j d) := by
          rw [scaleCoordinate_one_div (Λ := Λ)]
        _ = d := scaleCoordinate_unscaleCoordinate (Λ := Λ) j d
    change f.val (scaleCoordinate (Λ := Λ) j (scaleCoordinate (Λ := 1 / Λ) j d)) = f.val d
    rw [h]
  comp_eq₂ := by
    ext f d
    have h : scaleCoordinate (Λ := 1 / Λ) j (scaleCoordinate (Λ := Λ) j d) = d := by
      calc
        scaleCoordinate (Λ := 1 / Λ) j (scaleCoordinate (Λ := Λ) j d) =
            unscaleCoordinate (Λ := Λ) j (scaleCoordinate (Λ := Λ) j d) := by
          rw [scaleCoordinate_one_div (Λ := Λ)]
        _ = d := unscaleCoordinate_scaleCoordinate (Λ := Λ) j d
    change f.val (scaleCoordinate (Λ := 1 / Λ) j (scaleCoordinate (Λ := Λ) j d)) = f.val d
    rw [h]

noncomputable instance coordinateFrobeniusRingHom_invPair_symm (j : ι) [Fact (1 / Λ > 0)] :
    RingHomInvPair (coordinateFrobeniusRingHomInv (Λ := Λ) (R := R) j)
      (coordinateFrobeniusRingHom (Λ := Λ) (R := R) j) :=
  RingHomInvPair.symm _ _

end Ring

end CoordinateFrobenius

section OneVariable

/-! ## One-variable Frobenius -/

variable {A : Type*} [AddCommGroup A]

/-- The function underlying the one-variable Frobenius endomorphism. This is the
`Unit`-coordinate specialization of `coordinateFrobeniusFun`. -/
noncomputable def frobeniusFun (Λ : ℝ) [Fact (Λ > 0)] (f : RealNovikovSeries A) :
    (Unit → ↥(⊤ : AddSubgroup ℝ)) → A :=
  coordinateFrobeniusFun (Λ := Λ) () f

/-- The one-variable Frobenius preserves the Novikov finiteness condition. -/
lemma isNovikovSeries_frobenius (f : RealNovikovSeries A) :
    isNovikovSeries (frobeniusFun Λ f) :=
  isNovikovSeries_coordinateFrobenius (Λ := Λ) () f

/-- The Frobenius endomorphism on one-variable real Novikov series. -/
noncomputable def frobenius (Λ : ℝ) [Fact (Λ > 0)] :
    RealNovikovSeries A →+ RealNovikovSeries A :=
  coordinateFrobeniusAddHom (Λ := Λ) ()

@[simp]
lemma frobenius_apply_val (f : RealNovikovSeries A) (d : Unit → ↥(⊤ : AddSubgroup ℝ)) :
    (frobenius Λ f) d = f (fun _ => ⟨(d () : ℝ) / Λ, AddSubgroup.mem_top _⟩) := by
  change f (scaleCoordinate (Λ := Λ) () d) = f (fun _ => ⟨(d () : ℝ) / Λ, AddSubgroup.mem_top _⟩)
  apply congrArg f
  ext x
  cases x
  simp [scaleCoordinate]

lemma frobenius_monomial (a : A) (d : Unit → ↥(⊤ : AddSubgroup ℝ)) :
    frobenius Λ (novikovMonomial a d) =
      novikovMonomial a (fun _ => ⟨(d () : ℝ) * Λ, AddSubgroup.mem_top _⟩) := by
  ext d'
  simp only [frobenius_apply_val, novikovMonomial, Subtype.coe_mk]
  have hΛpos : Λ ≠ 0 := hΛ.out.ne'
  have h_iff : (fun _ => ⟨↑(d' ()) / Λ, AddSubgroup.mem_top _⟩) = d ↔
      d' = fun _ => ⟨↑(d ()) * Λ, AddSubgroup.mem_top _⟩ := by
    constructor
    · intro h
      ext i
      have h1 := congr_fun h i
      rw [Subtype.ext_iff] at h1
      field_simp [hΛpos] at h1 ⊢
      exact h1
    · intro h
      ext i
      rw [h]
      field_simp [hΛpos]
  simp only [h_iff]

/-- The Frobenius endomorphism preserves the degree-0 coefficient. -/
lemma frobenius_apply_zero (f : RealNovikovSeries A) :
    (frobenius Λ f) 0 = f 0 := by
  rw [frobenius_apply_val]
  change f (fun _ => ⟨(0 : ℝ) / Λ, AddSubgroup.mem_top _⟩) =
    f (fun _ => (0 : ↥(⊤ : AddSubgroup ℝ)))
  apply congrArg f
  ext x
  cases x
  simp

/-- Iterating the Frobenius endomorphism preserves the degree-0 coefficient. -/
lemma frobenius_iterate_apply_zero (f : RealNovikovSeries A) (k : ℕ) :
    (frobenius Λ)^[k] f 0 = f 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', frobenius_apply_zero, ih]

/-- The Frobenius endomorphism scales the filtration by `Λ`. -/
lemma frobenius_filtration (f : RealNovikovSeries A) (D : ℝ)
    (hf : f ∈ filtration (⊤ : AddSubgroup ℝ) A D) :
    frobenius Λ f ∈ filtration (⊤ : AddSubgroup ℝ) A (Λ * D) := by
  intro d hd
  rw [frobenius_apply_val]
  apply hf
  have hΛpos : 0 < Λ := hΛ.out
  have : (d () : ℝ) / Λ < D := by
    calc
      (d () : ℝ) / Λ < (Λ * D) / Λ := div_lt_div_of_pos_right hd hΛpos
      _ = D := by field_simp [hΛpos.ne']
  exact this

/-- Iterating the Frobenius `k` times scales the filtration by `Λ^k`. -/
lemma frobenius_iterate_filtration (f : RealNovikovSeries A) (D : ℝ)
    (hf : f ∈ filtration (⊤ : AddSubgroup ℝ) A D) (k : ℕ) :
    (frobenius Λ)^[k] f ∈ filtration (⊤ : AddSubgroup ℝ) A (Λ ^ k * D) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ']
    have hF := frobenius_filtration (Λ := Λ) ((frobenius Λ)^[k] f) (Λ ^ k * D) ih
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using hF

/-- The one-variable Frobenius is continuous for the filtration topology. -/
lemma frobenius_continuous : Continuous (frobenius Λ : RealNovikovSeries A → RealNovikovSeries A) := by
  haveI : IsTopologicalAddGroup (RealNovikovSeries A) := is_topological_add_group
  apply continuous_of_continuousAt_zero
  let FB := filtrationBasis (⊤ : AddSubgroup ℝ) A
  rw [ContinuousAt, map_zero, FB.nhds_zero_hasBasis.tendsto_iff FB.nhds_zero_hasBasis]
  intro V ⟨D, hV⟩
  subst hV
  refine ⟨filtration (⊤ : AddSubgroup ℝ) A (D / Λ), ⟨D / Λ, rfl⟩, ?_⟩
  intro f hf
  have h := frobenius_filtration (Λ := Λ) f (D / Λ) hf
  have hΛpos : Λ ≠ 0 := hΛ.out.ne'
  have h_eq : Λ * (D / Λ) = D := by field_simp [hΛpos]
  rwa [h_eq] at h

variable {B : Type*} [AddCommGroup B]

/-- The one-variable Frobenius commutes with applying an additive map to
coefficients. -/
lemma frobenius_comp_map (g : A →+ B) (f : RealNovikovSeries A) :
    frobenius Λ (Novikov.map g f) = Novikov.map g (frobenius Λ f) := by
  ext d
  simp only [frobenius_apply_val, map_apply]

/-- If `Λ > 1`, the fixed points of the one-variable Frobenius are exactly the
constant Novikov series. -/
lemma frobenius_fixed_points [hΛ1 : Fact (Λ > 1)] (f : RealNovikovSeries A) :
    frobenius Λ f = f ↔ ∃ a : A, f = novikovMonomial a 0 := by
  constructor
  · intro h
    use f 0
    ext d
    by_cases hd : d = 0
    · rw [hd]
      simp [novikovMonomial]
    · have h_eq : ∀ n : ℕ,
          f (fun _ => ⟨(d () : ℝ) / Λ^n, AddSubgroup.mem_top _⟩) = f d := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, ← div_div]
          have h1 : (frobenius Λ f)
              (fun x ↦ ⟨↑(d ()) / Λ ^ n, AddSubgroup.mem_top _⟩) =
              f (fun x ↦ ⟨↑(d ()) / Λ ^ n / Λ, AddSubgroup.mem_top _⟩) := by
            simp [frobenius_apply_val]
          rw [← h1, h]
          exact ih
      let S := { d' | f d' ≠ 0 ∧ (d' () : ℝ) < |(d () : ℝ)| + 1 }
      let s : Unit → ℝ := fun _ => 1
      have hs : ∀ i, 0 < s i := fun _ => zero_lt_one
      have h_sum : ∀ d' : Unit → ↥(⊤ : AddSubgroup ℝ),
          ∑ i, s i * (d' i : ℝ) = (d' () : ℝ) := by
        intro d'
        simp only [Fintype.sum_unique, s, one_mul]
      have h_eqS : S =
          {d' | f d' ≠ 0 ∧ ∑ i, s i * (d' i : ℝ) < |(d () : ℝ)| + 1} := by
        apply Set.ext
        intro d'
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h_sum]
      have hS : S.Finite := by
        rw [h_eqS]
        exact f.prop s hs (|(d () : ℝ)| + 1)
      by_contra h_nz
      simp only [novikovMonomial, hd, ↓reduceIte, ne_eq] at h_nz
      have h_in_S : ∀ n : ℕ,
          (fun _ => ⟨(d () : ℝ) / Λ^n, AddSubgroup.mem_top _⟩) ∈ S := by
        intro n
        rw [h_eqS]
        simp only [Set.mem_setOf_eq, h_sum]
        constructor
        · rw [h_eq]
          exact h_nz
        · have hΛpos : 0 < Λ := hΛ.out
          have hΛn : 1 ≤ Λ^n := by
            apply one_le_pow₀
            have := hΛ1.out; linarith
          have h_abs : |(d () : ℝ) / Λ^n| ≤ |(d () : ℝ)| := by
            rw [abs_div, abs_pow, abs_of_nonneg hΛpos.le]
            exact div_le_self (abs_nonneg _) hΛn
          have h_le := abs_le.1 h_abs
          have := hΛ.out; linarith
      let f_seq : ℕ → (Unit → ↥(⊤ : AddSubgroup ℝ)) :=
        fun n => fun _ => ⟨(d () : ℝ) / Λ^n, AddSubgroup.mem_top _⟩
      have h_inj : Function.Injective f_seq := by
        intro n1 n2 h_seq
        have h_seq1 := congr_fun h_seq ()
        have h1 : (d () : ℝ) / Λ^n1 = (d () : ℝ) / Λ^n2 := Subtype.ext_iff.1 h_seq1
        have h_d0 : (d () : ℝ) ≠ 0 := by
          intro h_d_zero
          apply hd
          ext x
          simp [h_d_zero]
        have hΛpos : 0 < Λ := hΛ.out
        have hΛn1 : Λ^n1 ≠ 0 := pow_ne_zero n1 hΛpos.ne'
        have hΛn2 : Λ^n2 ≠ 0 := pow_ne_zero n2 hΛpos.ne'
        field_simp [hΛn1, hΛn2, h_d0] at h1
        by_contra h_neq
        rcases lt_or_gt_of_ne h_neq with h_lt | h_gt
        · have hΛlt : Λ^n1 < Λ^n2 := pow_lt_pow_right₀ (by have := hΛ1.out; linarith) h_lt
          have := hΛ.out; linarith
        · have hΛlt : Λ^n2 < Λ^n1 := pow_lt_pow_right₀ (by have := hΛ1.out; linarith) h_gt
          have := hΛ.out; linarith
      have h_inf : {d' | d' ∈ Set.range f_seq}.Infinite := Set.infinite_range_of_injective h_inj
      have h_sub : Set.range f_seq ⊆ S := by
        rintro _ ⟨n, rfl⟩
        exact h_in_S n
      exact h_inf (hS.subset h_sub)
  · rintro ⟨a, rfl⟩
    rw [frobenius_monomial]
    congr
    ext i
    simp

/-- The one-variable Frobenius preserves convolution products associated to a
bilinear additive map on coefficients. -/
lemma frobenius_mul_bil {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : RealNovikovSeries A)
    (g : RealNovikovSeries B) (α : A →+ B →+ C) :
    frobenius Λ (novikovSeriesMul f g α) =
      novikovSeriesMul (frobenius Λ f) (frobenius Λ g) α :=
  coordinateFrobenius_mul_bil (Λ := Λ) () f g α

end OneVariable

section OneVariableRing

/-! ## One-variable Frobenius as a ring and algebra endomorphism -/

variable {A : Type*} [CommRing A]

lemma frobenius_mul (f g : RealNovikovSeries A) :
    frobenius Λ (f * g) = frobenius Λ f * frobenius Λ g :=
  frobenius_mul_bil f g AddMonoidHom.mul

/-- The Frobenius ring homomorphism on one-variable real Novikov series, as the
`Unit`-coordinate specialization of `coordinateFrobeniusRingHom`. -/
noncomputable def frobeniusRingHom : RealNovikovSeries A →+* RealNovikovSeries A :=
  coordinateFrobeniusRingHom (Λ := Λ) (R := A) (ι := Unit) ()

/-- The `Unit`-coordinate Frobenius ring homomorphism is the one-variable
Frobenius ring homomorphism. -/
lemma coordinateFrobeniusRingHom_unit_eq :
    coordinateFrobeniusRingHom (Λ := Λ) (R := A) (ι := Unit) () =
      frobeniusRingHom (Λ := Λ) (A := A) :=
  rfl

lemma frobenius_algebraMap (a : A) :
    frobeniusRingHom (Λ := Λ) (algebraMap A (RealNovikovSeries A) a) =
      algebraMap A (RealNovikovSeries A) a := by
  change frobenius Λ (novikovMonomial a 0) = novikovMonomial a 0
  rw [frobenius_monomial]
  congr; ext; simp

/-- The Frobenius ring homomorphism preserves the degree-0 coefficient. -/
lemma frobeniusRingHom_apply_zero (f : RealNovikovSeries A) :
    (frobeniusRingHom (Λ := Λ) (A := A)) f 0 = f 0 :=
  frobenius_apply_zero f

/-- Iterating the Frobenius ring homomorphism preserves the degree-0 coefficient. -/
lemma frobeniusRingHom_iterate_apply_zero (f : RealNovikovSeries A) (k : ℕ) :
    (frobeniusRingHom (Λ := Λ) (A := A))^[k] f 0 = f 0 :=
  frobenius_iterate_apply_zero f k

/-- Iterating the Frobenius ring homomorphism `k` times scales the filtration by `Λ^k`. -/
lemma frobeniusRingHom_iterate_filtration (f : RealNovikovSeries A) (D : ℝ)
    (hf : f ∈ filtration (⊤ : AddSubgroup ℝ) A D) (k : ℕ) :
    (frobeniusRingHom (Λ := Λ) (A := A))^[k] f ∈
      filtration (⊤ : AddSubgroup ℝ) A (Λ ^ k * D) := by
  simpa [frobeniusRingHom, frobenius] using frobenius_iterate_filtration f D hf k

/-- The Frobenius iterated `k` times scales the exponent of a monomial `t^d`
to `t^{Λ^k * d}`. -/
lemma frobenius_iterate_monomial_one (d : ℝ) (k : ℕ) :
    (Novikov.frobenius Λ)^[k]
        (novikovMonomial (1 : A) (fun _ : Unit => ⟨d, AddSubgroup.mem_top _⟩)) =
      novikovMonomial (1 : A) (fun _ : Unit => ⟨Λ ^ k * d, AddSubgroup.mem_top _⟩) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    rw [frobenius_monomial (A := A)]
    rw [ih (d * Λ)]
    congr; ext x; simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]

/-- The Frobenius endomorphism on one-variable real Novikov series as an algebra homomorphism. -/
noncomputable def frobeniusAlgHom : RealNovikovSeries A →ₐ[A] RealNovikovSeries A where
  toRingHom := frobeniusRingHom (Λ := Λ)
  commutes' := frobenius_algebraMap

end OneVariableRing

end Novikov
