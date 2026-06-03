import Novikov.Descent.Constant
import Novikov.Descent.FullFaithful
import Novikov.Isocrystal.Field
import Novikov.Isocrystal.Field.Triangular
import Novikov.Series.Module

/-!
# Constant descent is an equivalence over algebraically closed fields

This file formalizes Proposition `Prop:NovDescentForGeomPts`: if `K` is an
algebraically closed field, then the constant-descent functor
`vectToNovikovDescent (⊤ : AddSubgroup ℝ) K` from finite projective `K`-modules
to real Novikov descent data over `K` is an equivalence.

The constant-functor compatibility used here (the natural isomorphism
`vectToNovikovDescent ⊤ K ⋙ descentToIsocrystal K ≅ vectToNovIsoc K`) is
provided by `Novikov.Descent.Constant`; do not reprove it here.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract Matrix
open scoped BigOperators

namespace Novikov.Descent

universe u

variable {Λ : ℝ} [Fact (Λ > 1)]
variable {K : Type u} [Field K]

open NovikovIsocrystal

noncomputable local instance : Algebra K (realC K).R₂ := Novikov.novikovAlgebra

private lemma F2_eigen_coeff (c : K) (x : (realC K).R₂)
    (h : x = (algebraMap K (realC K).R₂ c) * F2 (Λ := Λ) K x)
    (d : Fin 2 → ↥(⊤ : AddSubgroup ℝ)) :
    x.val d = c * x.val (scaleCoordinate (Λ := Λ) (1 : Fin 2) d) := by
  have h' : x = c • (F2 (Λ := Λ) K x) := by
    simpa [Algebra.smul_def] using h
  have hv := congrFun (congrArg Subtype.val h') d
  simpa [F2] using hv

/-- A nonzero `F₂`-eigenvector with constant eigenvalue has no support on
exponents whose second coordinate is nonzero. -/
lemma F2_eigen_vanish_of_second_ne_zero (c : K) (x : (realC K).R₂)
    (h : x = (algebraMap K (realC K).R₂ c) * F2 (Λ := Λ) K x)
    {d : Fin 2 → ↥(⊤ : AddSubgroup ℝ)} (hd1 : d 1 ≠ 0) :
    x.val d = 0 :=
  coordinateFrobenius_vanish_of_scale_preserves_nonzero (Λ := Λ) (1 : Fin 2) x.prop
    (fun d hd => by rw [F2_eigen_coeff (Λ := Λ) c x h d, hd, mul_zero]) hd1

/-- If a nonzero element of `R₂` satisfies `x = c F₂(x)` for a constant unit
`c : Kˣ`, then `c = 1`. -/
lemma F2_eigen_constant_scalar_eq_one (c : Kˣ) (x : (realC K).R₂)
    (hx : x ≠ 0)
    (h : x = (algebraMap K (realC K).R₂ (c : K)) * F2 (Λ := Λ) K x) :
    c = 1 := by
  obtain ⟨d, hd⟩ : ∃ d, x.val d ≠ 0 := by
    by_contra hno
    apply hx
    apply NovikovSeries.ext
    intro d
    by_cases hxd : x.val d = 0
    · exact hxd
    · exact (hno ⟨d, hxd⟩).elim
  have hd1 : d 1 = 0 := by
    by_contra hd1
    exact hd (F2_eigen_vanish_of_second_ne_zero (Λ := Λ) (c : K) x h hd1)
  have hscale : scaleCoordinate (Λ := Λ) (1 : Fin 2) d = d := by
    funext i
    by_cases hi : i = (1 : Fin 2)
    · subst i
      apply Subtype.ext
      have hd1real : (d 1 : ℝ) = 0 := by simpa using congrArg Subtype.val hd1
      simp [scaleCoordinate, hd1real]
    · simp [scaleCoordinate, hi]
  have hc := F2_eigen_coeff (Λ := Λ) (c : K) x h d
  rw [hscale] at hc
  have heq : (c : K) * x.val d = 1 * x.val d := by
    rw [← hc]
    simp
  apply Units.ext
  exact mul_right_cancel₀ hd heq

/-- A nonzero `F₂`-fixed element of `R₂` is a unit: by the `π₁` equalizer it
comes from a nonzero one-variable Novikov series, hence from a unit. -/
lemma F2_fixed_nonzero_isUnit (x : (realC K).R₂) (hx : x ≠ 0)
    (h : F2 (Λ := Λ) K x = x) : IsUnit x := by
  obtain ⟨y, hy⟩ := novikovCosimplicialRing_frobenius_equalizer_π₁ (Λ := Λ) K x h
  have hyne : y ≠ 0 := by
    intro hy0
    apply hx
    rw [hy, hy0, map_zero]
  have hyunit : IsUnit y := by
    change IsUnit (show RealNovikovSeries K from y)
    exact isUnit_iff_ne_zero.mpr hyne
  rw [hy]
  exact hyunit.map (realC K).π₁

/-- Extract the coefficient series in the second variable at first exponent `0`. -/
noncomputable def extract_t_degree_zero (y : (realC K).R₂) : RealNovikovSeries K := by
  let yFun : (Unit → ↥(⊤ : AddSubgroup ℝ)) → K :=
    fun d => y.val (fun i : Fin 2 => if i = 0 then 0 else d ())
  have hy : isNovikovSeries yFun := by
    intro s hs C
    let s₂ : Fin 2 → ℝ := fun i => if i = 0 then 1 else s ()
    have hs₂ : ∀ i, 0 < s₂ i := by
      intro i
      by_cases hi : i = 0
      · simp [s₂, hi]
      · simp [s₂, hi, hs ()]
    let emb : (Unit → ↥(⊤ : AddSubgroup ℝ)) → (Fin 2 → ↥(⊤ : AddSubgroup ℝ)) :=
      fun d i => if i = 0 then 0 else d ()
    have hemb_inj : Function.Injective emb := by
      intro d₁ d₂ hEmb
      ext u
      fin_cases u
      have h1 := congr_fun hEmb 1
      simpa [emb] using h1
    have hfin := Set.Finite.preimage (fun _ _ _ _ hEmb => hemb_inj hEmb) (y.prop s₂ hs₂ C)
    refine hfin.subset ?_
    intro d hd
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    simp only [Set.mem_setOf_eq] at hd
    refine ⟨hd.1, ?_⟩
    have hsum : ∑ i, s₂ i * (emb d i : ℝ) = ∑ i, s i * (d i : ℝ) := by
      simp [s₂, emb]
    rw [hsum]
    exact hd.2
  exact ⟨yFun, hy⟩

@[simp] lemma extract_t_degree_zero_apply (y : (realC K).R₂)
    (d : Unit → ↥(⊤ : AddSubgroup ℝ)) :
    extract_t_degree_zero y d = y.val (fun i : Fin 2 => if i = 0 then 0 else d ()) := rfl

@[simp] lemma extract_t_degree_zero_add (x y : (realC K).R₂) :
    extract_t_degree_zero (x + y) = extract_t_degree_zero x + extract_t_degree_zero y := by
  ext d
  rfl

@[simp] lemma extract_t_degree_zero_zero :
    extract_t_degree_zero (0 : (realC K).R₂) = 0 := by
  ext d
  rfl

lemma extract_t_degree_zero_sum {ι : Type*} (s : Finset ι) (f : ι → (realC K).R₂) :
    extract_t_degree_zero (Finset.sum s f) =
      Finset.sum s (fun i => extract_t_degree_zero (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih => simp [has, ih]

@[simp] lemma extract_t_degree_zero_π₂ (a : RealNovikovSeries K) :
    extract_t_degree_zero ((realC K).π₂ a) = a := by
  ext d
  simp [extract_t_degree_zero, novikovCosimplicialRing_π₂_apply]

set_option linter.flexible false in
set_option linter.unnecessarySeqFocus false in
/-- Extraction at first exponent `0` is linear for multiplication by a `π₂`-pulled
one-variable series. -/
lemma extract_t_degree_zero_π₂_mul (a : RealNovikovSeries K) (y : (realC K).R₂) :
    extract_t_degree_zero ((realC K).π₂ a * y) = a * extract_t_degree_zero y := by
  apply NovikovSeries.ext
  intro d
  let sl : Fin 2 → ↥(⊤ : AddSubgroup ℝ) := fun i => if i = 0 then 0 else d ()
  let emb : (Unit → ↥(⊤ : AddSubgroup ℝ)) → (Fin 2 → ↥(⊤ : AddSubgroup ℝ)) :=
    fun v i => if i = 0 then 0 else v ()
  change (((realC K).π₂ a * y).val sl) = (a * extract_t_degree_zero y).val d
  have hmul : Novikov.novikovMulFun ((realC K).π₂ a) y sl =
      Novikov.novikovMulFun a (extract_t_degree_zero y) d := by
    unfold Novikov.novikovMulFun
    let S2 : Finset (((Fin 2 → ↥(⊤ : AddSubgroup ℝ)) × (Fin 2 → ↥(⊤ : AddSubgroup ℝ)))) :=
      (finite_pair_sum_eq (T1 := fnSupport ((realC K).π₂ a).val) (T2 := fnSupport y.val)
        ((realC K).π₂ a).prop y.prop sl).toFinset
    let S1 : Finset (((Unit → ↥(⊤ : AddSubgroup ℝ)) × (Unit → ↥(⊤ : AddSubgroup ℝ)))) :=
      (finite_pair_sum_eq (T1 := fnSupport a.val) (T2 := fnSupport (extract_t_degree_zero y).val)
        a.prop (extract_t_degree_zero y).prop d).toFinset
    change Finset.sum S2 (fun p => ((realC K).π₂ a).val p.1 * y.val p.2) =
      Finset.sum S1 (fun q => a.val q.1 * (extract_t_degree_zero y).val q.2)
    -- `π₂ a` is supported on first exponent `0`, and `sl` has first exponent `0`,
    -- so both factors of every contributing pair vanish in their first coordinate.
    have hzero : ∀ p ∈ S2, p.1 0 = 0 ∧ p.2 0 = 0 := by
      intro p hp
      simp only [S2, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
      obtain ⟨hsum, hp1, _⟩ := hp
      have h10 : p.1 0 = 0 := by
        rw [novikovCosimplicialRing_π₂_apply] at hp1
        by_contra hne; simp [hne] at hp1
      refine ⟨h10, ?_⟩
      have h0 := congrFun hsum 0
      simp [sl, h10] at h0
      exact h0
    have hp2emb : ∀ p ∈ S2, p.2 = emb (fun _ => p.2 1) := by
      intro p hp
      obtain ⟨_, h20⟩ := hzero p hp
      funext i; fin_cases i <;> simp [emb, h20]
    refine Finset.sum_bij (fun p _ => (fun _ : Unit => p.1 1, fun _ : Unit => p.2 1))
      ?hmem ?hinj ?hsurj ?hval
    · intro p hp
      obtain ⟨hp10, _⟩ := hzero p hp
      have hp2e := hp2emb p hp
      simp only [S2, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
      obtain ⟨hsum, hp1, hp2⟩ := hp
      simp only [S1, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      refine ⟨?_, ?_, ?_⟩
      · ext u
        fin_cases u
        have h1 := congrFun hsum 1
        simp [sl] at h1
        simpa using congrArg Subtype.val h1
      · rw [novikovCosimplicialRing_π₂_apply] at hp1
        simpa [hp10] using hp1
      · change y.val (emb (fun _ : Unit => p.2 1)) ≠ 0
        rw [← hp2e]; exact hp2
    · intro p1 hp1mem p2 hp2mem hq
      simp only [Prod.mk.injEq] at hq
      obtain ⟨hq1, hq2⟩ := hq
      obtain ⟨h110, h120⟩ := hzero p1 hp1mem
      obtain ⟨h210, h220⟩ := hzero p2 hp2mem
      ext i <;> fin_cases i
      · simpa using congrArg Subtype.val (h110.trans h210.symm)
      · simpa using congrArg Subtype.val (congrFun hq1 ())
      · simpa using congrArg Subtype.val (h120.trans h220.symm)
      · simpa using congrArg Subtype.val (congrFun hq2 ())
    · intro q hq
      refine ⟨(emb q.1, emb q.2), ?_, ?_⟩
      · simp only [S2, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        simp only [S1, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq
        obtain ⟨hsum, hq1, hq2⟩ := hq
        refine ⟨?_, ?_, ?_⟩
        · ext i <;> fin_cases i <;> simp [sl, emb]
          have h := congrFun hsum ()
          simpa using congrArg Subtype.val h
        · rw [novikovCosimplicialRing_π₂_apply]
          simp [emb, hq1]
        · show y.val (emb q.2) ≠ 0
          simpa [emb] using hq2
      · simp [emb]
    · intro p hp
      obtain ⟨hp10, _⟩ := hzero p hp
      rw [novikovCosimplicialRing_π₂_apply]
      simp [hp10]
      rw [show y.val p.2 = (extract_t_degree_zero y).val (fun _ : Unit => p.2 1) from
        congrArg y.val (hp2emb p hp)]
      exact Or.inl rfl
  exact (Novikov.novikovMul_val ((realC K).π₂ a) y sl).trans
    (hmul.trans (Novikov.novikovMul_val a (extract_t_degree_zero y) d).symm)

/-- Extraction commutes with the second-coordinate Frobenius. -/
lemma extract_t_degree_zero_F2 (y : (realC K).R₂) :
    extract_t_degree_zero (F2 (Λ := Λ) K y) =
      frobeniusRingHom (Λ := Λ) (A := K) (extract_t_degree_zero y) := by
  ext d
  change (F2 (Λ := Λ) K y).val (fun i : Fin 2 => if i = 0 then 0 else d ()) =
    (frobeniusRingHom (Λ := Λ) (A := K) (extract_t_degree_zero y)).val d
  change y.val (scaleCoordinate (Λ := Λ) (1 : Fin 2) (fun i : Fin 2 => if i = 0 then 0 else d ())) =
    y.val (fun i : Fin 2 => if i = 0 then 0 else ⟨(d () : ℝ) / Λ, AddSubgroup.mem_top _⟩)
  apply congrArg y.val
  funext i
  fin_cases i <;> simp [scaleCoordinate]

/-- Extracting first-coordinate degree `0` from a finite matrix equation over
`R₂` yields the corresponding one-variable Frobenius matrix equation. -/
lemma extract_t_degree_zero_matrix_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (RealNovikovSeries K))
    (C : Fin n → RealNovikovSeries K)
    (z : Fin n → (realC K).R₂)
    (h : ∀ i, z i = (∑ j, (realC K).π₂ (A i j) * F2 (Λ := Λ) K (z j)) +
      (realC K).π₂ (C i)) :
    let Z : Fin n → RealNovikovSeries K := fun j => extract_t_degree_zero (z j)
    ∀ i, Z i = (∑ j, A i j * frobeniusRingHom (Λ := Λ) (A := K) (Z j)) + C i := by
  intro Z i
  dsimp [Z]
  calc
    extract_t_degree_zero (z i)
        = extract_t_degree_zero ((∑ j, (realC K).π₂ (A i j) * F2 (Λ := Λ) K (z j)) +
            (realC K).π₂ (C i)) := by rw [h i]
    _ = (∑ j, extract_t_degree_zero ((realC K).π₂ (A i j) * F2 (Λ := Λ) K (z j))) +
        extract_t_degree_zero ((realC K).π₂ (C i)) := by
      rw [extract_t_degree_zero_add, extract_t_degree_zero_sum]
    _ = (∑ j, A i j * frobeniusRingHom (Λ := Λ) (A := K) (extract_t_degree_zero (z j))) +
        C i := by
      simp [extract_t_degree_zero_π₂_mul, extract_t_degree_zero_F2]

/-- Generalized normalized-extension extraction.  If a nonzero last coordinate
is `F₂`-fixed and the upper block satisfies `x = A F₂(x) + C F₂(xᵢ)`, then
dividing by the last coordinate and extracting first-degree zero produces a
one-variable solution of `Z = A F(Z) + C`. -/
lemma generalized_extension_extract {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (RealNovikovSeries K))
    (C : Fin n → RealNovikovSeries K)
    (xi : (realC K).R₂) (xj : Fin n → (realC K).R₂)
    (hxi_ne : xi ≠ 0) (hxi : F2 (Λ := Λ) K xi = xi)
    (hxj : ∀ i, xj i = (∑ j, (realC K).π₂ (A i j) * F2 (Λ := Λ) K (xj j)) +
      (realC K).π₂ (C i) * F2 (Λ := Λ) K xi) :
    ∃ Z : Fin n → RealNovikovSeries K,
      ∀ i, Z i = (∑ j, A i j * frobeniusRingHom (Λ := Λ) (A := K) (Z j)) + C i := by
  obtain ⟨u, hu⟩ := F2_fixed_nonzero_isUnit (Λ := Λ) xi hxi_ne hxi
  have hFu : F2 (Λ := Λ) K (u : (realC K).R₂) = (u : (realC K).R₂) := by
    simpa [hu] using hxi
  have hFinv : F2 (Λ := Λ) K (↑(u⁻¹) : (realC K).R₂) = (↑(u⁻¹) : (realC K).R₂) := by
    let f := (F2 (Λ := Λ) K).toMonoidWithZeroHom.toMonoidHom
    have hmapu : Units.map f u = u := Units.ext (by simpa [f] using hFu)
    simpa [f] using congrArg
      (fun w : (realC K).R₂ˣ => ((w⁻¹ : (realC K).R₂ˣ) : (realC K).R₂)) hmapu
  let z : Fin n → (realC K).R₂ := fun i => xj i * (↑(u⁻¹) : (realC K).R₂)
  have hz : ∀ i, z i = (∑ j, (realC K).π₂ (A i j) * F2 (Λ := Λ) K (z j)) +
      (realC K).π₂ (C i) := by
    intro i
    dsimp [z]
    calc
      xj i * (↑(u⁻¹) : (realC K).R₂)
          = ((∑ j, (realC K).π₂ (A i j) * F2 (Λ := Λ) K (xj j)) +
              (realC K).π₂ (C i) * F2 (Λ := Λ) K xi) * (↑(u⁻¹) : (realC K).R₂) := by
            rw [hxj i]
      _ = (∑ j, (realC K).π₂ (A i j) * (F2 (Λ := Λ) K (xj j) * (↑(u⁻¹) : (realC K).R₂))) +
            (realC K).π₂ (C i) := by
            rw [add_mul, Finset.sum_mul]
            simp [hFu, ← hu, mul_assoc]
      _ = (∑ j, (realC K).π₂ (A i j) * F2 (Λ := Λ) K (xj j * (↑(u⁻¹) : (realC K).R₂))) +
            (realC K).π₂ (C i) := by
            refine congrArg (fun s => s + (realC K).π₂ (C i)) ?_
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [map_mul, hFinv]
  exact ⟨fun j => extract_t_degree_zero (z j),
    extract_t_degree_zero_matrix_eq (Λ := Λ) A C z hz⟩

/-- The shear `(v, r) ↦ (v + Z r, r)` used to split a rank-one extension block. -/
noncomputable def blockShear {n : ℕ} (Z : Fin n → RealNovikovSeries K) :
    ((Fin n → RealNovikovSeries K) × RealNovikovSeries K) ≃ₗ[RealNovikovSeries K]
      ((Fin n → RealNovikovSeries K) × RealNovikovSeries K) where
  toFun p := (fun i => p.1 i + Z i * p.2, p.2)
  invFun p := (fun i => p.1 i - Z i * p.2, p.2)
  left_inv p := by
    ext i <;> simp
  right_inv p := by
    ext i <;> simp
  map_add' p q := by
    apply Prod.ext
    · funext i
      change p.1 i + q.1 i + Z i * (p.2 + q.2) =
        (p.1 i + Z i * p.2) + (q.1 i + Z i * q.2)
      ring
    · rfl
  map_smul' r p := by
    apply Prod.ext
    · funext i
      change r * p.1 i + Z i * (r * p.2) = r * (p.1 i + Z i * p.2)
      ring
    · rfl

/-- The block Frobenius with arbitrary upper-left matrix `A` and extension
column `C`. -/
noncomputable def blockFrobeniusGeneral {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (RealNovikovSeries K)) (C : Fin n → RealNovikovSeries K) :
    ((Fin n → RealNovikovSeries K) × RealNovikovSeries K) →
      ((Fin n → RealNovikovSeries K) × RealNovikovSeries K) :=
  fun p => (A *ᵥ (fun i => frobeniusRingHom (Λ := Λ) (A := K) (p.1 i)) +
      fun i => C i * frobeniusRingHom (Λ := Λ) (A := K) p.2,
    frobeniusRingHom (Λ := Λ) (A := K) p.2)

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
/-- A shear by a solution of `Z = A F(Z) + C` kills the extension column of the
block Frobenius with upper-left block `A`. -/
lemma blockShear_conjugates_general {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (RealNovikovSeries K))
    (C Z : Fin n → RealNovikovSeries K)
    (hZ : ∀ i, Z i = (∑ j, A i j * frobeniusRingHom (Λ := Λ) (A := K) (Z j)) + C i)
    (p : (Fin n → RealNovikovSeries K) × RealNovikovSeries K) :
    (blockShear Z).symm (blockFrobeniusGeneral (Λ := Λ) A C ((blockShear Z) p)) =
      (A *ᵥ (fun i => frobeniusRingHom (Λ := Λ) (A := K) (p.1 i)),
        frobeniusRingHom (Λ := Λ) (A := K) p.2) := by
  apply Prod.ext
  · funext i
    simp [blockFrobeniusGeneral, blockShear, Matrix.mulVec, dotProduct, map_add, map_mul,
      Finset.sum_add_distrib]
    rw [hZ i]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    ring_nf
  · simp [blockFrobeniusGeneral, blockShear]

/-- Coordinates for the constant isocrystal attached to the free `K`-module
`Fin n → K`. -/
noncomputable def constPiLinearEquiv (n : ℕ) :
    ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := K)).obj
      ({ M := Fin n → K } : FiniteProjectiveModule K)).M ≃ₗ[RealNovikovSeries K]
      (Fin n → RealNovikovSeries K) :=
  (Novikov.novikovBaseChangeEquivPi (Γ := (⊤ : AddSubgroup ℝ)) (A := K)
      (ι := Unit) (ι' := Fin n)).trans
    (Novikov.novikovPiEquiv (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (A := K) (M := K))

/-- On pure tensors, `constPiLinearEquiv` is the expected coordinate map. -/
lemma constPiLinearEquiv_tmul_apply (n : ℕ) (r : RealNovikovSeries K) (v : Fin n → K)
    (i : Fin n) (d : Unit → ↥(⊤ : AddSubgroup ℝ)) :
    (constPiLinearEquiv (Λ := Λ) (K := K) n (r ⊗ₜ[K] v) i) d = v i * r d := by
  change ((Novikov.novikovPiEquiv (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (A := K) (M := K))
    ((Novikov.novikovBaseChangeEquivPi (Γ := (⊤ : AddSubgroup ℝ)) (A := K) (ι := Unit) (ι' := Fin n))
      (r ⊗ₜ[K] v)) i) d = v i * r d
  have hbc := LinearMap.congr_fun
    (Novikov.novikovBaseChangeMap_eq_equivPi (Γ := (⊤ : AddSubgroup ℝ)) (A := K)
      (ι := Unit) (ι' := Fin n)).symm (r ⊗ₜ[K] v)
  have h1 : ((Novikov.novikovPiEquiv (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (A := K) (M := K))
      ((Novikov.novikovBaseChangeEquivPi (Γ := (⊤ : AddSubgroup ℝ)) (A := K) (ι := Unit) (ι' := Fin n))
        (r ⊗ₜ[K] v)) i) =
      ((Novikov.novikovPiEquiv (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (A := K) (M := K))
      ((Novikov.novikovBaseChangeMap (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (A := K) (M := Fin n → K))
        (r ⊗ₜ[K] v)) i) := by
    exact congrFun (congrArg (fun s =>
      (Novikov.novikovPiEquiv (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) (A := K) (M := K)) s) hbc) i
  rw [h1]
  rw [Novikov.novikovBaseChangeMap_tmul]
  change (Novikov.novikovSeriesMul r
      (Novikov.novikovMonomial v (0 : Unit → ↥(⊤ : AddSubgroup ℝ))) Novikov.smulAddHom d) i =
      v i * r d
  have hright := Novikov.novikovSeriesMul_right_monomial r v Novikov.smulAddHom
    (0 : Unit → ↥(⊤ : AddSubgroup ℝ)) d
  simp only [add_zero] at hright
  have hi := congrFun hright i
  simpa [Novikov.smulAddHom, mul_comm] using hi

/-- `constPiLinearEquiv` identifies the Frobenius on the constant free
isocrystal with coordinatewise one-variable Frobenius. -/
lemma constPiLinearEquiv_commute_frobenius (n : ℕ)
    (x : ((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := K)).obj
      ({ M := Fin n → K } : FiniteProjectiveModule K)).M) :
    constPiLinearEquiv (Λ := Λ) (K := K) n
      (((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := K)).obj
        ({ M := Fin n → K } : FiniteProjectiveModule K)).F_M x) =
      fun i => frobeniusRingHom (Λ := Λ) (A := K)
        ((constPiLinearEquiv (Λ := Λ) (K := K) n x) i) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      ext i d
      rfl
  | add x y hx hy =>
      rw [show (((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := K)).obj
        ({ M := Fin n → K } : FiniteProjectiveModule K)).F_M (x + y)) =
        (((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := K)).obj
          ({ M := Fin n → K } : FiniteProjectiveModule K)).F_M x) +
        (((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := K)).obj
          ({ M := Fin n → K } : FiniteProjectiveModule K)).F_M y) by
          exact map_add (((NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := K)).obj
            ({ M := Fin n → K } : FiniteProjectiveModule K)).F_M) x y]
      rw [(constPiLinearEquiv (Λ := Λ) (K := K) n).map_add]
      rw [hx, hy]
      funext i
      change frobeniusRingHom (Λ := Λ) (A := K) ((constPiLinearEquiv (Λ := Λ) (K := K) n x) i) +
          frobeniusRingHom (Λ := Λ) (A := K) ((constPiLinearEquiv (Λ := Λ) (K := K) n y) i) =
        frobeniusRingHom (Λ := Λ) (A := K) ((constPiLinearEquiv (Λ := Λ) (K := K) n (x + y)) i)
      rw [show (constPiLinearEquiv (Λ := Λ) (K := K) n (x + y)) i =
          (constPiLinearEquiv (Λ := Λ) (K := K) n x) i +
            (constPiLinearEquiv (Λ := Λ) (K := K) n y) i by
        exact congrFun ((constPiLinearEquiv (Λ := Λ) (K := K) n).map_add x y) i]
      rw [map_add]
  | tmul r v =>
      change constPiLinearEquiv (Λ := Λ) (K := K) n
          (frobeniusRingHom (Λ := Λ) (A := K) r ⊗ₜ[K] v) =
        fun i => frobeniusRingHom (Λ := Λ) (A := K)
          ((constPiLinearEquiv (Λ := Λ) (K := K) n (r ⊗ₜ[K] v)) i)
      ext i d
      rw [constPiLinearEquiv_tmul_apply (Λ := Λ) n]
      change v i * (frobeniusRingHom (Λ := Λ) (A := K) r) d =
        (frobeniusRingHom (Λ := Λ) (A := K)
          ((constPiLinearEquiv (Λ := Λ) (K := K) n (r ⊗ₜ[K] v)) i)) d
      simp only [frobeniusRingHom, coordinateFrobeniusRingHom_apply]
      rw [constPiLinearEquiv_tmul_apply (Λ := Λ) n r v i (scaleCoordinate (Λ := Λ) () d)]

/-- The standard linear equivalence between an `n`-block plus one last coordinate
and functions on `Fin (n+1)`, implemented using `Fin.snoc`. -/
noncomputable def finSnocLinearEquiv (n : ℕ) :
    ((Fin n → RealNovikovSeries K) × RealNovikovSeries K) ≃ₗ[RealNovikovSeries K]
      (Fin (n+1) → RealNovikovSeries K) where
  toFun p := Fin.snoc p.1 p.2
  invFun f := (fun i => f i.castSucc, f (Fin.last n))
  left_inv p := by
    ext i <;> simp
  right_inv f := by
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp
  map_add' p q := by
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp
  map_smul' r p := by
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp

/-- `finSnocLinearEquiv` commutes with coordinatewise Frobenius. -/
lemma finSnocLinearEquiv_frobenius {n : ℕ}
    (p : (Fin n → RealNovikovSeries K) × RealNovikovSeries K) :
    finSnocLinearEquiv (K := K) n
      ((fun i => frobeniusRingHom (Λ := Λ) (A := K) (p.1 i)),
        frobeniusRingHom (Λ := Λ) (A := K) p.2) =
      fun i => frobeniusRingHom (Λ := Λ) (A := K) ((finSnocLinearEquiv (K := K) n p) i) := by
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp [finSnocLinearEquiv]

/-- In `Fin.snoc` block coordinates, multiplying by a block matrix is
`blockFrobeniusGeneral`. -/
lemma finSnocLinearEquiv_blockFrobeniusGeneral {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (RealNovikovSeries K))
    (A : Matrix (Fin n) (Fin n) (RealNovikovSeries K))
    (C : Fin n → RealNovikovSeries K)
    (hblock : ∀ i j : Fin n, T i.castSucc j.castSucc = A i j)
    (hcol : ∀ i : Fin n, T i.castSucc (Fin.last n) = C i)
    (hlastrow : ∀ j : Fin n, T (Fin.last n) j.castSucc = 0)
    (hlastdiag : T (Fin.last n) (Fin.last n) = 1)
    (v : Fin (n + 1) → RealNovikovSeries K) :
    (finSnocLinearEquiv (K := K) n).symm
      (T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (v j))) =
    blockFrobeniusGeneral (Λ := Λ) A C ((finSnocLinearEquiv (K := K) n).symm v) := by
  apply Prod.ext
  · funext i
    change (T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (v j))) i.castSucc =
      (blockFrobeniusGeneral (Λ := Λ) A C ((finSnocLinearEquiv (K := K) n).symm v)).1 i
    rw [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_castSucc]
    simp [finSnocLinearEquiv, blockFrobeniusGeneral, hblock, hcol, Matrix.mulVec, dotProduct]
  · change (T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (v j))) (Fin.last n) =
      (blockFrobeniusGeneral (Λ := Λ) A C ((finSnocLinearEquiv (K := K) n).symm v)).2
    rw [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_castSucc]
    have hsum0 : (∑ x : Fin n,
        T (Fin.last n) x.castSucc * frobeniusRingHom (Λ := Λ) (A := K) (v x.castSucc)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp [hlastrow]
    rw [hsum0]
    simp [finSnocLinearEquiv, blockFrobeniusGeneral, hlastdiag]

/-- If coordinates conjugate the Frobenius matrix to the identity Frobenius,
package the coordinate change as an isomorphism to the constant free
isocrystal. -/
noncomputable def coordinateIsoToConst {n : ℕ} (I : NovikovIsocrystal (Λ := Λ) K)
    (e : I.M ≃ₗ[RealNovikovSeries K] (Fin n → RealNovikovSeries K))
    (T : Matrix (Fin n) (Fin n) (RealNovikovSeries K))
    (B : (Fin n → RealNovikovSeries K) ≃ₗ[RealNovikovSeries K] (Fin n → RealNovikovSeries K))
    (hB : ∀ v, B (T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (v j))) =
      fun i => frobeniusRingHom (Λ := Λ) (A := K) (B v i))
    (hF : ∀ x, e (I.F_M x) = T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (e x j))) :
    I ≅ (NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := K)).obj
      ({ M := Fin n → K } : FiniteProjectiveModule K) := by
  let P : FiniteProjectiveModule K := { M := Fin n → K }
  let J := (NovikovIsocrystal.vectToNovIsoc (Λ := Λ) (A := K)).obj P
  let Lcoord : I.M ≃ₗ[RealNovikovSeries K] (Fin n → RealNovikovSeries K) := e.trans B
  let L : I.M ≃ₗ[RealNovikovSeries K] J.M :=
    Lcoord.trans (constPiLinearEquiv (Λ := Λ) (K := K) n).symm
  have hLcoord : ∀ x, Lcoord (I.F_M x) = fun i => frobeniusRingHom (Λ := Λ) (A := K) (Lcoord x i) := by
    intro x
    dsimp [Lcoord]
    rw [hF x]
    exact hB (e x)
  have hL : ∀ x, J.F_M (L x) = L (I.F_M x) := by
    intro x
    apply (constPiLinearEquiv (Λ := Λ) (K := K) n).injective
    rw [constPiLinearEquiv_commute_frobenius (Λ := Λ) n (L x)]
    change (fun i => frobeniusRingHom (Λ := Λ) (A := K)
        ((constPiLinearEquiv (Λ := Λ) (K := K) n (L x)) i)) =
      constPiLinearEquiv (Λ := Λ) (K := K) n (L (I.F_M x))
    dsimp [L]
    simp only [LinearEquiv.apply_symm_apply]
    exact (hLcoord x).symm
  refine
    { hom := { toLinearMap := L.toLinearMap, commute_frobenius := hL }
      inv := { toLinearMap := L.symm.toLinearMap, commute_frobenius := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro y
    apply L.injective
    calc
      L (I.F_M (L.symm y)) = J.F_M (L (L.symm y)) := (hL (L.symm y)).symm
      _ = J.F_M y := by rw [LinearEquiv.apply_symm_apply]
      _ = L (L.symm (J.F_M y)) := (LinearEquiv.apply_symm_apply L (J.F_M y)).symm
  · apply NovikovIsocrystal.hom_ext
    ext x
    exact L.symm_apply_apply x
  · apply NovikovIsocrystal.hom_ext
    ext x
    exact L.apply_symm_apply x

/-- Last-row coordinate extraction for an upper-triangular matrix.  If `T` is
upper triangular, the last coordinate of `(T.map π₂) *ᵥ y` only sees the last
 diagonal entry. -/
lemma upper_triangular_last_coordinate {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (realC K).R₁)
    (htri : ∀ i j, j < i → T i j = 0)
    (y : Fin (n + 1) → (realC K).R₂) :
    ((T.map (realC K).π₂) *ᵥ y) (Fin.last n) =
      (realC K).π₂ (T (Fin.last n) (Fin.last n)) * y (Fin.last n) := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro j _ hj
    have hjlt : j < Fin.last n := Fin.lt_last_iff_ne_last.mpr hj
    rw [Matrix.map_apply, htri (Fin.last n) j hjlt]
    have h0 : (realC K).π₂ (0 : (realC K).R₁) = 0 := map_zero (realC K).π₂
    rw [h0, zero_mul]
  · intro hlast
    exact (hlast (Finset.mem_univ _)).elim

/-- Compatibility of the two-variable Frobenius `F₂` with the second face
`π₂ : R₁ → R₂`. -/
lemma F2_π₂_apply_eq (r : (realC K).R₁) :
    F2 (Λ := Λ) K ((realC K).π₂ r) =
      (realC K).π₂ (frobeniusRingHom (Λ := Λ) (A := K) r) :=
  congrFun (congrArg DFunLike.coe (F2_comp_π₂_eq (Λ := Λ) K)) r

/-- The second face sends a constant one-variable Novikov series to the same
constant two-variable Novikov series. -/
lemma π₂_algebraMap (a : K) :
    (realC K).π₂ (algebraMap K (RealNovikovSeries K) a) =
      algebraMap K (realC K).R₂ a := by
  change substituteRingHom (Γ := (⊤ : AddSubgroup ℝ)) (A := K) (fun _ : Unit => (1 : Fin 2))
      (Novikov.algebraMapNovikov a : RealNovikovSeries K) =
    (Novikov.algebraMapNovikov a : (realC K).R₂)
  change substitute (Γ := (⊤ : AddSubgroup ℝ)) (fun _ : Unit => (1 : Fin 2))
      (Novikov.algebraMapNovikov a : RealNovikovSeries K) =
    (Novikov.algebraMapNovikov a : (realC K).R₂)
  rw [substitute_algebraMap]

noncomputable local instance : Algebra (realC K).R₁ (realC K).R₂ := (realC K).π₂.toAlgebra

/-- Coordinate equivalence for the `π₂`-base change of a finite free
`R₁`-module. -/
noncomputable def pi2CoordLinearEquiv (n : ℕ) :
    π₂s (realC K) (Fin n → (realC K).R₁) ≃ₗ[(realC K).R₂]
      (Fin n → (realC K).R₂) := by
  letI : Algebra (realC K).R₁ (realC K).R₂ := (realC K).π₂.toAlgebra
  exact TensorProduct.piScalarRight (realC K).R₁ ((realC K).R₂) ((realC K).R₂) (Fin n)

/-- On pure tensors, `pi2CoordLinearEquiv` is the standard coordinate map. -/
lemma pi2CoordLinearEquiv_tmul (n : ℕ) (s : (realC K).R₂)
    (v : Fin n → (realC K).R₁) :
    pi2CoordLinearEquiv (K := K) n (s ⊗ₜ[(realC K).R₁] v) = fun i => v i • s := by
  ext i
  simp [pi2CoordLinearEquiv, TensorProduct.piScalarRightHom_tmul]

/-- Coordinate equivalence on `π₂^* M` induced by triangular coordinates on `M`. -/
noncomputable def pi2TriangularLinearEquiv {n : ℕ}
    (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) K)
    (e : M.M ≃ₗ[(realC K).R₁] (Fin n → (realC K).R₁)) :
    π₂s (realC K) M.M ≃ₗ[(realC K).R₂] (Fin n → (realC K).R₂) :=
  (LinearEquiv.baseChange (realC K).R₁ (realC K).R₂ M.M (Fin n → (realC K).R₁) e).trans
    (pi2CoordLinearEquiv (K := K) n)

/-- Coordinates on `π₂^* M` induced by triangular coordinates on `M`. -/
noncomputable def pi2TriangularCoords {n : ℕ} (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) K)
    (e : M.M ≃ₗ[(realC K).R₁] (Fin n → (realC K).R₁)) :
    π₂s (realC K) M.M →ₗ[(realC K).R₂] (Fin n → (realC K).R₂) :=
  (pi2TriangularLinearEquiv (K := K) M e).toLinearMap

/-- Pure-tensor form of the coordinate equation for `FM2` under triangular
coordinates. -/
lemma pi2TriangularCoords_FM2_tmul {n : ℕ} (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) K)
    (e : M.M ≃ₗ[(realC K).R₁] (Fin n → (realC K).R₁))
    (T : Matrix (Fin n) (Fin n) (realC K).R₁)
    (hF : ∀ m, e (descentFrobeniusToFun (Λ := Λ) K M m) =
      T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (e m j)))
    (s : (realC K).R₂) (m : M.M) :
    pi2TriangularCoords M e (FM2 (Λ := Λ) K M (s ⊗ₜ[(realC K).R₁] m)) =
      (T.map (realC K).π₂) *ᵥ
        (fun j => F2 (Λ := Λ) K (pi2TriangularCoords M e (s ⊗ₜ[(realC K).R₁] m) j)) := by
  rw [FM2_tmulπ₂]
  change pi2CoordLinearEquiv (K := K) n
      (baseChangeMap (realC K).π₂ e.toLinearMap
        ((F2 (Λ := Λ) K s) ⊗ₜ[(realC K).R₁] descentFrobeniusToFun (Λ := Λ) K M m)) = _
  rw [baseChangeMap_tmul]
  rw [pi2CoordLinearEquiv_tmul]
  have hcoord : ∀ j,
      pi2TriangularCoords M e (s ⊗ₜ[(realC K).R₁] m) j =
        (realC K).π₂ (e m j) * s := by
    intro j
    change (pi2CoordLinearEquiv (K := K) n
      (baseChangeMap (realC K).π₂ e.toLinearMap (s ⊗ₜ[(realC K).R₁] m))) j =
        (realC K).π₂ (e m j) * s
    rw [baseChangeMap_tmul]
    rw [pi2CoordLinearEquiv_tmul]
    change e m j • s = (realC K).π₂ (e m j) * s
    rw [Algebra.smul_def]
    rfl
  ext i
  change e (descentFrobeniusToFun (Λ := Λ) K M m) i • F2 (Λ := Λ) K s =
    ((T.map (realC K).π₂) *ᵥ fun j =>
      F2 (Λ := Λ) K (pi2TriangularCoords M e (s ⊗ₜ[(realC K).R₁] m) j)) i
  rw [congrFun (hF m) i]
  rw [show (fun j => F2 (Λ := Λ) K
        (pi2TriangularCoords M e (s ⊗ₜ[(realC K).R₁] m) j)) =
      (fun j => F2 (Λ := Λ) K ((realC K).π₂ (e m j) * s)) by
    funext j
    rw [hcoord j]]
  change (realC K).π₂ ((T *ᵥ fun j => frobeniusRingHom (Λ := Λ) (A := K) (e m j)) i) *
      F2 (Λ := Λ) K s =
    ((T.map (realC K).π₂) *ᵥ fun j =>
      F2 (Λ := Λ) K ((realC K).π₂ (e m j) * s)) i
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  simp only [Matrix.map_apply]
  rw [map_sum]
  simp only [map_mul, F2_π₂_apply_eq]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Coordinate equation for `FM2` under triangular coordinates. -/
lemma pi2TriangularCoords_FM2 {n : ℕ} (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) K)
    (e : M.M ≃ₗ[(realC K).R₁] (Fin n → (realC K).R₁))
    (T : Matrix (Fin n) (Fin n) (realC K).R₁)
    (hF : ∀ m, e (descentFrobeniusToFun (Λ := Λ) K M m) =
      T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (e m j)))
    (x : π₂s (realC K) M.M) :
    pi2TriangularCoords M e (FM2 (Λ := Λ) K M x) =
      (T.map (realC K).π₂) *ᵥ
        (fun j => F2 (Λ := Λ) K (pi2TriangularCoords M e x j)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      ext i
      simp [pi2TriangularCoords, Matrix.mulVec, dotProduct]
  | tmul s m =>
      exact pi2TriangularCoords_FM2_tmul (Λ := Λ) M e T hF s m
  | add x y hx hy =>
      ext i
      rw [map_add, map_add]
      rw [hx, hy]
      simp only [Pi.add_apply, map_add]
      rw [Matrix.mulVec, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, dotProduct]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Applying triangular coordinates to the recovered top-row fixed element gives
 the matrix fixed-point equation over `R₂`. -/
lemma recoverTop_coordinate_fixed_equation {n : ℕ}
    (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) K)
    (e : M.M ≃ₗ[(realC K).R₁] (Fin n → (realC K).R₁))
    (T : Matrix (Fin n) (Fin n) (realC K).R₁)
    (hF : ∀ m, e (descentFrobeniusToFun (Λ := Λ) K M m) =
      T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (e m j)))
    (m : M.M) :
    let y := pi2TriangularCoords (K := K) M e (recoverTopMap K M m)
    y = (T.map (realC K).π₂) *ᵥ (fun j => F2 (Λ := Λ) K (y j)) := by
  intro y
  have hfix := recoverTopMap_mem_equalizer (Λ := Λ) K M m
  have hcoord := congrArg (pi2TriangularCoords (K := K) M e) hfix
  rw [pi2TriangularCoords_FM2 (Λ := Λ) M e T hF] at hcoord
  exact hcoord.symm

/-- A matrix Frobenius has enough fixed vectors if every linear functional
vanishing on all fixed solutions is zero.  This is the coordinate form of the
fact that the recovered top-row fixed elements span after `π₁`-base change. -/
def matrixFixedSpans {n : ℕ} (T : Matrix (Fin n) (Fin n) (realC K).R₁) : Prop :=
  ∀ l : (Fin n → (realC K).R₂) →ₗ[(realC K).R₂] (realC K).R₂,
    (∀ y : Fin n → (realC K).R₂,
      y = (T.map (realC K).π₂) *ᵥ (fun j => F2 (Λ := Λ) K (y j)) → l y = 0) →
    l = 0

/-- The fixed solutions coming from a Novikov descent datum span in triangular
coordinates. -/
lemma matrixFixedSpans_of_descent {n : ℕ}
    (M : NovikovDescentDatum (⊤ : AddSubgroup ℝ) K)
    (e : M.M ≃ₗ[(realC K).R₁] (Fin n → (realC K).R₁))
    (T : Matrix (Fin n) (Fin n) (realC K).R₁)
    (hF : ∀ m, e (descentFrobeniusToFun (Λ := Λ) K M m) =
      T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (e m j))) :
    matrixFixedSpans (Λ := Λ) (K := K) T := by
  intro l hl
  letI : Algebra (realC K).R₁ (realC K).R₂ := (realC K).π₁.toAlgebra
  let L : π₁s (realC K) M.M ≃ₗ[(realC K).R₂] (Fin n → (realC K).R₂) :=
    M.φ.trans (pi2TriangularLinearEquiv (K := K) M e)
  have hcomp : l.comp L.toLinearMap =
      (0 : π₁s (realC K) M.M →ₗ[(realC K).R₂] (realC K).R₂) := by
    apply baseChange_linearMap_ext
    intro m
    change l (L ((1 : (realC K).R₂) ⊗ₜ[(realC K).R₁] m)) = 0
    change l (pi2TriangularCoords (K := K) M e (recoverTopMap K M m)) = 0
    exact hl _ (recoverTop_coordinate_fixed_equation (Λ := Λ) M e T hF m)
  apply LinearMap.ext
  intro y
  have hy := LinearMap.congr_fun hcomp (L.symm y)
  simpa using hy

/-- If fixed solutions span, then in each coordinate there is some fixed solution
with nonzero value in that coordinate. -/
lemma matrixFixedSpans_exists_fixed_coord_ne_zero {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (realC K).R₁)
    (hspan : matrixFixedSpans (Λ := Λ) (K := K) T) (k : Fin n) :
    ∃ y : Fin n → (realC K).R₂,
      y = (T.map (realC K).π₂) *ᵥ (fun j => F2 (Λ := Λ) K (y j)) ∧ y k ≠ 0 := by
  by_contra hno
  push Not at hno
  have hproj : (LinearMap.proj k : (Fin n → (realC K).R₂) →ₗ[(realC K).R₂]
      (realC K).R₂) = 0 := by
    apply hspan
    intro y hy
    exact hno y hy
  have hval := LinearMap.congr_fun hproj (Pi.single k (1 : (realC K).R₂))
  have h1 : (1 : (realC K).R₂) = 0 := by simpa using hval
  have hv := congrFun (congrArg Subtype.val h1) (0 : Fin 2 → ↥(⊤ : AddSubgroup ℝ))
  change (Novikov.novikovOne : (realC K).R₂).val (0 : Fin 2 → ↥(⊤ : AddSubgroup ℝ)) =
      (0 : K) at hv
  simp [Novikov.novikovOne, Novikov.novikovMonomial] at hv

/-- For an upper-triangular matrix with constant diagonal and spanning fixed
solutions, the last diagonal scalar is `1`. -/
lemma matrixFixedSpans_last_scalar_eq_one {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (realC K).R₁)
    (c : Fin (n + 1) → Kˣ)
    (hspan : matrixFixedSpans (Λ := Λ) (K := K) T)
    (htri : ∀ i j, j < i → T i j = 0)
    (hdiag : ∀ i, T i i = algebraMap K (RealNovikovSeries K) ((c i : K))) :
    c (Fin.last n) = 1 := by
  obtain ⟨y, hfix, hyne⟩ :=
    matrixFixedSpans_exists_fixed_coord_ne_zero (Λ := Λ) (K := K) T hspan (Fin.last n)
  have hlast := congrFun hfix (Fin.last n)
  rw [upper_triangular_last_coordinate T htri] at hlast
  have hdiaglast := hdiag (Fin.last n)
  have hπdiag := π₂_algebraMap (K := K) (c (Fin.last n) : K)
  have heigen : y (Fin.last n) =
      (algebraMap K (realC K).R₂ (c (Fin.last n) : K)) *
        F2 (Λ := Λ) K (y (Fin.last n)) := by
    simpa [hdiaglast, hπdiag] using hlast
  exact F2_eigen_constant_scalar_eq_one (Λ := Λ) (c (Fin.last n)) (y (Fin.last n)) hyne heigen

/-- If a block matrix has upper-left block `A` and extension column `C`, then a
fixed vector satisfies the corresponding block row equations. -/
lemma block_row_fixed_equation_general {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (realC K).R₁)
    (A : Matrix (Fin n) (Fin n) (RealNovikovSeries K))
    (C : Fin n → RealNovikovSeries K)
    (hblock : ∀ i j : Fin n, T i.castSucc j.castSucc = A i j)
    (hcol : ∀ i : Fin n, T i.castSucc (Fin.last n) = C i)
    (y : Fin (n + 1) → (realC K).R₂)
    (hfixed : y = (T.map (realC K).π₂) *ᵥ (fun j => F2 (Λ := Λ) K (y j)))
    (i : Fin n) :
    y i.castSucc = (∑ x : Fin n,
      (realC K).π₂ (A i x) * F2 (Λ := Λ) K (y x.castSucc)) +
      (realC K).π₂ (C i) * F2 (Λ := Λ) K (y (Fin.last n)) := by
  calc
    y i.castSucc = ((T.map (realC K).π₂) *ᵥ (fun j => F2 (Λ := Λ) K (y j))) i.castSucc :=
      congrFun hfixed i.castSucc
    _ = ∑ j, (T.map (realC K).π₂) i.castSucc j * F2 (Λ := Λ) K (y j) := by
      rw [Matrix.mulVec, dotProduct]
    _ = (∑ x : Fin n,
        (T.map (realC K).π₂) i.castSucc x.castSucc * F2 (Λ := Λ) K (y x.castSucc)) +
        (T.map (realC K).π₂) i.castSucc (Fin.last n) * F2 (Λ := Λ) K (y (Fin.last n)) := by
      rw [Fin.sum_univ_castSucc]
    _ = (∑ x : Fin n,
        (realC K).π₂ (A i x) * F2 (Λ := Λ) K (y x.castSucc)) +
        (realC K).π₂ (C i) * F2 (Λ := Λ) K (y (Fin.last n)) := by
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro x hx
        simp [Matrix.map_apply, hblock]
      · simp [Matrix.map_apply, hcol]

/-- After shearing by a solution of `Z = A F(Z) + C`, the top coordinates of a
fixed vector for a block matrix with upper-left block `A` and extension column
`C` are fixed for the upper-left block. -/
lemma top_unshear_fixed {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (realC K).R₁)
    (A : Matrix (Fin n) (Fin n) (RealNovikovSeries K))
    (C Z : Fin n → RealNovikovSeries K)
    (hblock : ∀ i j : Fin n, T i.castSucc j.castSucc = A i j)
    (hcol : ∀ i : Fin n, T i.castSucc (Fin.last n) = C i)
    (hlastrow : ∀ j : Fin n, T (Fin.last n) j.castSucc = 0)
    (hlastdiag : T (Fin.last n) (Fin.last n) = 1)
    (hZ : ∀ i, Z i = (∑ j, A i j * frobeniusRingHom (Λ := Λ) (A := K) (Z j)) + C i)
    (y : Fin (n + 1) → (realC K).R₂)
    (hy : y = (T.map (realC K).π₂) *ᵥ (fun j => F2 (Λ := Λ) K (y j))) :
    let u : Fin n → (realC K).R₂ := fun i => y i.castSucc - (realC K).π₂ (Z i) * y (Fin.last n)
    u = (A.map (realC K).π₂) *ᵥ (fun j => F2 (Λ := Λ) K (u j)) := by
  intro u
  have htop : ∀ i : Fin n, y i.castSucc =
      (∑ j, (realC K).π₂ (A i j) * F2 (Λ := Λ) K (y j.castSucc)) +
        (realC K).π₂ (C i) * F2 (Λ := Λ) K (y (Fin.last n)) := by
    intro i
    exact block_row_fixed_equation_general (Λ := Λ) T A C hblock hcol y hy i
  have hlast : y (Fin.last n) = F2 (Λ := Λ) K (y (Fin.last n)) := by
    have h := congrFun hy (Fin.last n)
    rw [Matrix.mulVec, dotProduct] at h
    rw [Fin.sum_univ_castSucc] at h
    have hsum0 : (∑ x : Fin n,
        (T.map (realC K).π₂) (Fin.last n) x.castSucc * F2 (Λ := Λ) K (y x.castSucc)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp [Matrix.map_apply, hlastrow]
    rw [hsum0] at h
    rw [Matrix.map_apply, hlastdiag] at h
    simpa using h
  ext i
  dsimp [u]
  rw [Matrix.mulVec, dotProduct]
  rw [htop i]
  have hFsub (j : Fin n) : F2 (Λ := Λ) K (y j.castSucc - (realC K).π₂ (Z j) * y (Fin.last n)) =
      F2 (Λ := Λ) K (y j.castSucc) -
        (realC K).π₂ (frobeniusRingHom (Λ := Λ) (A := K) (Z j)) *
          F2 (Λ := Λ) K (y (Fin.last n)) := by
    rw [map_sub, map_mul, F2_π₂_apply_eq]
  simp_rw [hFsub]
  have hZπ : (realC K).π₂ (Z i) =
      (∑ j, (realC K).π₂ (A i j) *
        (realC K).π₂ (frobeniusRingHom (Λ := Λ) (A := K) (Z j))) + (realC K).π₂ (C i) := by
    calc
      (realC K).π₂ (Z i) =
          (realC K).π₂ ((∑ j, A i j * frobeniusRingHom (Λ := Λ) (A := K) (Z j)) + C i) := by
            rw [hZ i]
      _ = (realC K).π₂ (∑ j, A i j * frobeniusRingHom (Λ := Λ) (A := K) (Z j)) +
            (realC K).π₂ (C i) :=
        map_add (realC K).π₂ _ _
      _ = (∑ j, (realC K).π₂ (A i j * frobeniusRingHom (Λ := Λ) (A := K) (Z j))) +
            (realC K).π₂ (C i) := by
        rw [map_sum]
      _ = (∑ j, (realC K).π₂ (A i j) *
            (realC K).π₂ (frobeniusRingHom (Λ := Λ) (A := K) (Z j))) +
            (realC K).π₂ (C i) := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact map_mul (realC K).π₂ _ _
  rw [hZπ]
  rw [show ((∑ j, (realC K).π₂ (A i j) *
        (realC K).π₂ (frobeniusRingHom (Λ := Λ) (A := K) (Z j))) +
        (realC K).π₂ (C i)) * y (Fin.last n) =
      ((∑ j, (realC K).π₂ (A i j) *
        (realC K).π₂ (frobeniusRingHom (Λ := Λ) (A := K) (Z j))) +
        (realC K).π₂ (C i)) * F2 (Λ := Λ) K (y (Fin.last n)) by
        exact congrArg (fun t => ((∑ j, (realC K).π₂ (A i j) *
          (realC K).π₂ (frobeniusRingHom (Λ := Λ) (A := K) (Z j))) +
          (realC K).π₂ (C i)) * t) hlast]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  simp only [Matrix.map_apply]
  ring_nf

/-- If fixed solutions span for a block matrix and the extension column is killed
by a shear, then fixed solutions span for the upper-left block. -/
lemma matrixFixedSpans_upper_left_of_extension {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) (realC K).R₁)
    (A : Matrix (Fin n) (Fin n) (RealNovikovSeries K))
    (C Z : Fin n → RealNovikovSeries K)
    (hspan : matrixFixedSpans (Λ := Λ) (K := K) T)
    (hblock : ∀ i j : Fin n, T i.castSucc j.castSucc = A i j)
    (hcol : ∀ i : Fin n, T i.castSucc (Fin.last n) = C i)
    (hlastrow : ∀ j : Fin n, T (Fin.last n) j.castSucc = 0)
    (hlastdiag : T (Fin.last n) (Fin.last n) = 1)
    (hZ : ∀ i, Z i = (∑ j, A i j * frobeniusRingHom (Λ := Λ) (A := K) (Z j)) + C i) :
    matrixFixedSpans (Λ := Λ) (K := K) A := by
  intro l hl
  let topUnshear : (Fin (n + 1) → (realC K).R₂) →ₗ[(realC K).R₂] (Fin n → (realC K).R₂) :=
    { toFun := fun y i => y i.castSucc - (realC K).π₂ (Z i) * y (Fin.last n)
      map_add' := by
        intro x y
        ext i
        simp
        ring
      map_smul' := by
        intro a y
        ext i
        simp
        ring }
  let lfull : (Fin (n + 1) → (realC K).R₂) →ₗ[(realC K).R₂] (realC K).R₂ := l.comp topUnshear
  have hlfull : lfull = 0 := by
    apply hspan
    intro y hy
    exact hl (topUnshear y)
      (top_unshear_fixed (Λ := Λ) T A C Z hblock hcol hlastrow hlastdiag hZ y hy)
  apply LinearMap.ext
  intro v
  let y : Fin (n + 1) → (realC K).R₂ := Fin.snoc v (0 : (realC K).R₂)
  have hv := LinearMap.congr_fun hlfull y
  change l (topUnshear y) = 0 at hv
  have htop : topUnshear y = v := by
    ext i
    simp [topUnshear, y]
  simpa [htop] using hv

/-- A triangular Frobenius matrix whose fixed solutions span is conjugate to the
identity Frobenius.  This is the coordinate induction behind the algebraically
closed descent argument. -/
lemma triangular_matrix_conjugates_to_identity :
    ∀ {n : ℕ} (T : Matrix (Fin n) (Fin n) (RealNovikovSeries K))
      (c : Fin n → Kˣ),
      matrixFixedSpans (Λ := Λ) (K := K) T →
      (∀ i j, j < i → T i j = 0) →
      (∀ i, T i i = algebraMap K (RealNovikovSeries K) ((c i : K))) →
      ∃ B : (Fin n → RealNovikovSeries K) ≃ₗ[RealNovikovSeries K]
          (Fin n → RealNovikovSeries K),
        ∀ v, B (T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (v j))) =
          fun i => frobeniusRingHom (Λ := Λ) (A := K) (B v i) := by
  intro n
  induction n with
  | zero =>
      intro T c hspan htri hdiag
      refine ⟨LinearEquiv.refl (RealNovikovSeries K) (Fin 0 → RealNovikovSeries K), ?_⟩
      intro v
      ext i
      exact Fin.elim0 i
  | succ n ih =>
      intro T c hspan htri hdiag
      let A : Matrix (Fin n) (Fin n) (RealNovikovSeries K) := fun i j => T i.castSucc j.castSucc
      let C : Fin n → RealNovikovSeries K := fun i => T i.castSucc (Fin.last n)
      let cA : Fin n → Kˣ := fun i => c i.castSucc
      have hblock : ∀ i j : Fin n, T i.castSucc j.castSucc = A i j := by intro i j; rfl
      have hcol : ∀ i : Fin n, T i.castSucc (Fin.last n) = C i := by intro i; rfl
      have hlastrow : ∀ j : Fin n, T (Fin.last n) j.castSucc = 0 := by
        intro j
        apply htri
        exact Fin.lt_last_iff_ne_last.mpr (by simp)
      have hc : c (Fin.last n) = 1 :=
        matrixFixedSpans_last_scalar_eq_one (Λ := Λ) T c hspan htri hdiag
      have hlastdiag : T (Fin.last n) (Fin.last n) = 1 := by
        rw [hdiag (Fin.last n), hc]
        simp
      have hAtri : ∀ i j : Fin n, j < i → A i j = 0 := by
        intro i j hij
        exact htri i.castSucc j.castSucc (by simpa using hij)
      have hAdiag : ∀ i : Fin n, A i i = algebraMap K (RealNovikovSeries K) ((cA i : K)) := by
        intro i
        exact hdiag i.castSucc
      obtain ⟨y, hyfix, hyne⟩ :=
        matrixFixedSpans_exists_fixed_coord_ne_zero (Λ := Λ) (K := K) T hspan (Fin.last n)
      have hylast_fix : F2 (Λ := Λ) K (y (Fin.last n)) = y (Fin.last n) := by
        have hlast := congrFun hyfix (Fin.last n)
        rw [upper_triangular_last_coordinate T htri] at hlast
        rw [hdiag (Fin.last n), hc] at hlast
        rw [π₂_algebraMap] at hlast
        simp at hlast
        exact hlast.symm
      have hxj : ∀ i : Fin n, y i.castSucc =
          (∑ j, (realC K).π₂ (A i j) * F2 (Λ := Λ) K (y j.castSucc)) +
            (realC K).π₂ (C i) * F2 (Λ := Λ) K (y (Fin.last n)) := by
        intro i
        exact block_row_fixed_equation_general (Λ := Λ) T A C hblock hcol y hyfix i
      obtain ⟨Z, hZ⟩ := generalized_extension_extract (Λ := Λ) A C (y (Fin.last n))
        (fun i => y i.castSucc) hyne hylast_fix hxj
      have hAspan : matrixFixedSpans (Λ := Λ) (K := K) A :=
        matrixFixedSpans_upper_left_of_extension (Λ := Λ) T A C Z hspan hblock hcol
          hlastrow hlastdiag hZ
      obtain ⟨Btop, hBtop⟩ := ih A cA hAspan hAtri hAdiag
      let prodB : ((Fin n → RealNovikovSeries K) × RealNovikovSeries K) ≃ₗ[RealNovikovSeries K]
          ((Fin n → RealNovikovSeries K) × RealNovikovSeries K) :=
        Btop.prodCongr (LinearEquiv.refl (RealNovikovSeries K) (RealNovikovSeries K))
      let B : (Fin (n + 1) → RealNovikovSeries K) ≃ₗ[RealNovikovSeries K]
          (Fin (n + 1) → RealNovikovSeries K) :=
        (finSnocLinearEquiv (K := K) n).symm.trans
          ((blockShear Z).symm.trans (prodB.trans (finSnocLinearEquiv (K := K) n)))
      refine ⟨B, ?_⟩
      intro v
      dsimp [B]
      rw [finSnocLinearEquiv_blockFrobeniusGeneral (Λ := Λ) T A C hblock hcol hlastrow
        hlastdiag v]
      let p : (Fin n → RealNovikovSeries K) × RealNovikovSeries K :=
        (blockShear Z).symm ((finSnocLinearEquiv (K := K) n).symm v)
      have hp : (finSnocLinearEquiv (K := K) n).symm v = blockShear Z p := by
        dsimp [p]
        rw [LinearEquiv.apply_symm_apply]
      rw [hp, blockShear_conjugates_general (Λ := Λ) A C Z hZ p]
      simp only [prodB, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
        LinearEquiv.symm_apply_apply]
      rw [hBtop p.1]
      exact finSnocLinearEquiv_frobenius (Λ := Λ) (K := K)
        ((Btop p.1, p.2) : (Fin n → RealNovikovSeries K) × RealNovikovSeries K)

/-- Over an algebraically closed field, the isocrystal attached to any real
Novikov descent datum is constant. -/
theorem descentToIsocrystal_obj_is_const_of_algClosed [IsAlgClosed K]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) K) :
    ∃ P : FiniteProjectiveModule.{u,u} K,
      Nonempty ((descentToIsocrystal.{u,u} (Λ := Λ) K).obj M ≅
        (NovikovIsocrystal.vectToNovIsoc.{u,u} (Λ := Λ) (A := K)).obj P) := by
  let I := (descentToIsocrystal.{u,u} (Λ := Λ) K).obj M
  obtain ⟨n, e, c, T, htri, hdiag, hF⟩ := nov_isoc_geom_pt_triangular (Λ := Λ) I
  have hF' : ∀ m, e (descentFrobeniusToFun (Λ := Λ) K M m) =
      T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (e m j)) := by
    intro m
    exact hF m
  have hspan : matrixFixedSpans (Λ := Λ) (K := K) T :=
    matrixFixedSpans_of_descent (Λ := Λ) M e T hF'
  obtain ⟨B, hB⟩ := triangular_matrix_conjugates_to_identity (Λ := Λ) T c hspan htri hdiag
  refine ⟨{ M := Fin n → K }, ⟨?_⟩⟩
  exact coordinateIsoToConst (Λ := Λ) I e T B hB hF

/-- Over an algebraically closed field, constant real Novikov descent data are an
equivalence.  Essential surjectivity lifts the isocrystal-constancy theorem
`descentToIsocrystal_obj_is_const_of_algClosed` through the fully faithful
functor `descentToIsocrystal`. -/
theorem vectToNovikovDescent_isEquivalence_algClosed
    (K : Type u) [Field K] [IsAlgClosed K] :
    (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) K).IsEquivalence := by
  letI : Fact ((2 : ℝ) > 1) := ⟨by norm_num⟩
  let F := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) K
  have hFF : F.FullyFaithful := vectToNovikovDescent_fullyFaithful (⊤ : AddSubgroup ℝ) K
  letI : F.Faithful := hFF.faithful
  letI : F.Full := hFF.full
  letI : F.EssSurj := by
    constructor
    intro M
    obtain ⟨P, ⟨e⟩⟩ := descentToIsocrystal_obj_is_const_of_algClosed (Λ := (2 : ℝ)) (K := K) M
    refine ⟨P, ⟨?_⟩⟩
    let α := descentToIsocrystal_comp_vectToNovikovDescent_iso.{u,u} (Λ := (2 : ℝ)) (A := K)
    exact (descentToIsocrystal_fullyFaithful.{u,u} (Λ := (2 : ℝ)) (A := K)).preimageIso
      ((α.app P).trans e.symm)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The corresponding bundled categorical equivalence. -/
noncomputable def vectToNovikovDescent_equivalence_algClosed
    (K : Type u) [Field K] [IsAlgClosed K] :
    FiniteProjectiveModule.{u, u} K ≌ NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) K := by
  let F := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) K
  haveI : F.IsEquivalence := vectToNovikovDescent_isEquivalence_algClosed K
  exact F.asEquivalence

end Novikov.Descent
