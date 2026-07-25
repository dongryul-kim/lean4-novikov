import Novikov.Descent.Nilpotent
import Novikov.Descent.Reduced
import Novikov.Isocrystal.Lattice
import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Real Novikov descent over arbitrary commutative rings

Every real Novikov descent datum becomes constant after quotienting by a
finitely generated nilpotent ideal. The proof constructs that ideal from the
nonpositive coefficients of finitely many Frobenius errors, applies the lattice
criterion for isocrystals, and then lifts constancy through the nilpotent
thickening.
-/

noncomputable section

open CategoryTheory TensorProduct
open Novikov Novikov.Descent.Abstract Novikov.Miscellany

namespace Novikov.Descent

universe u v

private lemma one_tmul_span_eq_top
    {R S N ι : Type*} [CommRing R] [CommRing S]
    [AddCommGroup N] [Module R N] [Algebra R S]
    (v : ι → N)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span S
        (Set.range fun i => (1 : S) ⊗ₜ[R] v i) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul s m =>
      have hm : m ∈ Submodule.span R (Set.range v) := by
        rw [hv]
        trivial
      induction hm using Submodule.span_induction generalizing s with
      | mem m hm =>
          obtain ⟨i, rfl⟩ := hm
          rw [TensorProduct.tmul_eq_smul_one_tmul]
          exact Submodule.smul_mem _ s (Submodule.subset_span ⟨i, rfl⟩)
      | zero => simp only [TensorProduct.tmul_zero, Submodule.zero_mem]
      | add x y _ _ hx hy =>
          simpa only [TensorProduct.tmul_add] using
            Submodule.add_mem _ (hx s) (hy s)
      | smul a m _ hm =>
          rw [TensorProduct.tmul_smul]
          exact hm _

private lemma exists_generators_reduction_frobenius_error_zero
    {Λ : ℝ} [Fact (Λ > 1)]
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (N₀ : FiniteProjectiveModule.{u, u} B)
    (e : Novikov.baseChange q I ≅
      NovikovIsocrystal.ConstIsocrystal (Λ := Λ) N₀) :
    ∃ n k : ℕ, ∃ g : Fin n ⊕ Fin k → I.M,
      Submodule.span (RealNovikovSeries A) (Set.range g) = ⊤ ∧
      ∀ i, reductionMap
        (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) q) I.M
          (I.F_M (g i) - g i) = 0 := by
  classical
  let qR := mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) q
  have hqR : Function.Surjective qR := mapRingHom_surjective q hq
  obtain ⟨n, v, hv⟩ :=
    Module.Finite.exists_fin (R := B) (M := N₀.M)
  let vB : Fin n →
      (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) N₀).M :=
    fun i => (1 : RealNovikovSeries B) ⊗ₜ[B] v i
  have hvB : Submodule.span (RealNovikovSeries B) (Set.range vB) = ⊤ :=
    one_tmul_span_eq_top v hv
  have hvB_surj : Function.Surjective
      (Fintype.linearCombination (RealNovikovSeries B) vB) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination
      (RealNovikovSeries B) vB).mp hvB
  let z : Fin n → (Novikov.baseChange q I).M :=
    fun i => e.inv.toLinearMap (vB i)
  have hred_surj : Function.Surjective (reductionMap qR I.M) :=
    reductionMap_surjective qR hqR
  choose m hm using fun i => hred_surj (z i)
  obtain ⟨k, u, hu⟩ :=
    Module.Finite.exists_fin (R := RealNovikovSeries A) (M := I.M)
  choose b hb using fun j =>
    hvB_surj (e.hom.toLinearMap (reductionMap qR I.M (u j)))
  choose a ha using fun j i => hqR (b j i)
  let h : Fin k → I.M := fun j => u j - ∑ i, a j i • m i
  let g : Fin n ⊕ Fin k → I.M := Sum.elim m h
  have he_inj : Function.Injective e.hom.toLinearMap := by
    intro x y hxy
    have hxy' := congrArg e.inv.toLinearMap hxy
    change (e.hom ≫ e.inv).toLinearMap x =
      (e.hom ≫ e.inv).toLinearMap y at hxy'
    rw [e.hom_inv_id] at hxy'
    exact hxy'
  have hem (i : Fin n) :
      e.hom.toLinearMap (reductionMap qR I.M (m i)) = vB i := by
    rw [hm]
    change (e.inv ≫ e.hom).toLinearMap (vB i) = vB i
    rw [e.inv_hom_id]
    rfl
  have hh (j : Fin k) : reductionMap qR I.M (h j) = 0 := by
    apply he_inj
    calc
      e.hom.toLinearMap (reductionMap qR I.M (h j)) = 0 := by
        simp only [h, map_sub, map_sum, map_smul]
        have hscalar (i : Fin n) :
            e.hom.toLinearMap (a j i • reductionMap qR I.M (m i)) =
              b j i • vB i := by
          change e.hom.toLinearMap
              (qR (a j i) • reductionMap qR I.M (m i)) = b j i • vB i
          calc
            e.hom.toLinearMap
                (qR (a j i) • reductionMap qR I.M (m i)) =
              qR (a j i) •
                e.hom.toLinearMap (reductionMap qR I.M (m i)) :=
                e.hom.toLinearMap.map_smul _ _
            _ = b j i • vB i := by rw [ha, hem]
        calc
          e.hom.toLinearMap
              (reductionMap qR I.M (u j) -
                ∑ i, a j i • reductionMap qR I.M (m i)) =
            e.hom.toLinearMap (reductionMap qR I.M (u j)) -
              e.hom.toLinearMap
                (∑ i, a j i • reductionMap qR I.M (m i)) :=
              e.hom.toLinearMap.map_sub _ _
          _ = e.hom.toLinearMap (reductionMap qR I.M (u j)) -
              ∑ i, e.hom.toLinearMap
                (a j i • reductionMap qR I.M (m i)) := by
            congr 1
            exact map_sum e.hom.toLinearMap
              (fun i => a j i • reductionMap qR I.M (m i)) Finset.univ
          _ = e.hom.toLinearMap (reductionMap qR I.M (u j)) -
              ∑ i, b j i • vB i := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            exact hscalar i
          _ = 0 := by rw [← hb]; exact sub_self _
      _ = e.hom.toLinearMap 0 := e.hom.toLinearMap.map_zero.symm
  have hFRed (x : I.M) :
      reductionMap qR I.M (I.F_M x) =
        (Novikov.baseChange q I).F_M (reductionMap qR I.M x) := by
    rw [reductionMap_apply, reductionMap_apply, Novikov.baseChange_F_tmul]
    simp only [map_one]
  refine ⟨n, k, g, ?_, ?_⟩
  · apply top_unique
    rw [← hu]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hh_mem : h j ∈ Submodule.span (RealNovikovSeries A) (Set.range g) :=
      Submodule.subset_span ⟨Sum.inr j, rfl⟩
    have hm_mem : ∑ i, a j i • m i ∈
        Submodule.span (RealNovikovSeries A) (Set.range g) := by
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
    rw [show u j = h j + ∑ i, a j i • m i by simp only [h]; abel]
    exact Submodule.add_mem _ hh_mem hm_mem
  · intro i
    rcases i with i | j
    · change reductionMap qR I.M (I.F_M (m i) - m i) = 0
      rw [map_sub, hFRed, hm]
      change (Novikov.baseChange q I).F_M
          (e.inv.toLinearMap (vB i)) - e.inv.toLinearMap (vB i) = 0
      rw [e.inv.commute_frobenius]
      have hvB_fixed :
          (NovikovIsocrystal.ConstIsocrystal (Λ := Λ) N₀).F_M (vB i) =
            vB i := by
        change TensorProduct.map
            (frobeniusAlgHom (Λ := Λ) (A := B)).toLinearMap
            (LinearMap.id : N₀.M →ₗ[B] N₀.M)
            ((1 : RealNovikovSeries B) ⊗ₜ[B] v i) =
          (1 : RealNovikovSeries B) ⊗ₜ[B] v i
        rw [TensorProduct.map_tmul]
        change frobeniusRingHom (Λ := Λ) (A := B)
            (1 : RealNovikovSeries B) ⊗ₜ[B] v i =
          (1 : RealNovikovSeries B) ⊗ₜ[B] v i
        rw [map_one]
      rw [hvB_fixed, sub_self]
    · change reductionMap qR I.M (I.F_M (h j) - h j) = 0
      rw [map_sub, hFRed, hh]
      exact sub_eq_zero.mpr (Novikov.baseChange q I).F_M.map_zero

private lemma exists_frobenius_error_coefficients
    {Λ : ℝ} [Fact (Λ > 1)]
    {A B : Type u} {ι : Type v} [CommRing A] [CommRing B]
    [Fintype ι]
    (q : A →+* B) (hq : Function.Surjective q)
    (I : NovikovIsocrystal (Λ := Λ) A)
    (g : ι → I.M)
    (hg : Submodule.span (RealNovikovSeries A) (Set.range g) = ⊤)
    (hzero : ∀ i, reductionMap
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) q) I.M
        (I.F_M (g i) - g i) = 0) :
    ∃ c : ι → ι → RealNovikovSeries A,
      (∀ i, I.F_M (g i) - g i = ∑ j, c i j • g j) ∧
      ∀ i j, c i j ∈ RingHom.ker
        (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) q) := by
  classical
  let qR := mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) q
  have hqR : Function.Surjective qR := mapRingHom_surjective q hq
  have herr (i : ι) : I.F_M (g i) - g i ∈
      RingHom.ker qR •
        Submodule.span (RealNovikovSeries A) (Set.range g) := by
    have hi : I.F_M (g i) - g i ∈ LinearMap.ker (reductionMap qR I.M) := by
      exact hzero i
    rw [reductionMap_ker qR hqR] at hi
    rw [hg]
    exact hi
  choose c hc_mem hc_sum using fun i =>
    (Submodule.mem_ideal_smul_span_iff_exists_sum
      (RingHom.ker qR) g (I.F_M (g i) - g i)).mp (herr i)
  refine ⟨fun i j => c i j, ?_, ?_⟩
  · intro i
    calc
      I.F_M (g i) - g i = (c i).sum (fun j a => a • g j) :=
        (hc_sum i).symm
      _ = ∑ j, c i j • g j :=
        Finsupp.sum_fintype (c i) (fun j a => a • g j) (by
          intro j
          exact zero_smul _ _)
  · intro i j
    exact hc_mem i j

private def nonpositiveCoefficients
    {A : Type u} {ι : Type v} [CommRing A] [Fintype ι]
    (c : ι → ι → RealNovikovSeries A) : Set A :=
  ⋃ i, ⋃ j, (fun d => (c i j).val d) ''
    {d : Unit → (⊤ : AddSubgroup ℝ) |
      (c i j).val d ≠ 0 ∧ (d () : ℝ) ≤ 0}

private lemma nonpositiveCoefficients_finite
    {A : Type u} {ι : Type v} [CommRing A] [Fintype ι]
    (c : ι → ι → RealNovikovSeries A) :
    (nonpositiveCoefficients c).Finite := by
  apply Set.finite_iUnion
  intro i
  apply Set.finite_iUnion
  intro j
  apply Set.Finite.image
  exact (finite_support_below (c i j) 1).subset (by
    intro d hd
    exact ⟨hd.1, by linarith [hd.2]⟩)

/-- A finite family of real Novikov series vanishing modulo the nilradical
becomes strictly positive after quotienting by a nilpotent ideal. -/
lemma exists_nilpotent_ideal_coefficients_positive
    {A : Type u} {ι : Type v} [CommRing A] [Fintype ι]
    (c : ι → ι → RealNovikovSeries A)
    (hc : ∀ i j, c i j ∈ RingHom.ker
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
        (Ideal.Quotient.mk (nilradical A)))) :
    ∃ J : Ideal A, IsNilpotent J ∧
      ∀ i j, IsPositive
        (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
          (Ideal.Quotient.mk J) (c i j)) := by
  classical
  let J : Ideal A := Ideal.span (nonpositiveCoefficients c)
  have hJ_fg : J.FG := by
    exact Submodule.fg_span (nonpositiveCoefficients_finite c)
  have hJ_le : J ≤ nilradical A := by
    change Ideal.span (nonpositiveCoefficients c) ≤ nilradical A
    apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_iUnion.mp ha with ⟨i, ha⟩
    rcases Set.mem_iUnion.mp ha with ⟨j, ha⟩
    rcases ha with ⟨d, hd, rfl⟩
    have hcij := hc i j
    change mapRingHom (Ideal.Quotient.mk (nilradical A)) (c i j) = 0 at hcij
    have hd0 := congrArg
      (fun x : RealNovikovSeries (A ⧸ nilradical A) => x.val d) hcij
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [mapRingHom_apply, ZeroMemClass.coe_zero, Pi.zero_apply] using hd0
  refine ⟨J, (hJ_fg.isNilpotent_iff_le_nilradical).mpr hJ_le, ?_⟩
  intro i j d hd
  rw [mapRingHom_apply]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  by_cases hcoeff : (c i j).val d = 0
  · simpa only [hcoeff] using J.zero_mem
  · apply Ideal.subset_span
    change (c i j).val d ∈ nonpositiveCoefficients c
    apply Set.mem_iUnion.mpr
    refine ⟨i, Set.mem_iUnion.mpr ?_⟩
    refine ⟨j, ?_⟩
    exact ⟨d, ⟨hcoeff, hd⟩, rfl⟩

private noncomputable def baseChangeGenerator
    {Λ : ℝ} [Fact (Λ > 1)]
    {A B : Type u} {ι : Type v} [CommRing A] [CommRing B]
    (q : A →+* B) (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (g : ι → I.M) : ι → (Novikov.baseChange q I).M :=
  letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) :=
    Novikov.realNovikovSeriesAlgebra q
  fun i => (1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] g i

private lemma baseChangeGenerator_span_eq_top
    {Λ : ℝ} [Fact (Λ > 1)]
    {A B : Type u} {ι : Type v} [CommRing A] [CommRing B]
    (q : A →+* B) (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (g : ι → I.M)
    (hg : Submodule.span (RealNovikovSeries A) (Set.range g) = ⊤) :
    Submodule.span (RealNovikovSeries B)
      (Set.range (baseChangeGenerator q I g)) = ⊤ := by
  letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) :=
    Novikov.realNovikovSeriesAlgebra q
  change Submodule.span (RealNovikovSeries B)
    (Set.range fun i => (1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] g i) = ⊤
  exact one_tmul_span_eq_top g hg

private noncomputable def generatorLattice
    {Λ : ℝ} [Fact (Λ > 1)]
    {A B : Type u} {ι : Type v} [CommRing A] [CommRing B] [Fintype ι]
    (q : A →+* B) (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (g : ι → I.M)
    (hg : Submodule.span (RealNovikovSeries A) (Set.range g) = ⊤) :
    (Novikov.baseChange q I).Lattice where
  carrier := Submodule.span (RealNovikovPowerSeries B)
    (Set.range (baseChangeGenerator q I g))
  finite := Module.Finite.span_of_finite
    (RealNovikovPowerSeries B) (Set.finite_range _)
  span_eq_top := by
    apply top_unique
    rw [← baseChangeGenerator_span_eq_top q I g hg]
    exact Submodule.span_mono Submodule.subset_span

private lemma baseChangeGenerator_frobenius_error
    {Λ : ℝ} [Fact (Λ > 1)]
    {A B : Type u} {ι : Type v} [CommRing A] [CommRing B] [Fintype ι]
    (q : A →+* B) (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (g : ι → I.M) (c : ι → ι → RealNovikovSeries A)
    (herror : ∀ i, I.F_M (g i) - g i = ∑ j, c i j • g j)
    (i : ι) :
    (Novikov.baseChange q I).F_M (baseChangeGenerator q I g i) -
        baseChangeGenerator q I g i =
      ∑ j, mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) q (c i j) •
        baseChangeGenerator q I g j := by
  let qR := mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) q
  letI : Algebra (RealNovikovSeries A) (RealNovikovSeries B) := qR.toAlgebra
  dsimp only [baseChangeGenerator]
  rw [Novikov.baseChange_F_tmul, map_one]
  let T := TensorProduct.mk (RealNovikovSeries A)
    (RealNovikovSeries B) I.M (1 : RealNovikovSeries B)
  change T (I.F_M (g i)) - T (g i) =
    ∑ j, qR (c i j) • T (g j)
  calc
    T (I.F_M (g i)) - T (g i) = T (I.F_M (g i) - g i) :=
      (T.map_sub _ _).symm
    _ = T (∑ j, c i j • g j) := congrArg T (herror i)
    _ = ∑ j, T (c i j • g j) :=
      map_sum T (fun j => c i j • g j) Finset.univ
    _ = ∑ j, qR (c i j) • T (g j) := by
      apply Finset.sum_congr rfl
      intro j hj
      change (1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A]
          (c i j • g j) =
        qR (c i j) •
          ((1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] g j)
      rw [TensorProduct.tmul_smul]
      change (qR (c i j) * 1) ⊗ₜ[RealNovikovSeries A] g j =
        qR (c i j) •
          ((1 : RealNovikovSeries B) ⊗ₜ[RealNovikovSeries A] g j)
      rw [mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private lemma generatorLattice_generator_error_mem
    {Λ : ℝ} [Fact (Λ > 1)]
    {A : Type u} {ι : Type v} [CommRing A] [Fintype ι]
    (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (g : ι → I.M)
    (hg : Submodule.span (RealNovikovSeries A) (Set.range g) = ⊤)
    (c : ι → ι → RealNovikovSeries A)
    (herror : ∀ i, I.F_M (g i) - g i = ∑ j, c i j • g j)
    (J : Ideal A)
    (hcpos : ∀ i j, IsPositive
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
        (Ideal.Quotient.mk J) (c i j))) (i : ι) :
    let qJ := Ideal.Quotient.mk J
    let IC := Novikov.baseChange qJ I
    let L := generatorLattice qJ I g hg
    IC.F_M (baseChangeGenerator qJ I g i) -
        baseChangeGenerator qJ I g i ∈
      RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) • L.carrier := by
  classical
  dsimp only
  rw [baseChangeGenerator_frobenius_error
    (Ideal.Quotient.mk J) I g c herror i]
  apply Submodule.sum_mem
  intro j hj
  let cP : RealNovikovPowerSeries (A ⧸ J) :=
    ⟨mapRingHom (Ideal.Quotient.mk J) (c i j),
      fun d hd => hcpos i j d hd.le⟩
  change cP • baseChangeGenerator (Ideal.Quotient.mk J) I g j ∈
    RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) •
      (generatorLattice (Ideal.Quotient.mk J) I g hg).carrier
  apply Submodule.smul_mem_smul
  · rw [RealNovikovPowerSeries.mem_positiveIdeal_iff_isPositive]
    exact hcpos i j
  · exact Submodule.subset_span ⟨j, rfl⟩

private lemma generatorLattice_error_mem
    {Λ : ℝ} [Fact (Λ > 1)]
    {A : Type u} {ι : Type v} [CommRing A] [Fintype ι]
    (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (g : ι → I.M)
    (hg : Submodule.span (RealNovikovSeries A) (Set.range g) = ⊤)
    (c : ι → ι → RealNovikovSeries A)
    (herror : ∀ i, I.F_M (g i) - g i = ∑ j, c i j • g j)
    (J : Ideal A)
    (hcpos : ∀ i j, IsPositive
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
        (Ideal.Quotient.mk J) (c i j)))
    (x : (Novikov.baseChange (Ideal.Quotient.mk J) I).M)
    (hx : x ∈ (generatorLattice
      (Ideal.Quotient.mk J) I g hg).carrier) :
    let IC := Novikov.baseChange (Ideal.Quotient.mk J) I
    let L := generatorLattice (Ideal.Quotient.mk J) I g hg
    IC.F_M x - x ∈
      RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) • L.carrier := by
  classical
  dsimp only
  let qJ := Ideal.Quotient.mk J
  let IC := Novikov.baseChange qJ I
  let L := generatorLattice qJ I g hg
  change IC.F_M x - x ∈
    RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) • L.carrier
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact generatorLattice_generator_error_mem I g hg c herror J hcpos i
  | zero =>
      rw [IC.F_M.map_zero, sub_self]
      exact Submodule.zero_mem _
  | add y z hy hz ihy ihz =>
      have hadd := Submodule.add_mem
        (RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) • L.carrier) ihy ihz
      rw [map_add]
      have heq : IC.F_M y + IC.F_M z - (y + z) =
          (IC.F_M y - y) + (IC.F_M z - z) := by abel
      rw [heq]
      exact hadd
  | smul a y hy ih =>
      let Fa : RealNovikovPowerSeries (A ⧸ J) :=
        ⟨frobenius Λ (a : RealNovikovSeries (A ⧸ J)), by
          have hFa := frobenius_filtration (Λ := Λ)
            (a : RealNovikovSeries (A ⧸ J)) 0 a.property
          simpa using hFa⟩
      let δa : RealNovikovPowerSeries (A ⧸ J) :=
        ⟨frobenius Λ (a : RealNovikovSeries (A ⧸ J)) - a,
          (filtration (⊤ : AddSubgroup ℝ) (A ⧸ J) 0).sub_mem
            Fa.property a.property⟩
      have hfirst : Fa • (IC.F_M y - y) ∈
          RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) • L.carrier :=
        (RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) •
          L.carrier).smul_mem Fa ih
      have hδa : δa ∈
          RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) := by
        rw [RealNovikovPowerSeries.mem_positiveIdeal_iff_isPositive]
        exact RealNovikovPowerSeries.frobenius_sub_self_isPositive a
      have hsecond : δa • y ∈
          RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) • L.carrier :=
        Submodule.smul_mem_smul hδa hy
      have hsum := Submodule.add_mem
        (RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) • L.carrier)
        hfirst hsecond
      change IC.F_M ((a : RealNovikovSeries (A ⧸ J)) • y) -
          (a : RealNovikovSeries (A ⧸ J)) • y ∈ _
      rw [map_smulₛₗ]
      change frobenius Λ (a : RealNovikovSeries (A ⧸ J)) • IC.F_M y -
          (a : RealNovikovSeries (A ⧸ J)) • y ∈ _
      dsimp only [Fa, δa] at hsum
      change frobenius Λ (a : RealNovikovSeries (A ⧸ J)) •
          (IC.F_M y - y) +
        (frobenius Λ (a : RealNovikovSeries (A ⧸ J)) - a) • y ∈ _ at hsum
      have heq :
          frobenius Λ (a : RealNovikovSeries (A ⧸ J)) • IC.F_M y -
              (a : RealNovikovSeries (A ⧸ J)) • y =
            frobenius Λ (a : RealNovikovSeries (A ⧸ J)) • (IC.F_M y - y) +
              (frobenius Λ (a : RealNovikovSeries (A ⧸ J)) - a) • y := by
        module
      rw [heq]
      exact hsum

/-- Positive Frobenius-error coefficients on a finite generating family
produce a lattice on which every Frobenius error lies in the positive ideal. -/
lemma exists_lattice_frobenius_error_positive
    {Λ : ℝ} [Fact (Λ > 1)]
    {A : Type u} {ι : Type v} [CommRing A] [Fintype ι]
    (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (g : ι → I.M)
    (hg : Submodule.span (RealNovikovSeries A) (Set.range g) = ⊤)
    (c : ι → ι → RealNovikovSeries A)
    (herror : ∀ i, I.F_M (g i) - g i = ∑ j, c i j • g j)
    (J : Ideal A)
    (hcpos : ∀ i j, IsPositive
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
        (Ideal.Quotient.mk J) (c i j))) :
    let qJ := Ideal.Quotient.mk J
    let IC := Novikov.baseChange qJ I
    ∃ L : IC.Lattice,
      ∀ x : L.carrier,
        IC.F_M (x : IC.M) - (x : IC.M) ∈
          RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) • L.carrier := by
  dsimp only
  let L := generatorLattice (Ideal.Quotient.mk J) I g hg
  refine ⟨L, ?_⟩
  intro x
  exact generatorLattice_error_mem I g hg c herror J hcpos x x.property

private lemma nilradical_isRadical
    (A : Type u) [CommRing A] : (nilradical A).IsRadical := by
  change (⊥ : Ideal A).radical.IsRadical
  exact Ideal.radical_isRadical (⊥ : Ideal A)

private theorem baseChange_nilradical_isocrystal_const
    {Λ : ℝ} [Fact (Λ > 1)]
    (A : Type u) [CommRing A]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A) :
    let Ired := nilradical A
    let q := Ideal.Quotient.mk Ired
    let IA := (descentToIsocrystal.{u, u} (Λ := Λ) A).obj M
    ∃ N₀ : FiniteProjectiveModule.{u, u} (A ⧸ Ired),
      Nonempty
        (Novikov.baseChange q IA ≅
          NovikovIsocrystal.ConstIsocrystal (Λ := Λ) N₀) := by
  dsimp only
  let Ired := nilradical A
  let B := A ⧸ Ired
  let q : A →+* B := Ideal.Quotient.mk Ired
  letI : IsReduced B :=
    (Ideal.isRadical_iff_quotient_reduced Ired).mp
      (nilradical_isRadical A)
  let IA := (descentToIsocrystal.{u, u} (Λ := Λ) A).obj M
  let MB := M.baseChange (realCCoeffHom q)
  obtain ⟨N₀, ⟨eB⟩⟩ :=
    descentToIsocrystal_obj_is_const_of_reduced (Λ := Λ) B MB
  refine ⟨N₀, ⟨?_⟩⟩
  exact descentToIsocrystal_baseChangeIso (Λ := Λ) q M ≪≫ eB

private structure GeneratorData
    {Λ : ℝ} [Fact (Λ > 1)]
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (I : NovikovIsocrystal.{u, u} (Λ := Λ) A) where
  n : ℕ
  k : ℕ
  g : Fin n ⊕ Fin k → I.M
  span_eq_top : Submodule.span (RealNovikovSeries A) (Set.range g) = ⊤
  error_zero : ∀ i, reductionMap
    (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) q) I.M
      (I.F_M (g i) - g i) = 0

private noncomputable def generatorData
    {Λ : ℝ} [Fact (Λ > 1)]
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (N₀ : FiniteProjectiveModule.{u, u} B)
    (e : Novikov.baseChange q I ≅
      NovikovIsocrystal.ConstIsocrystal (Λ := Λ) N₀) :
    GeneratorData q I := by
  apply Classical.choice
  obtain ⟨n, k, g, hg, hzero⟩ :=
    exists_generators_reduction_frobenius_error_zero q hq I N₀ e
  exact ⟨⟨n, k, g, hg, hzero⟩⟩

private structure CoefficientData
    {Λ : ℝ} [Fact (Λ > 1)]
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (G : GeneratorData q I) where
  c : (Fin G.n ⊕ Fin G.k) → (Fin G.n ⊕ Fin G.k) → RealNovikovSeries A
  error_eq : ∀ i, I.F_M (G.g i) - G.g i = ∑ j, c i j • G.g j
  mem_ker : ∀ i j, c i j ∈ RingHom.ker
    (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) q)

private noncomputable def coefficientData
    {Λ : ℝ} [Fact (Λ > 1)]
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (G : GeneratorData q I) : CoefficientData q I G := by
  apply Classical.choice
  obtain ⟨c, herror, hc⟩ :=
    exists_frobenius_error_coefficients
      (Λ := Λ) (A := A) (B := B) (ι := Fin G.n ⊕ Fin G.k)
      q hq I G.g G.span_eq_top G.error_zero
  exact ⟨⟨c, herror, hc⟩⟩

private structure IdealData
    {A : Type u} {ι : Type v} [CommRing A] [Fintype ι]
    (c : ι → ι → RealNovikovSeries A) where
  J : Ideal A
  isNilpotent : IsNilpotent J
  coefficients_positive : ∀ i j, IsPositive
    (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
      (Ideal.Quotient.mk J) (c i j))

private noncomputable def idealData
    {A : Type u} {ι : Type v} [CommRing A] [Fintype ι]
    (c : ι → ι → RealNovikovSeries A)
    (hc : ∀ i j, c i j ∈ RingHom.ker
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
        (Ideal.Quotient.mk (nilradical A)))) : IdealData c := by
  apply Classical.choice
  obtain ⟨J, hJ, hcpos⟩ :=
    exists_nilpotent_ideal_coefficients_positive c hc
  exact ⟨⟨J, hJ, hcpos⟩⟩

private structure LatticeData
    {Λ : ℝ} [Fact (Λ > 1)]
    {A : Type u} [CommRing A]
    (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (J : Ideal A) where
  L : (Novikov.baseChange (Ideal.Quotient.mk J) I).Lattice
  error_positive : ∀ x : L.carrier,
    (Novikov.baseChange (Ideal.Quotient.mk J) I).F_M
        (x : (Novikov.baseChange (Ideal.Quotient.mk J) I).M) - x ∈
      RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) • L.carrier

private noncomputable def latticeData
    {Λ : ℝ} [Fact (Λ > 1)]
    {A : Type u} {ι : Type v} [CommRing A] [Fintype ι]
    (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (g : ι → I.M)
    (hg : Submodule.span (RealNovikovSeries A) (Set.range g) = ⊤)
    (c : ι → ι → RealNovikovSeries A)
    (herror : ∀ i, I.F_M (g i) - g i = ∑ j, c i j • g j)
    (D : IdealData c) : LatticeData I D.J := by
  apply Classical.choice
  obtain ⟨L, hL⟩ := exists_lattice_frobenius_error_positive
    I g hg c herror D.J D.coefficients_positive
  exact ⟨⟨L, hL⟩⟩

/-- An isocrystal with a lattice whose Frobenius errors lie in the positive
ideal is constant. -/
theorem isocrystal_const_of_positive_lattice
    {Λ : ℝ} [Fact (Λ > 1)]
    {A : Type u} [CommRing A]
    (I : NovikovIsocrystal.{u, u} (Λ := Λ) A)
    (J : Ideal A)
    (L : (Novikov.baseChange (Ideal.Quotient.mk J) I).Lattice)
    (hL : ∀ x : L.carrier,
      (Novikov.baseChange (Ideal.Quotient.mk J) I).F_M
          (x : (Novikov.baseChange (Ideal.Quotient.mk J) I).M) - x ∈
        RealNovikovPowerSeries.positiveIdeal (A := A ⧸ J) • L.carrier) :
    ∃ P : FiniteProjectiveModule.{u, u} (A ⧸ J),
      Nonempty
        (Novikov.baseChange (Ideal.Quotient.mk J) I ≅
          NovikovIsocrystal.ConstIsocrystal (Λ := Λ) P) := by
  apply lattice_isocrystal (Novikov.baseChange (Ideal.Quotient.mk J) I) L
  intro x
  simpa only [NovikovIsocrystal.Lattice.shift] using
    (Submodule.mem_positiveIdeal_smul_iff_exists_realNovikovShift
      L.carrier
      ((Novikov.baseChange (Ideal.Quotient.mk J) I).F_M
        (x : (Novikov.baseChange (Ideal.Quotient.mk J) I).M) - x)).mp (hL x)

private theorem exists_nilpotent_ideal_isocrystal_const
    {Λ : ℝ} [Fact (Λ > 1)]
    (A : Type u) [CommRing A]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A) :
    let IA := (descentToIsocrystal.{u, u} (Λ := Λ) A).obj M
    ∃ J : Ideal A, IsNilpotent J ∧
      ∃ P : FiniteProjectiveModule.{u, u} (A ⧸ J),
        Nonempty
          (Novikov.baseChange (Ideal.Quotient.mk J) IA ≅
            NovikovIsocrystal.ConstIsocrystal (Λ := Λ) P) := by
  dsimp only
  let Ired := nilradical A
  let q : A →+* A ⧸ Ired := Ideal.Quotient.mk Ired
  let IA := (descentToIsocrystal.{u, u} (Λ := Λ) A).obj M
  obtain ⟨N₀, ⟨e⟩⟩ :=
    baseChange_nilradical_isocrystal_const (Λ := Λ) A M
  let G := generatorData
    q Ideal.Quotient.mk_surjective IA N₀ e
  let C := coefficientData q Ideal.Quotient.mk_surjective IA G
  have hC : ∀ i j, C.c i j ∈ RingHom.ker
      (mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
        (Ideal.Quotient.mk (nilradical A))) := by
    simpa only [q, Ired] using C.mem_ker
  let D := idealData C.c hC
  let LD := latticeData IA G.g G.span_eq_top C.c C.error_eq D
  obtain ⟨P, eP⟩ := isocrystal_const_of_positive_lattice
    IA D.J LD.L LD.error_positive
  exact ⟨D.J, D.isNilpotent, P, eP⟩

private noncomputable def descentConstIsoOfBaseChangeIsocrystalConst
    {Λ : ℝ} [Fact (Λ > 1)]
    {A : Type u} [CommRing A]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (J : Ideal A)
    (P : FiniteProjectiveModule.{u, u} (A ⧸ J))
    (e : Novikov.baseChange (Ideal.Quotient.mk J)
        ((descentToIsocrystal.{u, u} (Λ := Λ) A).obj M) ≅
      NovikovIsocrystal.ConstIsocrystal (Λ := Λ) P) :
    (vectToNovikovDescent.{0, u, u}
        (⊤ : AddSubgroup ℝ) (A ⧸ J)).obj P ≅
      M.baseChange (realCCoeffHom (Ideal.Quotient.mk J)) := by
  let qJ := Ideal.Quotient.mk J
  let MC := M.baseChange (realCCoeffHom qJ)
  let α := descentToIsocrystal_comp_vectToNovikovDescent_iso.{u, u}
    (Λ := Λ) (A := A ⧸ J)
  let β := descentToIsocrystal_baseChangeIso (Λ := Λ) qJ M
  exact (descentToIsocrystal_fullyFaithful.{u, u}
    (Λ := Λ) (A := A ⧸ J)).preimageIso
      (α.app P ≪≫ e.symm ≪≫ β)

private theorem exists_nilpotent_ideal_descent_const_aux
    {Λ : ℝ} [Fact (Λ > 1)]
    (A : Type u) [CommRing A]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A) :
    ∃ J : Ideal A, IsNilpotent J ∧
      ∃ P : FiniteProjectiveModule.{u, u} (A ⧸ J),
        Nonempty
          ((vectToNovikovDescent.{0, u, u}
              (⊤ : AddSubgroup ℝ) (A ⧸ J)).obj P ≅
            M.baseChange (realCCoeffHom (Ideal.Quotient.mk J))) := by
  obtain ⟨J, hJ, P, ⟨e⟩⟩ :=
    exists_nilpotent_ideal_isocrystal_const (Λ := Λ) A M
  exact ⟨J, hJ, P,
    ⟨descentConstIsoOfBaseChangeIsocrystalConst M J P e⟩⟩

/-- Every real Novikov descent datum becomes constant after quotienting by a
nilpotent ideal. -/
theorem exists_nilpotent_ideal_descent_const
    (A : Type u) [CommRing A]
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A) :
    ∃ J : Ideal A, IsNilpotent J ∧
      ∃ P : FiniteProjectiveModule.{u, u} (A ⧸ J),
        Nonempty
          ((vectToNovikovDescent.{0, u, u}
              (⊤ : AddSubgroup ℝ) (A ⧸ J)).obj P ≅
            M.baseChange (realCCoeffHom (Ideal.Quotient.mk J))) := by
  letI : Fact ((2 : ℝ) > 1) := ⟨by norm_num⟩
  exact exists_nilpotent_ideal_descent_const_aux (Λ := (2 : ℝ)) A M

/-- Constant real Novikov descent is an equivalence over every commutative
ring. -/
theorem vectToNovikovDescent_isEquivalence_real
    (A : Type u) [CommRing A] :
    (vectToNovikovDescent.{0, u, u}
      (⊤ : AddSubgroup ℝ) A).IsEquivalence := by
  let F := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) A
  have hFF : F.FullyFaithful :=
    vectToNovikovDescent_fullyFaithful (⊤ : AddSubgroup ℝ) A
  letI : F.Faithful := hFF.faithful
  letI : F.Full := hFF.full
  letI : F.EssSurj := by
    constructor
    intro M
    obtain ⟨J, hJ, P, e⟩ :=
      exists_nilpotent_ideal_descent_const A M
    exact novikovDescent_nilpotent A J hJ M ⟨P, e⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The bundled equivalence for constant real Novikov descent over an arbitrary
commutative ring. -/
noncomputable def vectToNovikovDescent_equivalence_real
    (A : Type u) [CommRing A] :
    FiniteProjectiveModule.{u, u} A ≌
      NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A := by
  let F := vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) A
  haveI : F.IsEquivalence :=
    vectToNovikovDescent_isEquivalence_real A
  exact F.asEquivalence

end Novikov.Descent
