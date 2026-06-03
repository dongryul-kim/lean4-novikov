import Novikov.Isocrystal.Field
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Triangularization of Novikov isocrystals over algebraically closed fields

This file proves `Prop:NovIsocGeomPt`: a Novikov isocrystal over an
algebraically closed field `K` admits a triangular basis whose diagonal
Frobenius eigenvalues are constants `c_i : Kˣ`.

Since `RealNovikovSeries K` is a field when `K` is, the underlying module of an
isocrystal is a finite-dimensional vector space, and the eigenvector
`exists_frobenius_eigenvector` lets us peel off a rank-one sub-line and induct on
the quotient.

## Main definitions / results

* `quotSemilinearEquiv`: a semilinear automorphism stabilizing a submodule
  descends to the quotient.
* `semilinear_eq_mulVec`: a semilinear endomorphism of `Fin N → R` is matrix
  multiplication on the `σ`-twisted coordinate vector.
* `triangular_aux`: the triangularization, by induction on the finrank.
* `nov_isoc_geom_pt_triangular`: the triangularization for an isocrystal.
-/

open scoped BigOperators
open TensorProduct Novikov.Miscellany Matrix

namespace Novikov

variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]
variable {K : Type*} [Field K] [IsAlgClosed K]

section Quot
variable {R : Type*} [CommRing R] {σ : R →+* R} {σ' : R →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- A semilinear automorphism `Φ` of `V` that stabilizes a submodule `L` (both
forward and backward) descends to a semilinear automorphism of `V ⧸ L`. -/
noncomputable def quotSemilinearEquiv (Φ : V ≃ₛₗ[σ] V) (L : Submodule R V)
    (hf : L ≤ Submodule.comap Φ.toLinearMap L)
    (hg : L ≤ Submodule.comap Φ.symm.toLinearMap L) :
    (V ⧸ L) ≃ₛₗ[σ] (V ⧸ L) where
  toFun := Submodule.mapQ L L Φ.toLinearMap hf
  invFun := Submodule.mapQ L L Φ.symm.toLinearMap hg
  map_add' x y := by simp
  map_smul' r x := by simp
  left_inv y := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L y
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply]; simp
  right_inv y := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L y
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply]; simp

@[simp] lemma quotSemilinearEquiv_mk (Φ : V ≃ₛₗ[σ] V) (L : Submodule R V)
    (hf : L ≤ Submodule.comap Φ.toLinearMap L)
    (hg : L ≤ Submodule.comap Φ.symm.toLinearMap L) (x : V) :
    quotSemilinearEquiv Φ L hf hg (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Φ x) := by
  change Submodule.mapQ L L Φ.toLinearMap hf (Submodule.Quotient.mk x) = _
  exact Submodule.mapQ_apply L L Φ.toLinearMap x

end Quot

section SemilinearMatrix
variable {R : Type*} [CommRing R] {σ : R →+* R} {N : ℕ}

/-- Any `σ`-semilinear endomorphism of `Fin N → R` is given by its matrix acting on
the `σ`-twisted coordinate vector. -/
lemma semilinear_eq_mulVec (Ψ : (Fin N → R) →ₛₗ[σ] (Fin N → R)) (w : Fin N → R) :
    Ψ w = (Matrix.of fun i j => Ψ (Pi.single j 1) i) *ᵥ (fun j => σ (w j)) := by
  have hw : w = ∑ j, Pi.single j (w j) := (Finset.univ_sum_single w).symm
  conv_lhs => rw [hw]
  rw [map_sum]
  funext i
  rw [Finset.sum_apply, Matrix.mulVec_eq_sum]
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hsingle : Pi.single j (w j) = w j • Pi.single j (1 : R) := by
    funext k; by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [hsingle, map_smulₛₗ]
  simp [Pi.smul_apply, mul_comm]

end SemilinearMatrix

section Triangular

/-- Triangularization induction over the finrank. -/
theorem triangular_aux :
    ∀ (n : ℕ) (V : Type*) [AddCommGroup V] [Module (RealNovikovSeries K) V]
      [Module.Finite (RealNovikovSeries K) V]
      (Φ : V ≃ₛₗ[frobeniusRingHom (Λ := Λ) (A := K)] V),
      Module.finrank (RealNovikovSeries K) V = n →
      ∃ (e : V ≃ₗ[RealNovikovSeries K] (Fin n → RealNovikovSeries K))
        (c : Fin n → Kˣ) (T : Matrix (Fin n) (Fin n) (RealNovikovSeries K)),
        (∀ i j, j < i → T i j = 0) ∧
        (∀ i, T i i = algebraMap K (RealNovikovSeries K) ((c i : K))) ∧
        (∀ x, e (Φ x) =
          T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (e x j))) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ Φ hdim
    haveI : Subsingleton V := Module.finrank_zero_iff.mp hdim
    haveI : Subsingleton (Fin 0 → RealNovikovSeries K) := by
      refine ⟨fun a b => funext (fun i => Fin.elim0 i)⟩
    refine ⟨LinearEquiv.ofSubsingleton V (Fin 0 → RealNovikovSeries K), Fin.elim0,
      0, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro x; exact funext (fun i => Fin.elim0 i)
  | succ n ih =>
    intro V _ _ _ Φ hdim
    set R := RealNovikovSeries K with hR
    -- package as isocrystal to get an eigenvector
    have hpos : 0 < Module.finrank R V := by rw [hdim]; omega
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨m, hm, c₀, hEig⟩ :
        ∃ (m : V) (_ : m ≠ 0) (c : Kˣ), Φ m = algebraMap K R ((c : K)) • m :=
      exists_frobenius_eigenvector (Λ := Λ)
        ({ M := V, F_M := Φ } : NovikovIsocrystal (Λ := Λ) K) inferInstance
    -- hEig : Φ m = algebraMap K R (c₀ : K) • m
    set a₀ := algebraMap K R ((c₀ : K)) with ha₀
    have ha₀u : IsUnit a₀ := (Units.isUnit c₀).map (algebraMap K R)
    have ha₀0 : a₀ ≠ 0 := ha₀u.ne_zero
    set L := Submodule.span R {m} with hL
    -- L is Φ- and Φ⁻¹-stable
    have hσa : frobeniusRingHom (Λ := Λ) (A := K) a₀ = a₀ := by
      rw [ha₀]; exact frobenius_algebraMap _
    have hcoef : frobeniusRingHom (Λ := Λ) (A := K) (a₀⁻¹) * a₀ = 1 := by
      rw [map_inv₀, hσa]; exact inv_mul_cancel₀ ha₀0
    have hf : L ≤ Submodule.comap Φ.toLinearMap L := by
      rw [hL, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        Submodule.mem_comap, LinearEquiv.coe_coe, hEig]
      exact (Submodule.span R {m}).smul_mem a₀ (Submodule.mem_span_singleton_self m)
    have hsymm : Φ.symm m = a₀⁻¹ • m := by
      apply Φ.injective
      rw [LinearEquiv.apply_symm_apply, map_smulₛₗ, hEig, smul_smul, hcoef, one_smul]
    have hg : L ≤ Submodule.comap Φ.symm.toLinearMap L := by
      rw [hL, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        Submodule.mem_comap, LinearEquiv.coe_coe, hsymm]
      exact (Submodule.span R {m}).smul_mem _ (Submodule.mem_span_singleton_self m)
    let Φ_W := quotSemilinearEquiv Φ L hf hg
    -- quotient has finrank n
    have hWdim : Module.finrank R (V ⧸ L) = n := by
      have hL1 : Module.finrank R ↥L = 1 := by rw [hL]; exact finrank_span_singleton hm
      have h := Submodule.finrank_quotient_add_finrank L
      rw [hL1, hdim] at h
      omega
    obtain ⟨e', c', T', htri', hdiag', hfrob'⟩ := ih (V ⧸ L) Φ_W hWdim
    -- complement and lifted basis
    obtain ⟨C, hCcompl⟩ := Submodule.exists_isCompl L
    let qE := Submodule.quotientEquivOfIsCompl L C hCcompl
    let bC : Module.Basis (Fin n) R ↥C := Module.Basis.ofEquivFun (qE.symm.trans e')
    have hli : ∀ (a : R), ∀ x ∈ C, a • m + x = 0 → a = 0 := by
      intro a x hx hsum
      have hmem_L : a • m ∈ L :=
        L.smul_mem a (by rw [hL]; exact Submodule.mem_span_singleton_self m)
      have hmem_C : a • m ∈ C := by
        rw [eq_neg_of_add_eq_zero_left hsum]; exact C.neg_mem hx
      have hzero : a • m = 0 := by
        have hmem : a • m ∈ L ⊓ C := Submodule.mem_inf.mpr ⟨hmem_L, hmem_C⟩
        rw [disjoint_iff.mp hCcompl.disjoint] at hmem
        exact (Submodule.mem_bot R).mp hmem
      rcases smul_eq_zero.mp hzero with h | h
      · exact h
      · exact absurd h hm
    have hsp : ∀ (z : V), ∃ a : R, z + a • m ∈ C := by
      intro z
      have hz : z ∈ L ⊔ C := by rw [hCcompl.sup_eq_top]; exact Submodule.mem_top
      rw [Submodule.mem_sup] at hz
      obtain ⟨l, hl, cc, hcc, hzeq⟩ := hz
      rw [hL, Submodule.mem_span_singleton] at hl
      obtain ⟨bb, hbb⟩ := hl
      refine ⟨-bb, ?_⟩
      have hcceq : z + (-bb) • m = cc := by
        rw [← hzeq, ← hbb, neg_smul]; abel
      rw [hcceq]; exact hcc
    let b : Module.Basis (Fin (n+1)) R V := Module.Basis.mkFinCons m bC hli hsp
    let c : Fin (n+1) → Kˣ := Fin.cons c₀ c'
    let T : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j => b.equivFun (Φ (b j)) i
    -- basis evaluation facts
    have he_bj : ∀ j : Fin (n+1), b.equivFun (b j) = (Pi.single j (1:R) : Fin (n+1) → R) := by
      intro j; funext k
      rw [Module.Basis.equivFun_self, Pi.single_apply]
      by_cases h : j = k <;> simp [h, eq_comm]
    have he_symm : ∀ j : Fin (n+1),
        b.equivFun.symm (Pi.single j (1:R) : Fin (n+1) → R) = b j := by
      intro j; rw [← he_bj j, b.equivFun.symm_apply_apply]
    have hb0 : b 0 = m := by
      change (Module.Basis.mkFinCons m bC hli hsp) 0 = m
      rw [Module.Basis.coe_mkFinCons]; exact Fin.cons_zero _ _
    have hbsucc : ∀ i : Fin n, b i.succ = (bC i : V) := by
      intro i
      change (Module.Basis.mkFinCons m bC hli hsp) i.succ = (bC i : V)
      rw [Module.Basis.coe_mkFinCons]; simp [Fin.cons_succ]
    have hπb0 : (Submodule.Quotient.mk (b 0) : V ⧸ L) = 0 := by
      rw [hb0, Submodule.Quotient.mk_eq_zero, hL]
      exact Submodule.mem_span_singleton_self m
    have hπbsucc : ∀ i : Fin n,
        (Submodule.Quotient.mk (b i.succ) : V ⧸ L) = e'.symm (Pi.single i 1) := by
      intro i
      have hmk : (Submodule.Quotient.mk (b i.succ) : V ⧸ L) = qE.symm (bC i) := by
        rw [hbsucc]
        exact (Submodule.quotientEquivOfIsCompl_symm_apply L C hCcompl (bC i)).symm
      rw [hmk]
      have hbCi : bC i = qE (e'.symm (Pi.single i 1)) := by
        change (Module.Basis.ofEquivFun (qE.symm.trans e')) i = qE (e'.symm (Pi.single i 1))
        rw [Module.Basis.coe_ofEquivFun]
        change (qE.symm.trans e').symm (Pi.single i 1) = qE (e'.symm (Pi.single i 1))
        simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply]
      rw [hbCi, qE.symm_apply_apply]
    -- linking the (k+1)-st coordinate of `b.equivFun` to the k-th coordinate of `e' ∘ π`
    have hlink : ∀ (x : V) (k : Fin n),
        b.equivFun x k.succ = e' (Submodule.Quotient.mk x) k := by
      intro x k
      have hmap : ((LinearMap.proj k.succ : (Fin (n+1) → R) →ₗ[R] R).comp
            b.equivFun.toLinearMap : V →ₗ[R] R)
          = (LinearMap.proj k : (Fin n → R) →ₗ[R] R).comp (e'.toLinearMap.comp L.mkQ) := by
        apply Module.Basis.ext b
        intro j
        simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe,
          Submodule.mkQ_apply]
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
        · rw [he_bj 0, hπb0, map_zero, Pi.zero_apply, Pi.single_apply,
            if_neg (Fin.succ_ne_zero k)]
        · rw [he_bj i.succ, hπbsucc i, LinearEquiv.apply_symm_apply, Pi.single_apply,
            Pi.single_apply]
          by_cases h : i = k
          · subst h; simp
          · simp [Fin.succ_inj]
      have := LinearMap.congr_fun hmap x
      simpa only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe,
        Submodule.mkQ_apply] using this
    -- column j ≥ 1 of the Frobenius matrix
    have hcol : ∀ (j' i' : Fin n), b.equivFun (Φ (b j'.succ)) i'.succ = T' i' j' := by
      intro j' i'
      rw [hlink (Φ (b j'.succ)) i',
        show (Submodule.Quotient.mk (Φ (b j'.succ)) : V ⧸ L)
          = Φ_W (Submodule.Quotient.mk (b j'.succ)) from
          (quotSemilinearEquiv_mk Φ L hf hg (b j'.succ)).symm,
        hπbsucc j', hfrob' (e'.symm (Pi.single j' 1)), LinearEquiv.apply_symm_apply]
      have hσsingle : (fun j => frobeniusRingHom (Λ := Λ) (A := K)
            ((Pi.single j' (1:R) : Fin n → R) j)) = (Pi.single j' (1:R) : Fin n → R) := by
        funext j; simp only [Pi.single_apply]; by_cases h : j = j' <;> simp [h]
      rw [hσsingle]
      change (T' i') ⬝ᵥ (Pi.single j' (1:R) : Fin n → R) = T' i' j'
      rw [dotProduct_single, mul_one]
    -- column 0 of the Frobenius matrix
    have hcol0 : ∀ i : Fin (n+1),
        b.equivFun (Φ (b 0)) i = a₀ * (Pi.single (0 : Fin (n+1)) (1:R) : Fin (n+1) → R) i := by
      intro i
      have h1 : Φ (b 0) = a₀ • b 0 := by rw [hb0, hEig]
      rw [h1, map_smul, Pi.smul_apply, smul_eq_mul, he_bj 0]
    have hc0 : c 0 = c₀ := Fin.cons_zero _ _
    have hcs : ∀ i' : Fin n, c i'.succ = c' i' := fun i' => Fin.cons_succ _ _ _
    refine ⟨b.equivFun, c, T, ?_, ?_, ?_⟩
    · -- triangular
      intro i j hji
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · exact absurd hji (by simp)
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · change b.equivFun (Φ (b 0)) i'.succ = 0
          rw [hcol0 i'.succ, Pi.single_apply, if_neg (Fin.succ_ne_zero i'), mul_zero]
        · change b.equivFun (Φ (b j'.succ)) i'.succ = 0
          rw [hcol j' i']
          exact htri' i' j' (Fin.succ_lt_succ_iff.mp hji)
    · -- diagonal
      intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · change b.equivFun (Φ (b 0)) 0 = algebraMap K R ((c 0 : K))
        rw [hcol0 0, Pi.single_eq_same, mul_one, hc0]
      · change b.equivFun (Φ (b i'.succ)) i'.succ = algebraMap K R ((c i'.succ : K))
        rw [hcol i' i', hdiag' i', hcs i']
    · -- frobenius
      intro x
      let Ψ : (Fin (n+1) → R) →ₛₗ[frobeniusRingHom (Λ := Λ) (A := K)] (Fin (n+1) → R) :=
        ((b.equivFun.symm.trans Φ).trans b.equivFun).toLinearMap
      have hΨx : Ψ (b.equivFun x) = b.equivFun (Φ x) := by
        change b.equivFun (Φ (b.equivFun.symm (b.equivFun x))) = b.equivFun (Φ x)
        rw [b.equivFun.symm_apply_apply]
      have hΨcol : ∀ j, Ψ (Pi.single j 1) = b.equivFun (Φ (b j)) := by
        intro j
        change b.equivFun (Φ (b.equivFun.symm (Pi.single j 1))) = b.equivFun (Φ (b j))
        rw [he_symm j]
      have hmatrix : (Matrix.of fun i j => Ψ (Pi.single j 1) i) = T := by
        funext i j
        change Ψ (Pi.single j 1) i = b.equivFun (Φ (b j)) i
        rw [hΨcol j]
      have hΨ := semilinear_eq_mulVec Ψ (b.equivFun x)
      rw [hΨx] at hΨ
      rw [hΨ, hmatrix]

open NovikovIsocrystal in
/-- **Triangularization of a Novikov isocrystal over an algebraically closed
field** (`Prop:NovIsocGeomPt`). There is a coordinate equivalence
`I.M ≃ₗ (Fin n → R)`, scalars `c i : Kˣ`, and an upper-triangular matrix `T` with
diagonal `algebraMap (c i)` so that the Frobenius is `v ↦ T *ᵥ (σ ∘ v)`. -/
theorem nov_isoc_geom_pt_triangular (I : NovikovIsocrystal (Λ := Λ) K) :
    ∃ (n : ℕ) (e : I.M ≃ₗ[RealNovikovSeries K] (Fin n → RealNovikovSeries K))
      (c : Fin n → Kˣ) (T : Matrix (Fin n) (Fin n) (RealNovikovSeries K)),
      (∀ i j, j < i → T i j = 0) ∧
      (∀ i, T i i = algebraMap K (RealNovikovSeries K) ((c i : K))) ∧
      (∀ x, e (I.F_M x) =
        T *ᵥ (fun j => frobeniusRingHom (Λ := Λ) (A := K) (e x j))) :=
  ⟨Module.finrank (RealNovikovSeries K) I.M,
    triangular_aux _ I.M I.F_M rfl⟩

end Triangular

end Novikov
