import Novikov.Isocrystal.Field.Prep
import Novikov.Isocrystal.Field.Contraction
import Novikov.Isocrystal.Constant
import Novikov.Series.Field

/-!
# Existence of Frobenius eigenvectors over algebraically closed fields

This file proves that if `K` is an algebraically closed field and `M` is a
nonzero Novikov isocrystal over `K`, then there exists a nonzero element
`m ∈ M` and `c ∈ Kˣ` satisfying `F_M(m) = c • m`.

## Main results

* `exists_frobenius_eigenvector`: For any nonzero Novikov isocrystal `M` over an
  algebraically closed field `K`, there exists a nonzero `m : M.M` and `c : Kˣ`
  such that `M.F_M m = (algebraMap K (RealNovikovSeries K) (c : K)) • m`.
-/

open scoped BigOperators
open Filter Topology

namespace Novikov
open TensorProduct Novikov.Miscellany
variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]

section Field
variable {K : Type*} [Field K] [IsAlgClosed K]

open NovikovIsocrystal

/-- A nonzero Novikov isocrystal over an algebraically closed field admits a
nonzero Frobenius eigenvector with eigenvalue a constant scalar. -/
theorem exists_frobenius_eigenvector (M : NovikovIsocrystal (Λ := Λ) K) (hM_nontriv : Nontrivial M.M) :
    ∃ (m : M.M) (_ : m ≠ 0) (c : Kˣ),
    M.F_M m = (algebraMap K (RealNovikovSeries K) (c : K)) • m := by
  -- Pick a nonzero element m₀
  have hm0_exists : ∃ m : M.M, m ≠ 0 := by
    rcases exists_pair_ne M.M with ⟨a, b, h_ne⟩
    by_cases ha0 : a = 0
    · refine ⟨b, ?_⟩; rw [ha0] at h_ne; exact h_ne.symm
    · exact ⟨a, ha0⟩
  rcases hm0_exists with ⟨m0, hm0⟩
  -- Pre-prove properties of iterated Frobenius
  have h_F_iter_injective (k : ℕ) : Function.Injective (M.F_M^[k]) :=
    Function.Injective.iterate M.F_M.injective k
  have h_F_iter_zero (k : ℕ) : (M.F_M^[k] 0 : M.M) = 0 :=
    Function.iterate_fixed (map_zero M.F_M) k
  -- Find the linear relation
  let φ : M.M → M.M := fun x => M.F_M x
  rcases exists_linear_relation_of_finite_module (RealNovikovSeries K) M.M φ m0 hm0 with ⟨n, hn, a, h_indep, h_rel⟩
  have h_nonzero_a : ∃ i, a i ≠ 0 := by
    by_contra! h_all
    have hzero : M.F_M^[n] m0 = 0 := by
      calc
        M.F_M^[n] m0 = φ^[n] m0 := rfl
        _ = ∑ i : Fin n, a i • φ^[i] m0 := h_rel
        _ = ∑ i : Fin n, (0 : RealNovikovSeries K) • φ^[i] m0 := Finset.sum_congr rfl (fun i _ => by rw [h_all i])
        _ = 0 := by simp
    exact hm0 (h_F_iter_injective n (by rw [hzero, h_F_iter_zero]))
  -- Normalize coefficients
  rcases normalize_coeffs_by_scaling (Λ := Λ) n hn a h_nonzero_a with ⟨r, a', h_filt, h_const_term, h_a'_eq⟩
  rcases h_const_term with ⟨j, hj_const⟩
  -- Scale the starting vector by t^r
  let t_pow_r : RealNovikovSeries K :=
    novikovMonomial (1 : K) (fun _ : Unit => ⟨r, AddSubgroup.mem_top _⟩)
  have ht_r_ne_zero : t_pow_r ≠ 0 := by
    dsimp [t_pow_r]
    intro h
    have hval := congrArg (fun f : RealNovikovSeries K =>
      f (fun _ : Unit => ⟨r, AddSubgroup.mem_top _⟩)) h
    simp [novikovMonomial] at hval
  let m : M.M := t_pow_r • m0
  have hm_ne_zero : m ≠ 0 := by
    dsimp [m]
    intro h
    rcases smul_eq_zero.mp h with (ht | hm0')
    · exact ht_r_ne_zero ht
    · exact hm0 hm0'
  -- Find c ∈ K^× and a fixed point b of the contraction operator
  haveI : Fact (Λ > 0) := ⟨by linarith [hΛ1.out]⟩
  -- Find c ∈ Kˣ from constant terms
  let ā (i : Fin n) : K := a' i 0
  have h_ā_nonzero : ∃ i, ā i ≠ 0 := by exact ⟨j, hj_const⟩
  rcases exists_nonzero_solution_of_algClosed hn ā h_ā_nonzero with ⟨c, hc_eq⟩
  let F : RealNovikovSeries K →+* RealNovikovSeries K :=
    Novikov.frobeniusRingHom (Λ := Λ) (A := K)
  let t_pow_d (d : ℝ) : RealNovikovSeries K :=
    novikovMonomial (1 : K) (fun _ : Unit => ⟨d, AddSubgroup.mem_top _⟩)
  have hF_t_pow_d (d : ℝ) (k : ℕ) : F^[k] (t_pow_d d) = t_pow_d (Λ ^ k * d) := by
    simpa [F, t_pow_d, frobeniusRingHom] using frobenius_iterate_monomial_one d k
  have h_t_pow_d_mul (d₁ d₂ : ℝ) : t_pow_d d₁ * t_pow_d d₂ = t_pow_d (d₁ + d₂) := by
    dsimp [t_pow_d, novikovMul]
    simpa using novikovSeriesMul_monomial (1 : K) (1 : K) AddMonoidHom.mul
      (fun _ : Unit => ⟨d₁, AddSubgroup.mem_top _⟩)
      (fun _ : Unit => ⟨d₂, AddSubgroup.mem_top _⟩)
  have h_t_pow_d_inv (d : ℝ) : t_pow_d d * t_pow_d (-d) = 1 := by
    calc
      t_pow_d d * t_pow_d (-d) = t_pow_d (d + (-d)) := h_t_pow_d_mul d (-d)
      _ = t_pow_d 0 := by ring_nf
      _ = (1 : RealNovikovSeries K) := rfl
  have h_t_pow_r : t_pow_r = t_pow_d r := rfl
  -- Semilinearity: F_M^[k] (s • x) = (F^[k] s) • (F_M^[k] x)
  have h_FM_iter_smul (s : RealNovikovSeries K) (x : M.M) (k : ℕ) :
      M.F_M^[k] (s • x) = (F^[k] s) • (M.F_M^[k] x) := by
    induction k generalizing s x with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [ih s x, M.F_M.map_smulₛₗ]
  -- Relate F_M^[n] m to Σ a'ᵢ • F_M^[i] m
  have h_linrel_scaled : (M.F_M^[n] m) = ∑ i : Fin n, a' i • (M.F_M^[i] m) := by
    calc
      (M.F_M^[n] m) = (M.F_M^[n] (t_pow_r • m0)) := rfl
      _ = M.F_M^[n] (t_pow_d r • m0) := by rw [h_t_pow_r]
      _ = (F^[n] (t_pow_d r)) • (M.F_M^[n] m0) := h_FM_iter_smul (t_pow_d r) m0 n
      _ = (t_pow_d (Λ ^ n * r)) • (M.F_M^[n] m0) := by rw [hF_t_pow_d r n]
      _ = (t_pow_d (Λ ^ n * r)) • (∑ i : Fin n, a i • (M.F_M^[i] m0)) := by rw [h_rel]
      _ = ∑ i : Fin n, (t_pow_d (Λ ^ n * r)) • (a i • (M.F_M^[i] m0)) := by
        rw [Finset.smul_sum]
      _ = ∑ i : Fin n, a i • ((t_pow_d (Λ ^ n * r)) • (M.F_M^[i] m0)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [smul_smul, mul_comm]
      _ = ∑ i : Fin n, a' i • (M.F_M^[i] m) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        calc
          a i • ((t_pow_d (Λ ^ n * r)) • (M.F_M^[i] m0)) =
              (a i * t_pow_d (Λ ^ n * r)) • (M.F_M^[i] m0) := by simp [smul_smul]
          _ = (t_pow_d (r * (Λ ^ n - Λ ^ (i.val : ℕ))) * a i * t_pow_d (Λ ^ (i.val : ℕ) * r)) •
              (M.F_M^[i] m0) := by
            have hfactor : t_pow_d (Λ ^ n * r) =
                t_pow_d (r * (Λ ^ n - Λ ^ (i.val : ℕ))) * t_pow_d (Λ ^ (i.val : ℕ) * r) := by
              calc
                t_pow_d (Λ ^ n * r) = t_pow_d (r * (Λ ^ n - Λ ^ (i.val : ℕ)) + Λ ^ (i.val : ℕ) * r) := by ring_nf
                _ = t_pow_d (r * (Λ ^ n - Λ ^ (i.val : ℕ))) *
                    t_pow_d (Λ ^ (i.val : ℕ) * r) := by rw [h_t_pow_d_mul]
            rw [hfactor]
            ring_nf
          _ = a' i • ((F^[i.val] (t_pow_d r)) • (M.F_M^[i] m0)) := by
            rw [h_a'_eq i, hF_t_pow_d r i.val]
            simp [t_pow_d, smul_smul, mul_comm, mul_left_comm]
          _ = a' i • (M.F_M^[i] (t_pow_d r • m0)) := by
            rw [h_FM_iter_smul (t_pow_d r) m0 i.val]
          _ = a' i • (M.F_M^[i] m) := by rw [← h_t_pow_r]
  -- Show that the vectors F_M^[i] m are linearly independent
  have h_nonzero_s (i : Fin n) : F^[(i : ℕ)] (t_pow_d r) ≠ 0 := by
    rw [hF_t_pow_d r (i : ℕ)]
    dsimp [t_pow_d]
    intro h
    have hval := congrArg (fun f : RealNovikovSeries K =>
      f (fun _ : Unit => ⟨Λ ^ (i : ℕ) * r, AddSubgroup.mem_top _⟩)) h
    simp [novikovMonomial] at hval
  have h_indep_scaled :
      LinearIndependent (RealNovikovSeries K) (fun (i : Fin n) => (M.F_M^[i] m)) := by
    have h_eq_scaled (i : Fin n) : M.F_M^[i] m = (F^[(i : ℕ)] (t_pow_d r)) • (M.F_M^[i] m0) := by
      dsimp [m]
      rw [h_t_pow_r]
      rw [h_FM_iter_smul (t_pow_d r) m0 (i : ℕ)]
    intro l₁ l₂ hl_eq
    have hl_sum_eq : (∑ i ∈ l₁.support, l₁ i • (M.F_M^[i] m)) =
                    (∑ i ∈ l₂.support, l₂ i • (M.F_M^[i] m)) := by
      simpa [Finsupp.linearCombination_apply] using hl_eq
    -- Rewrite scaled vectors as scalar multiples of original
    have hl_sum_eq' : (∑ i ∈ l₁.support, (l₁ i * (F^[(i : ℕ)] (t_pow_d r))) • (M.F_M^[i] m0)) =
                     (∑ i ∈ l₂.support, (l₂ i * (F^[(i : ℕ)] (t_pow_d r))) • (M.F_M^[i] m0)) := by
      simpa [h_eq_scaled, smul_smul] using hl_sum_eq
    -- Build Finsupps with coefficients (l_j i * s_i)
    let l₁' : Fin n →₀ RealNovikovSeries K :=
      Finsupp.onFinset Finset.univ (fun i => l₁ i * (F^[(i : ℕ)] (t_pow_d r)))
        (by intro i hi; exact Finset.mem_univ _)
    let l₂' : Fin n →₀ RealNovikovSeries K :=
      Finsupp.onFinset Finset.univ (fun i => l₂ i * (F^[(i : ℕ)] (t_pow_d r)))
        (by intro i hi; exact Finset.mem_univ _)
    have h_lc_eq : Finsupp.linearCombination (RealNovikovSeries K)
        (fun (i : Fin n) => M.F_M^[i] m0) l₁' =
        Finsupp.linearCombination (RealNovikovSeries K)
        (fun (i : Fin n) => M.F_M^[i] m0) l₂' := by
      have h_support₁ : l₁'.support = l₁.support := by
        ext i
        simp [l₁', Finsupp.onFinset_apply, Finsupp.mem_support_iff, h_nonzero_s i]
      have h_support₂ : l₂'.support = l₂.support := by
        ext i
        simp [l₂', Finsupp.onFinset_apply, Finsupp.mem_support_iff, h_nonzero_s i]
      calc
        Finsupp.linearCombination (RealNovikovSeries K)
            (fun (i : Fin n) => M.F_M^[i] m0) l₁'
            = l₁'.sum (fun i a => a • (M.F_M^[i] m0)) := rfl
        _ = ∑ i ∈ l₁'.support, l₁' i • (M.F_M^[i] m0) := by rw [Finsupp.sum]
        _ = ∑ i ∈ l₁.support, l₁' i • (M.F_M^[i] m0) := by rw [h_support₁]
        _ = ∑ i ∈ l₁.support, (l₁ i * (F^[(i : ℕ)] (t_pow_d r))) • (M.F_M^[i] m0) := by
          simp [l₁', Finsupp.onFinset_apply]
        _ = ∑ i ∈ l₂.support, (l₂ i * (F^[(i : ℕ)] (t_pow_d r))) • (M.F_M^[i] m0) := hl_sum_eq'
        _ = ∑ i ∈ l₂.support, l₂' i • (M.F_M^[i] m0) := by
          simp [l₂', Finsupp.onFinset_apply]
        _ = ∑ i ∈ l₂'.support, l₂' i • (M.F_M^[i] m0) := by rw [h_support₂]
        _ = l₂'.sum (fun i a => a • (M.F_M^[i] m0)) := by rw [Finsupp.sum]
        _ = Finsupp.linearCombination (RealNovikovSeries K)
            (fun (i : Fin n) => M.F_M^[i] m0) l₂' := rfl
    have h_coeffs_eq : l₁' = l₂' := h_indep h_lc_eq
    ext i d
    have h_eq_at_i : l₁ i * (F^[(i : ℕ)] (t_pow_d r)) = l₂ i * (F^[(i : ℕ)] (t_pow_d r)) := by
      have := congrArg (fun f : Fin n →₀ RealNovikovSeries K => f i) h_coeffs_eq
      simpa [l₁', l₂', Finsupp.onFinset_apply, Finset.mem_univ] using this
    have h_sub_series : (l₁ i - l₂ i) * (F^[(i : ℕ)] (t_pow_d r)) = 0 := by
      rw [sub_mul, h_eq_at_i, sub_self]
    -- F^[i] (t_pow_d r) is a unit (it's a monomial)
    have h_s_unit : IsUnit (F^[(i : ℕ)] (t_pow_d r)) := by
      rw [hF_t_pow_d r (i : ℕ)]
      have h_inv : t_pow_d (Λ ^ (i : ℕ) * r) * t_pow_d (-(Λ ^ (i : ℕ) * r)) = 1 :=
        h_t_pow_d_inv (Λ ^ (i : ℕ) * r)
      exact ⟨⟨t_pow_d (Λ ^ (i : ℕ) * r), t_pow_d (-(Λ ^ (i : ℕ) * r)),
        h_inv, by rw [mul_comm, h_inv]⟩, rfl⟩
    rcases h_s_unit with ⟨u, hu⟩
    have h_sub_series' : (l₁ i - l₂ i) * (u : RealNovikovSeries K) = 0 := by
      rw [hu]; exact h_sub_series
    have hzero : l₁ i - l₂ i = 0 := by
      calc
        l₁ i - l₂ i = (l₁ i - l₂ i) * 1 := by simp
        _ = (l₁ i - l₂ i) * ((u : RealNovikovSeries K) * (u⁻¹ : RealNovikovSeries K)) := by simp
        _ = ((l₁ i - l₂ i) * (u : RealNovikovSeries K)) * (u⁻¹ : RealNovikovSeries K) := by ring
        _ = 0 * (u⁻¹ : RealNovikovSeries K) := by rw [h_sub_series']
        _ = 0 := by simp
    -- Apply the series equality at the point d
    apply sub_eq_zero.mp
    simpa [Pi.sub_apply, Pi.zero_apply] using congrArg (fun f : RealNovikovSeries K => f d) hzero
  -- Define the contraction operator g and prove g(1) ∈ filtration 0, (g 1)₀ = 1
  let g := contractionOperator Λ K n a' c
  have h_g1_filt0 : g 1 ∈ filtration (⊤ : AddSubgroup ℝ) K 0 := by
    dsimp [g, contractionOperator]
    have h1_filt0 : (1 : RealNovikovSeries K) ∈ filtration (⊤ : AddSubgroup ℝ) K 0 := by
      simpa using algMap_filt0 (1 : K)
    have h_term (i : Fin n) :
        (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
        (F^[n - i.val] 1) * (F^[n - 1 - i.val] (a' i)) ∈
        filtration (⊤ : AddSubgroup ℝ) K 0 := by
      have h_cinv : (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) ∈
          filtration (⊤ : AddSubgroup ℝ) K 0 :=
        algMap_pow_filt0 ((c : K)⁻¹) (n - i.val)
      have h_F1 : F^[n - i.val] 1 ∈ filtration (⊤ : AddSubgroup ℝ) K 0 :=
        frobeniusRingHom_iter_filt0 (Λ := Λ) (K := K) 1 h1_filt0 (n - i.val)
      have h_Fa : F^[n - 1 - i.val] (a' i) ∈ filtration (⊤ : AddSubgroup ℝ) K 0 :=
        frobeniusRingHom_iter_filt0 (Λ := Λ) (K := K) (a' i) (h_filt i) (n - 1 - i.val)
      have h_AB : (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
          (F^[n - i.val] 1) ∈ filtration (⊤ : AddSubgroup ℝ) K 0 := by
        have htemp := filtration_mul (D₁ := 0) (D₂ := 0) (Set.mul_mem_mul h_cinv h_F1)
        refine filtration_mono (D₁ := 0) (D₂ := 0 + 0) (by norm_num) htemp
      have htemp := filtration_mul (D₁ := 0) (D₂ := 0) (Set.mul_mem_mul h_AB h_Fa)
      refine filtration_mono (D₁ := 0) (D₂ := 0 + 0) (by norm_num) htemp
    refine AddSubgroup.sum_mem (filtration (⊤ : AddSubgroup ℝ) K 0)
      (t := Finset.univ) (fun i hi => h_term i)
  -- Constant term of g(1) equals 1
  have h_const_g1 : (g 1) 0 = 1 := by
    have h_eval_sum (s : Finset (Fin n)) (f : Fin n → RealNovikovSeries K) :
        (∑ i ∈ s, f i) 0 = ∑ i ∈ s, (f i 0) := by
      refine Finset.induction_on s (by simp) (fun i s his ih => ?_)
      simp
    have h_one_val : (1 : RealNovikovSeries K) 0 = (1 : K) := by
      simpa using algMap_val0 (1 : K)
    have h_sum_val : (g 1) 0 = ∑ i : Fin n, (((c : K)⁻¹) ^ (n - i.val) * (a' i 0)) := by
      dsimp [g, contractionOperator]
      rw [h_eval_sum Finset.univ (fun i => (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
          (F^[n - i.val] 1) * (F^[n - 1 - i.val] (a' i)))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      calc
        ((algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
            (F^[n - i.val] 1) * (F^[n - 1 - i.val] (a' i))) 0 =
          (((algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
            (F^[n - i.val] 1)) * (F^[n - 1 - i.val] (a' i))) 0 := rfl
        _ = ((algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
            (F^[n - i.val] 1)) 0 * ((F^[n - 1 - i.val] (a' i)) 0) :=
          filtration_zero_mul_val (by
            have htemp := filtration_mul (D₁ := 0) (D₂ := 0)
              (Set.mul_mem_mul (algMap_pow_filt0 ((c : K)⁻¹) (n - i.val))
                (frobeniusRingHom_iter_filt0 (Λ := Λ) (K := K) 1 (by simpa using algMap_filt0 (1 : K)) (n - i.val)))
            exact filtration_mono (D₁ := 0) (D₂ := 0 + 0) (by norm_num) htemp)
          (frobeniusRingHom_iter_filt0 (Λ := Λ) (K := K) (a' i) (h_filt i) (n - 1 - i.val))
        _ = (((algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val)) 0 *
            ((F^[n - i.val] 1) 0)) * ((F^[n - 1 - i.val] (a' i)) 0) := by
          rw [filtration_zero_mul_val (algMap_pow_filt0 ((c : K)⁻¹) (n - i.val))
            (frobeniusRingHom_iter_filt0 (Λ := Λ) (K := K) 1 (by simpa using algMap_filt0 (1 : K)) (n - i.val))]
        _ = (((c : K)⁻¹) ^ (n - i.val) * (1 : K)) * (a' i 0) := by
          rw [algMap_pow_val0 ((c : K)⁻¹) (n - i.val),
            frobeniusRingHom_iterate_apply_zero (Λ := Λ) (A := K) 1 (n - i.val),
            frobeniusRingHom_iterate_apply_zero (Λ := Λ) (A := K) (a' i) (n - 1 - i.val),
            h_one_val, mul_one]
        _ = (((c : K)⁻¹) ^ (n - i.val) * (a' i 0)) := by simp
    rw [h_sum_val]
    have h_c_ne_zero : (c : K) ≠ 0 := Units.ne_zero c
    have h_c_pow_ne_zero : (c : K)^n ≠ 0 := pow_ne_zero n h_c_ne_zero
    apply mul_right_cancel₀ h_c_pow_ne_zero
    calc
      (∑ i : Fin n, (((c : K)⁻¹) ^ (n - i.val) * (a' i 0))) * (c : K)^n
          = ∑ i : Fin n, (((c : K)⁻¹) ^ (n - i.val) * (a' i 0) * (c : K)^n) := by
        rw [Finset.sum_mul]
      _ = ∑ i : Fin n, ((a' i 0) * (((c : K)⁻¹) ^ (n - i.val) * (c : K)^n)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
      _ = ∑ i : Fin n, ((a' i 0) * (c : K)^(i.val)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have h_pow : ((c : K)⁻¹) ^ (n - i.val) * (c : K)^n = (c : K)^(i.val) := by
          calc
            ((c : K)⁻¹) ^ (n - i.val) * (c : K)^n
                = ((c : K)⁻¹) ^ (n - i.val) * ((c : K)^(n - i.val) * (c : K)^(i.val)) := by
              rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt i.is_lt)]
            _ = (((c : K)⁻¹) ^ (n - i.val) * (c : K)^(n - i.val)) * (c : K)^(i.val) := by ring
            _ = 1 * (c : K)^(i.val) := by simp [h_c_ne_zero]
            _ = (c : K)^(i.val) := by simp
        rw [h_pow]
      _ = (c : K)^n := by
        simpa [ā] using hc_eq.symm
      _ = 1 * (c : K)^n := by simp
  by_cases h_g1_eq_one : g 1 = 1
  · -- Fixed point found: b = 1
    have h_eig := exists_frobenius_eigenvector_of_fixed_point Λ K M m hm_ne_zero n hn a' c 1
      h_linrel_scaled h_indep_scaled (by simpa [g] using h_g1_eq_one) (by simp)
    rcases h_eig with ⟨m', hm', h_eq⟩
    exact ⟨m', hm', c, h_eq⟩
  · have h_diff_ne_zero : g 1 - 1 ≠ 0 := sub_ne_zero.mpr h_g1_eq_one
    -- g(1) - 1 is "positive" (vanishes on degrees ≤ 0)
    have h_diff_pos : IsPositive (g 1 - 1) := by
      intro d hd_le
      rcases lt_or_eq_of_le hd_le with (hlt | heq)
      · -- (d () : ℝ) < 0
        have h_g1_d : (g 1) d = 0 := h_g1_filt0 d hlt
        have h_one_d : (1 : RealNovikovSeries K) d = 0 := by
          simpa using (algMap_filt0 (1 : K)) d hlt
        simp [h_g1_d, h_one_d, Pi.sub_apply]
      · -- (d () : ℝ) = 0
        have hd0 : d = 0 := by
          ext x; fin_cases x; simpa using heq
        subst hd0
        have h_one_0 : (1 : RealNovikovSeries K) 0 = (1 : K) := by
          simpa using algMap_val0 (1 : K)
        simp [h_const_g1, h_one_0, Pi.sub_apply]
    -- ε := minDegree (g 1 - 1) > 0
    set ε := (minDegree (g 1 - 1) () : ℝ) with hε_def
    have hε_pos : 0 < ε :=
      support_has_min_pos (g 1 - 1) h_diff_ne_zero h_diff_pos
    -- Key: g(1) - 1 ∈ filtration ε
    have h_diff_filt_ε : g 1 - 1 ∈ filtration (⊤ : AddSubgroup ℝ) K ε := by
      intro d hd
      -- hd : (d () : ℝ) < ε = minDegree (g 1 - 1)
      apply minDegree_lt_apply (g 1 - 1) h_diff_ne_zero d
      simpa [hε_def] using hd
    -- Apply contractionOperator_fixed
    have h_fixed := contractionOperator_fixed n a' h_filt c h_g1_filt0 h_const_g1
    rcases h_fixed with ⟨b, h_gb, hb_zero⟩
    have hb_ne_zero : b ≠ 0 := by
      intro hb0; have : b 0 = 0 := by simp [hb0]
      rw [this] at hb_zero; exact zero_ne_one hb_zero
    have h_eig := exists_frobenius_eigenvector_of_fixed_point Λ K M m hm_ne_zero n hn a' c b
      h_linrel_scaled h_indep_scaled h_gb hb_ne_zero
    rcases h_eig with ⟨m', hm', h_eq⟩
    exact ⟨m', hm', c, h_eq⟩

end Field

section RankOne
variable {K : Type*} [CommRing K]

namespace NovikovIsocrystal

/-- The rank-one twisted Novikov isocrystal `(K((t)), c · F)`: its underlying
module is `RealNovikovSeries K` and its Frobenius is
`x ↦ algebraMap K _ (c : K) * frobenius x`. -/
noncomputable def rankOneTwist (c : Kˣ) : NovikovIsocrystal (Λ := Λ) K where
  M := RealNovikovSeries K
  F_M :=
    { toFun := fun x =>
        algebraMap K (RealNovikovSeries K) (c : K) * frobeniusRingHom (Λ := Λ) x
      invFun := fun y =>
        algebraMap K (RealNovikovSeries K) ((c⁻¹ : Kˣ) : K) * frobeniusRingHomInv (Λ := Λ) y
      map_add' := fun x y => by rw [map_add, mul_add]
      map_smul' := fun s x => by
        simp only [smul_eq_mul, map_mul]
        ring
      left_inv := fun x => by
        dsimp only
        rw [map_mul,
          show frobeniusRingHomInv (Λ := Λ) (algebraMap K (RealNovikovSeries K) (c : K))
            = algebraMap K (RealNovikovSeries K) (c : K) from frobenius_algebraMap _,
          RingHomInvPair.comp_apply_eq (σ := frobeniusRingHom (Λ := Λ) (A := K)),
          ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      right_inv := fun y => by
        dsimp only
        rw [map_mul,
          show frobeniusRingHom (Λ := Λ) (A := K)
              (algebraMap K (RealNovikovSeries K) ((c⁻¹ : Kˣ) : K))
            = algebraMap K (RealNovikovSeries K) ((c⁻¹ : Kˣ) : K) from frobenius_algebraMap _,
          RingHomInvPair.comp_apply_eq₂ (σ := frobeniusRingHom (Λ := Λ) (A := K)),
          ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul] }

/-- Formula for the Frobenius on the rank-one twisted isocrystal. -/
lemma rankOneTwist_F_M_apply (c : Kˣ) (x : RealNovikovSeries K) :
    (rankOneTwist (Λ := Λ) c).F_M x =
      algebraMap K (RealNovikovSeries K) (c : K) * frobeniusRingHom (Λ := Λ) x :=
  rfl

/-- For `c = 1`, the rank-one twisted Frobenius is the ordinary Frobenius. -/
lemma rankOneTwist_one_F_M_apply (x : RealNovikovSeries K) :
    (rankOneTwist (Λ := Λ) (1 : Kˣ)).F_M x = frobeniusRingHom (Λ := Λ) x := by
  simp [rankOneTwist_F_M_apply]

/-- The rank-one twisted isocrystal with scalar `1` is the constant isocrystal
attached to the rank-one free `K`-module. -/
noncomputable def rankOneTwist_one_iso_const :
    rankOneTwist (Λ := Λ) (1 : Kˣ) ≅
      ConstIsocrystal (Λ := Λ) ({ M := K } : FiniteProjectiveModule K) := by
  let e : (ConstIsocrystal (Λ := Λ) ({ M := K } : FiniteProjectiveModule K)).M ≃ₗ[RealNovikovSeries K]
      (rankOneTwist (Λ := Λ) (1 : Kˣ)).M :=
    TensorProduct.AlgebraTensorModule.rid K (RealNovikovSeries K) (RealNovikovSeries K)
  refine
    { hom :=
        { toLinearMap := e.symm.toLinearMap
          commute_frobenius := ?_ }
      inv :=
        { toLinearMap := e.toLinearMap
          commute_frobenius := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro x
    change RealNovikovSeries K at x
    change TensorProduct.map (frobeniusAlgHom (Λ := Λ) (A := K)).toLinearMap LinearMap.id (e.symm x) =
      e.symm ((rankOneTwist (Λ := Λ) (1 : Kˣ)).F_M x)
    rw [rankOneTwist_one_F_M_apply]
    have hx : e.symm x = x ⊗ₜ[K] (1 : K) :=
      TensorProduct.AlgebraTensorModule.rid_symm_apply (R := K)
        (A := RealNovikovSeries K) (M := RealNovikovSeries K) x
    have hFx : e.symm (frobeniusRingHom (Λ := Λ) (A := K) x) =
        frobeniusRingHom (Λ := Λ) (A := K) x ⊗ₜ[K] (1 : K) :=
      TensorProduct.AlgebraTensorModule.rid_symm_apply (R := K)
        (A := RealNovikovSeries K) (M := RealNovikovSeries K) _
    rw [hx, hFx, TensorProduct.map_tmul, LinearMap.id_apply]
    rfl
  · intro x
    induction x using TensorProduct.induction_on with
    | zero =>
        calc
          (rankOneTwist (Λ := Λ) (1 : Kˣ)).F_M (e 0)
              = (rankOneTwist (Λ := Λ) (1 : Kˣ)).F_M 0 := by rw [e.map_zero]
          _ = 0 := by rw [map_zero]
          _ = e 0 := by rw [e.map_zero]
          _ = e (((ConstIsocrystal (Λ := Λ) ({ M := K } : FiniteProjectiveModule K)).F_M) 0) := by
                symm
                calc
                  e (((ConstIsocrystal (Λ := Λ) ({ M := K } : FiniteProjectiveModule K)).F_M) 0)
                      = e 0 := by rw [map_zero]
                  _ = 0 := e.map_zero
    | tmul r a =>
        change (rankOneTwist (Λ := Λ) (1 : Kˣ)).F_M (e (r ⊗ₜ[K] a)) =
          e (TensorProduct.map (frobeniusAlgHom (Λ := Λ) (A := K)).toLinearMap LinearMap.id (r ⊗ₜ[K] a))
        rw [TensorProduct.map_tmul, LinearMap.id_apply, rankOneTwist_one_F_M_apply]
        have hr : e (r ⊗ₜ[K] (a : K)) = (a : K) • r :=
          TensorProduct.AlgebraTensorModule.rid_tmul (R := K)
            (A := RealNovikovSeries K) (M := RealNovikovSeries K) (a : K) r
        have hFr : e ((frobeniusAlgHom (Λ := Λ) (A := K)).toLinearMap r ⊗ₜ[K] (a : K)) =
            (a : K) • frobeniusRingHom (Λ := Λ) (A := K) r :=
          TensorProduct.AlgebraTensorModule.rid_tmul (R := K)
            (A := RealNovikovSeries K) (M := RealNovikovSeries K) (a : K)
            ((frobeniusAlgHom (Λ := Λ) (A := K)).toLinearMap r)
        rw [hr, hFr]
        change frobeniusRingHom (Λ := Λ) (A := K) ((a : K) • r) =
          (a : K) • frobeniusRingHom (Λ := Λ) (A := K) r
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, frobenius_algebraMap]
    | add x y hx hy =>
        change (rankOneTwist (Λ := Λ) (1 : Kˣ)).F_M (e (x + y)) =
          e (((ConstIsocrystal (Λ := Λ) ({ M := K } : FiniteProjectiveModule K)).F_M) (x + y))
        rw [show e (x + y) = e x + e y from e.map_add x y]
        rw [map_add]
        calc
          (rankOneTwist (Λ := Λ) (1 : Kˣ)).F_M (e x) +
              (rankOneTwist (Λ := Λ) (1 : Kˣ)).F_M (e y)
              = e (((ConstIsocrystal (Λ := Λ) ({ M := K } : FiniteProjectiveModule K)).F_M) x) +
                  e (((ConstIsocrystal (Λ := Λ) ({ M := K } : FiniteProjectiveModule K)).F_M) y) := by
                exact congrArg₂ HAdd.hAdd hx hy
          _ = e (((ConstIsocrystal (Λ := Λ) ({ M := K } : FiniteProjectiveModule K)).F_M) x +
                  ((ConstIsocrystal (Λ := Λ) ({ M := K } : FiniteProjectiveModule K)).F_M) y) := by
                rw [e.map_add]
          _ = e (((ConstIsocrystal (Λ := Λ) ({ M := K } : FiniteProjectiveModule K)).F_M) (x + y)) := by
                exact congrArg e (((ConstIsocrystal (Λ := Λ) ({ M := K } : FiniteProjectiveModule K)).F_M).map_add x y).symm
  · apply hom_ext
    apply LinearMap.ext
    intro x
    exact e.apply_symm_apply x
  · apply hom_ext
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x

end NovikovIsocrystal

end RankOne
end Novikov
