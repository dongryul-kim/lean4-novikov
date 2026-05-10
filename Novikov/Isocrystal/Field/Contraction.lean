import Novikov.Isocrystal.Basic
import Novikov.Series.Field
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Contraction operator and B-sequence for the Frobenius eigenvector theorem

Defines the contraction operator `g` and the auxiliary `bSeq` used in the
proof that every nonzero Novikov isocrystal over an algebraically closed field
admits a Frobenius eigenvector.
-/

open scoped BigOperators
open Filter Topology

namespace Novikov
variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]

section ContractionOperator

variable {K : Type*} [Field K]

/-- The contraction operator `g` from Step 5 of the proof of Proposition 2.16.

Given normalized coefficients `a_i ∈ K[[t]]` and a scalar `c ∈ K^×`, define

`g(b) = c^{-n}·F^n(b)·F^{n-1}(a₀) + c^{-n+1}·F^{n-1}(b)·F^{n-2}(a₁) + ... + c^{-1}·F(b)·a_{n-1}`

where `F` is the Frobenius endomorphism on `RealNovikovSeries K`. -/
noncomputable def contractionOperator (Λ : ℝ) [hΛ1 : Fact (Λ > 1)] (K : Type*) [Field K] (n : ℕ)
    (a : Fin n → RealNovikovSeries K) (c : Kˣ)
    (b : RealNovikovSeries K) : RealNovikovSeries K :=
  let F : RealNovikovSeries K → RealNovikovSeries K :=
    Novikov.frobeniusRingHom (Λ := Λ) (A := K)
  ∑ i : Fin n,
    ((algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val)) *
    (F^[n - i.val] b) *
    (F^[n - 1 - i.val] (a i))

/-- Iterates of the Frobenius ring homomorphism preserve the 0-th filtration. -/
lemma frobeniusRingHom_iter_filt0 (f : RealNovikovSeries K)
    (hf : f ∈ filtration (⊤ : AddSubgroup ℝ) K 0) (k : ℕ) :
    (Novikov.frobeniusRingHom (Λ := Λ) (A := K))^[k] f ∈ filtration (⊤ : AddSubgroup ℝ) K 0 := by
  have h := frobeniusRingHom_iterate_filtration (Λ := Λ) (A := K) f 0 hf k
  simpa [mul_zero] using h

/-- The `algebraMap` of any field element lies in the 0-th filtration. -/
lemma algMap_filt0 (a : K) : algebraMap K (RealNovikovSeries K) a ∈ filtration (⊤ : AddSubgroup ℝ) K 0 := by
  intro d hd
  have hd_ne_zero : d ≠ 0 := by
    intro hzero; subst hzero; simp at hd
  have : ((algebraMapNovikov a : RealNovikovSeries K) : (Unit → ↥(⊤ : AddSubgroup ℝ)) → K) d = 0 := by
    dsimp [algebraMapNovikov]; simp [hd_ne_zero]
  simpa [algebraMap] using this

/-- Powers of `algebraMap` elements also lie in the 0-th filtration. -/
lemma algMap_pow_filt0 (a : K) (k : ℕ) :
    (algebraMap K (RealNovikovSeries K) a) ^ k ∈ filtration (⊤ : AddSubgroup ℝ) K 0 := by
  induction k with
  | zero => simpa using algMap_filt0 (1 : K)
  | succ k ih =>
    rw [pow_succ]
    exact filtration_mul_mono (by norm_num) ih (algMap_filt0 a)

/-- `algebraMap` of a field element evaluates to that element at degree 0. -/
lemma algMap_val0 (a : K) : (algebraMap K (RealNovikovSeries K) a) 0 = a := by
  change (algebraMapNovikov a : RealNovikovSeries K).val (fun (_ : Unit) =>
    (0 : ↥(⊤ : AddSubgroup ℝ))) = a
  dsimp [algebraMapNovikov]
  split_ifs
  · rfl
  · exfalso; apply ‹_›; rfl

/-- Powers of `algebraMap` evaluate as powers of the field element at degree 0. -/
lemma algMap_pow_val0 (a : K) (k : ℕ) :
    ((algebraMap K (RealNovikovSeries K) a) ^ k) 0 = a ^ k := by
  induction k with
  | zero => simpa [pow_zero] using algMap_val0 (1 : K)
  | succ k ih =>
    calc
      ((algebraMap K (RealNovikovSeries K) a) ^ (k + 1)) 0 =
          ((algebraMap K (RealNovikovSeries K) a) ^ 1 *
            (algebraMap K (RealNovikovSeries K) a) ^ k) 0 := by ring_nf
      _ = ((algebraMap K (RealNovikovSeries K) a) ^ 1) 0 *
          ((algebraMap K (RealNovikovSeries K) a) ^ k) 0 :=
        filtration_zero_mul_val (algMap_pow_filt0 a 1) (algMap_pow_filt0 a k)
      _ = (algebraMap K (RealNovikovSeries K) a) 0 * a ^ k := by
        simp [algMap_val0 a, ih, pow_one]
      _ = a * a ^ k := by rw [algMap_val0 a]
      _ = a ^ (k + 1) := by simp [pow_succ, mul_comm]

/-- Key estimate (Step 7 of Proposition 2.16): if `x - y` lies in the `D`-th
filtration with `D ≥ 0`, and each `aᵢ` lies in the `0`-th filtration (i.e. `k[[t]]`),
then `g(x) - g(y)` lies in the `(Λ * D)`-th filtration. Here `g` is the contraction
operator defined above. -/
lemma contractionOperator_estimate (Λ : ℝ) [hΛ1 : Fact (Λ > 1)] (K : Type*) [Field K] (n : ℕ)
    (a : Fin n → RealNovikovSeries K) (ha : ∀ i, a i ∈ filtration (⊤ : AddSubgroup ℝ) K 0)
    (c : Kˣ) (x y : RealNovikovSeries K) (D : ℝ) (hDpos : 0 ≤ D)
    (hxy : x - y ∈ filtration (⊤ : AddSubgroup ℝ) K D) :
    contractionOperator Λ K n a c x - contractionOperator Λ K n a c y ∈
    filtration (⊤ : AddSubgroup ℝ) K (Λ * D) := by
  have hΛpos : 0 < Λ := by have := hΛ1.out; linarith
  let F : RealNovikovSeries K →+* RealNovikovSeries K :=
    Novikov.frobeniusRingHom (Λ := Λ) (A := K)
  -- Iterate of F subtracts:
  have hF_iter_sub (k : ℕ) (f g : RealNovikovSeries K) : F^[k] (f - g) = F^[k] f - F^[k] g := by
    induction k with
    | zero => rfl
    | succ k ih => simp
  let cinv : RealNovikovSeries K :=
    algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)
  -- Frobenius and its iterates preserve the filtration, scaling the threshold by Λ
  have hF_filt (f : RealNovikovSeries K) (D' : ℝ)
      (hf : f ∈ filtration (⊤ : AddSubgroup ℝ) K D') :
      F f ∈ filtration (⊤ : AddSubgroup ℝ) K (Λ * D') := by
    intro d hd
    apply hf
    calc
      (d () : ℝ) / Λ < (Λ * D') / Λ := div_lt_div_of_pos_right hd hΛpos
      _ = D' := by field_simp [hΛpos.ne']
  have hF_iter_filt (f : RealNovikovSeries K) (D' : ℝ)
      (hf : f ∈ filtration (⊤ : AddSubgroup ℝ) K D') (k : ℕ) :
      F^[k] f ∈ filtration (⊤ : AddSubgroup ℝ) K (Λ ^ k * D') := by
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      rw [Function.iterate_succ']
      have : F (F^[k] f) ∈ filtration (⊤ : AddSubgroup ℝ) K (Λ * (Λ ^ k * D')) :=
        hF_filt (F^[k] f) (Λ ^ k * D') ih
      simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using this
  -- Expand g(x) – g(y) into a sum
  have h_diff : contractionOperator Λ K n a c x - contractionOperator Λ K n a c y =
      ∑ i : Fin n, cinv ^ (n - i.val) * (F^[n - i.val] (x - y)) *
        (F^[n - 1 - i.val] (a i)) := by
    dsimp [contractionOperator]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    calc
      cinv ^ (n - i.val) * (F^[n - i.val] x) * (F^[n - 1 - i.val] (a i)) -
        cinv ^ (n - i.val) * (F^[n - i.val] y) * (F^[n - 1 - i.val] (a i))
      = cinv ^ (n - i.val) * ((F^[n - i.val] x) - (F^[n - i.val] y)) *
          (F^[n - 1 - i.val] (a i)) := by ring
      _ = cinv ^ (n - i.val) * (F^[n - i.val] (x - y)) *
          (F^[n - 1 - i.val] (a i)) := by rw [hF_iter_sub (n - i.val) x y]
  rw [h_diff]
  -- Each summand lies in the (Λ·D)‑filtration
  have h_term (i : Fin n) :
      cinv ^ (n - i.val) * (F^[n - i.val] (x - y)) * (F^[n - 1 - i.val] (a i)) ∈
      filtration (⊤ : AddSubgroup ℝ) K (Λ * D) := by
    let p := n - i.val
    let q := n - 1 - i.val
    have hp_pos : 1 ≤ p := by
      have hi : i.val < n := i.is_lt
      omega
    have h_pow_ge_Λ : (Λ : ℝ) ≤ (Λ : ℝ) ^ p := by
      have ha : (1 : ℝ) ≤ Λ := hΛ1.out.le
      simpa using pow_le_pow_right₀ ha hp_pos
    have hΛpow_ineq : (Λ : ℝ) * D ≤ (Λ : ℝ) ^ p * D :=
      mul_le_mul_of_nonneg_right h_pow_ge_Λ hDpos
    have h_add1 : (0 : ℝ) + ((Λ : ℝ) ^ p * D) ≥ (Λ : ℝ) ^ p * D :=
      calc
        (0 : ℝ) + ((Λ : ℝ) ^ p * D) = (Λ : ℝ) ^ p * D := by simp
        _ ≥ (Λ : ℝ) ^ p * D := le_rfl
    have h_add2 : ((Λ : ℝ) ^ p * D) + (0 : ℝ) ≥ (Λ : ℝ) ^ p * D :=
      calc
        ((Λ : ℝ) ^ p * D) + (0 : ℝ) = (Λ : ℝ) ^ p * D := by simp
        _ ≥ (Λ : ℝ) ^ p * D := le_rfl
    have h_term1 : cinv ^ p * (F^[p] (x - y)) ∈ filtration (⊤ : AddSubgroup ℝ) K ((Λ : ℝ) ^ p * D) :=
      filtration_mul_mono (Γ := (⊤ : AddSubgroup ℝ)) (A := K) h_add1 (algMap_pow_filt0 ((c : K)⁻¹) p)
        (hF_iter_filt (x - y) D hxy p)
    have h_term2 : (cinv ^ p * (F^[p] (x - y))) * (F^[q] (a i)) ∈
        filtration (⊤ : AddSubgroup ℝ) K ((Λ : ℝ) ^ p * D) :=
      filtration_mul_mono (Γ := (⊤ : AddSubgroup ℝ)) (A := K) h_add2 h_term1 (by
          simpa [mul_zero] using hF_iter_filt (a i) 0 (ha i) q)
    -- Lower the threshold from `Λ^p·D` to `Λ·D`
    exact filtration_mono (Γ := (⊤ : AddSubgroup ℝ)) (A := K) hΛpow_ineq h_term2
  exact AddSubgroup.sum_mem _ (fun i _ => h_term i)

/-- If all `a_i` lie in the `0`-filtration, `g(1)` is in the `0`-filtration,
and `g(1)` has constant term `1`, then there exists a fixed point `b` of `g`
with constant term `1`.

This is the iterative argument from the proof of Proposition 2.16. -/
lemma contractionOperator_fixed (n : ℕ) (a : Fin n → RealNovikovSeries K)
    (ha : ∀ i, a i ∈ filtration (⊤ : AddSubgroup ℝ) K 0) (c : Kˣ) :
    let g := contractionOperator Λ K n a c;
    g 1 ∈ filtration (⊤ : AddSubgroup ℝ) K 0 → (g 1) 0 = 1 →
    ∃ b : RealNovikovSeries K, g b = b ∧ b 0 = 1 := by
  intro g hg1_filt0 hg1_const
  have h_diff_pos : IsPositive (g 1 - 1) := by
    intro d hd_le
    have h1_0 : (1 : RealNovikovSeries K) 0 = (1 : K) := by
      rw [show (1 : RealNovikovSeries K) = novikovOne from rfl, novikovOne_val (A := K)]; simp
    rcases lt_or_eq_of_le hd_le with (hlt | heq)
    · have h1_d : (1 : RealNovikovSeries K) d = 0 := by
        have hd_ne : d ≠ 0 := by intro h; subst h; simp at hlt
        calc
          (1 : RealNovikovSeries K) d = novikovOne d := rfl
          _ = 0 := by rw [novikovOne_val (A := K)]; simp [hd_ne]
      simp [Pi.sub_apply, hg1_filt0 d hlt, h1_d]
    · have hd0 : d = 0 := by ext x; simpa using heq
      simp [hd0, Pi.sub_apply, hg1_const, h1_0]
  have h_exists_ε : ∃ (ε : ℝ), 0 < ε ∧ g 1 - 1 ∈ filtration (⊤ : AddSubgroup ℝ) K ε := by
    by_cases h_diff_zero : g 1 - 1 = 0
    · exact ⟨1, by norm_num, by rw [h_diff_zero]; exact (filtration _ _ _).zero_mem⟩
    · refine ⟨(minDegree (g 1 - 1) () : ℝ),
        support_has_min_pos (g 1 - 1) h_diff_zero h_diff_pos, ?_⟩
      intro d hd; exact minDegree_lt_apply (g 1 - 1) h_diff_zero d hd
  rcases h_exists_ε with ⟨ε, hε_pos, h_diff_filt_ε⟩
  let b_seq : ℕ → RealNovikovSeries K := fun j => g^[j] 1
  have h_step (j : ℕ) : b_seq (j + 1) - b_seq j ∈
      filtration (⊤ : AddSubgroup ℝ) K ((Λ : ℝ) ^ j * ε) := by
    induction j with
    | zero => simpa [b_seq] using h_diff_filt_ε
    | succ j ih =>
      have h_eq : b_seq (j + 2) - b_seq (j + 1) =
          g (b_seq (j + 1)) - g (b_seq j) := by
        simp [b_seq, g, Function.iterate_succ_apply']
      rw [h_eq]
      have hD_nonneg : 0 ≤ (Λ : ℝ) ^ j * ε :=
        mul_nonneg (pow_nonneg (by have h := hΛ1.out; linarith) j) hε_pos.le
      have h_est := contractionOperator_estimate Λ K n a ha c
        (b_seq (j + 1)) (b_seq j) ((Λ : ℝ) ^ j * ε) hD_nonneg ih
      simpa [g, mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_est
  -- Prove that consecutive differences are eventually smaller than any D
  have h_succ (D : ℝ) : ∃ N : ℕ, ∀ n ≥ N,
      b_seq (n + 1) - b_seq n ∈ filtration (⊤ : AddSubgroup ℝ) K D := by
    have hΛgt1 : 1 < Λ := hΛ1.out
    have hδ_pos : 0 < Λ - 1 := by linarith
    set δ := Λ - 1 with hδ_def
    have h_bernoulli (j : ℕ) : (Λ : ℝ) ^ j ≥ 1 + (j : ℝ) * δ := by
      induction j with
      | zero => simp
      | succ k ih =>
        rw [pow_succ]
        have hΛ_eq : (Λ : ℝ) = 1 + δ := by ring
        rw [hΛ_eq]
        have ih' : (1 + δ) ^ k ≥ 1 + (k : ℝ) * δ := by simpa [hΛ_eq] using ih
        have h_nonneg : 0 ≤ 1 + δ := by linarith
        have h1 : (1 + δ) ^ k * (1 + δ) ≥ (1 + (k : ℝ) * δ) * (1 + δ) := by nlinarith
        have h2 : (1 + (k : ℝ) * δ) * (1 + δ) ≥ 1 + ((k + 1 : ℕ) : ℝ) * δ := by
          calc
            (1 + (k : ℝ) * δ) * (1 + δ) = 1 + ((k : ℝ) + 1) * δ + (k : ℝ) * δ ^ 2 := by ring
            _ ≥ 1 + ((k : ℝ) + 1) * δ := by nlinarith
            _ = 1 + ((k + 1 : ℕ) : ℝ) * δ := by simp
        exact h2.trans h1
    set h_target := (D / ε - 1) / δ with hh_target
    rcases exists_nat_gt h_target with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have h_bound : (Λ : ℝ) ^ n * ε ≥ D := by
      have hn_ge_N : (N : ℝ) ≤ (n : ℝ) := mod_cast hn
      have hn_gt_target : (n : ℝ) > h_target := by linarith
      have hn_mul : 1 + (n : ℝ) * δ ≥ D / ε := by
        have h_mul : (n : ℝ) * δ > D / ε - 1 := by
          calc
            (n : ℝ) * δ > ((D / ε - 1) / δ) * δ := by nlinarith
            _ = D / ε - 1 := by field_simp [hδ_pos.ne']
        nlinarith
      have hΛn : (Λ : ℝ) ^ n ≥ 1 + (n : ℝ) * δ := h_bernoulli n
      have h_chain : D / ε ≤ (Λ : ℝ) ^ n := hn_mul.trans hΛn
      calc
        (Λ : ℝ) ^ n * ε ≥ (D / ε) * ε := mul_le_mul_of_nonneg_right h_chain hε_pos.le
        _ = D := by field_simp [hε_pos.ne']
    exact filtration_mono (Γ := (⊤ : AddSubgroup ℝ)) (A := K) h_bound (h_step n)
  have h_cauchySeq : CauchySeq b_seq :=
    cauchySeq_of_succ_diff_filtration b_seq h_succ
  have h_exists_limit : ∃ (b : RealNovikovSeries K),
      Filter.Tendsto b_seq Filter.atTop (nhds b) :=
    cauchySeq_tendsto_of_complete h_cauchySeq
  rcases h_exists_limit with ⟨b, hb_tendsto⟩
  -- At degree 0, g scales by a constant: (g x)₀ = x₀ · (g 1)₀
  have h_g_val (x : RealNovikovSeries K) (hx : x ∈ filtration (⊤ : AddSubgroup ℝ) K 0) : (g x) 0 = x 0 * (g 1) 0 := by
    have hΛpos : 0 < Λ := by linarith [hΛ1.out]
    let F : RealNovikovSeries K →+* RealNovikovSeries K :=
      Novikov.frobeniusRingHom (Λ := Λ) (A := K)
    -- Single term evaluation
    have hterm (y : RealNovikovSeries K) (hy : y ∈ filtration (⊤ : AddSubgroup ℝ) K 0) (i : Fin n) :
        ((algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
          (F^[n - i.val] y) * (F^[n - 1 - i.val] (a i))) 0 =
        y 0 * (((c : K)⁻¹) ^ (n - i.val) * (a i) 0) := by
      let A := (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val)
      let B := F^[n - i.val] y
      let C := F^[n - 1 - i.val] (a i)
      have hA : A ∈ filtration (⊤ : AddSubgroup ℝ) K 0 :=
        algMap_pow_filt0 ((c : K)⁻¹) (n - i.val)
      have hB : B ∈ filtration (⊤ : AddSubgroup ℝ) K 0 :=
        frobeniusRingHom_iter_filt0 y hy (n - i.val)
      have hC : C ∈ filtration (⊤ : AddSubgroup ℝ) K 0 :=
        frobeniusRingHom_iter_filt0 (a i) (ha i) (n - 1 - i.val)
      have hAB : A * B ∈ filtration (⊤ : AddSubgroup ℝ) K 0 :=
        filtration_mul_mono (by norm_num) hA hB
      calc
        (A * B * C) 0 = ((A * B) * C) 0 := rfl
        _ = (A * B) 0 * C 0 := filtration_zero_mul_val hAB hC
        _ = (A 0 * B 0) * C 0 := by rw [filtration_zero_mul_val hA hB]
        _ = A 0 * B 0 * C 0 := rfl
        _ = (((algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val)) 0) *
            ((F^[n - i.val] y) 0) * ((F^[n - 1 - i.val] (a i)) 0) := by dsimp [A, B, C]
        _ = (((c : K)⁻¹) ^ (n - i.val)) * (y 0) * ((a i) 0) := by
          rw [algMap_pow_val0 ((c : K)⁻¹) (n - i.val),
            frobeniusRingHom_iterate_apply_zero (Λ := Λ) (A := K) y (n - i.val),
            frobeniusRingHom_iterate_apply_zero (Λ := Λ) (A := K) (a i) (n - 1 - i.val)]
        _ = y 0 * (((c : K)⁻¹) ^ (n - i.val) * (a i) 0) := by ring
    calc
      (g x) 0 = ((∑ i : Fin n,
        (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
        (F^[n - i.val] x) * (F^[n - 1 - i.val] (a i))) 0) := rfl
      _ = ∑ i : Fin n, ((algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
        (F^[n - i.val] x) * (F^[n - 1 - i.val] (a i))) 0 := by simp
      _ = ∑ i : Fin n, (x 0 * (((c : K)⁻¹) ^ (n - i.val) * (a i) 0)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hterm x hx]
      _ = x 0 * (∑ i : Fin n, (((c : K)⁻¹) ^ (n - i.val) * (a i) 0)) := by
        simp [Finset.mul_sum]
      _ = x 0 * (∑ i : Fin n, (1 * (((c : K)⁻¹) ^ (n - i.val) * (a i) 0))) := by simp
      _ = x 0 * (∑ i : Fin n, ((algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
        (F^[n - i.val] 1) * (F^[n - 1 - i.val] (a i))) 0) := by
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hi := hterm (1 : RealNovikovSeries K) (by simpa using algMap_filt0 (1 : K)) i
        have h1eq : ((1 : RealNovikovSeries K) 0 : K) = (1 : K) := by
          simpa using algMap_val0 (1 : K)
        simpa [h1eq, one_mul] using hi.symm
      _ = x 0 * ((∑ i : Fin n,
        (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
        (F^[n - i.val] 1) * (F^[n - 1 - i.val] (a i))) 0) := by simp
      _ = x 0 * (g 1) 0 := rfl
  have h_const_preserved (x : RealNovikovSeries K) (hx : x ∈ filtration (⊤ : AddSubgroup ℝ) K 0)
      (hx0 : x 0 = 1) : (g x) 0 = 1 := by
    rw [h_g_val x hx, hx0, hg1_const, mul_one]
  have hb_seq_filt0 (m : ℕ) : b_seq m ∈ filtration (⊤ : AddSubgroup ℝ) K 0 := by
    induction m with
    | zero =>
      dsimp [b_seq]
      simpa using algMap_filt0 (1 : K)
    | succ m ih =>
      have h_succ_eq : b_seq (m + 1) = g (b_seq m) := by
        dsimp [b_seq]
        calc
          g^[m] (g 1) = g^[m+1] 1 := by rw [Function.iterate_succ_apply]
          _ = g (g^[m] 1) := by rw [Function.iterate_succ_apply']
      rw [h_succ_eq]
      dsimp [g, contractionOperator]
      let F := Novikov.frobeniusRingHom (Λ := Λ) (A := K)
      have h_term (i : Fin n) :
          (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
          (F^[n - i.val] (b_seq m)) *
          (F^[n - 1 - i.val] (a i)) ∈ filtration (⊤ : AddSubgroup ℝ) K 0 := by
        have h_cinv : (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) ∈
            filtration (⊤ : AddSubgroup ℝ) K 0 :=
          algMap_pow_filt0 ((c : K)⁻¹) (n - i.val)
        have h_Fx : F^[n - i.val] (b_seq m) ∈ filtration (⊤ : AddSubgroup ℝ) K 0 :=
          frobeniusRingHom_iter_filt0 (b_seq m) ih (n - i.val)
        have h_Fa : F^[n - 1 - i.val] (a i) ∈ filtration (⊤ : AddSubgroup ℝ) K 0 :=
          frobeniusRingHom_iter_filt0 (a i) (ha i) (n - 1 - i.val)
        have h_AB : (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
            (F^[n - i.val] (b_seq m)) ∈ filtration (⊤ : AddSubgroup ℝ) K 0 := by
          have htemp := filtration_mul (D₁ := 0) (D₂ := 0) (Set.mul_mem_mul h_cinv h_Fx)
          refine filtration_mono (D₁ := 0) (D₂ := 0 + 0) (by norm_num) htemp
        have htemp := filtration_mul (D₁ := 0) (D₂ := 0) (Set.mul_mem_mul h_AB h_Fa)
        refine filtration_mono (D₁ := 0) (D₂ := 0 + 0) (by norm_num) htemp
      refine AddSubgroup.sum_mem (filtration (⊤ : AddSubgroup ℝ) K 0)
        (t := Finset.univ) (fun i hi => h_term i)
  have hb_seq_zero (m : ℕ) : b_seq m 0 = 1 := by
    induction m with
    | zero =>
      dsimp [b_seq]
      simpa using algMap_val0 (1 : K)
    | succ m ih =>
      have h_succ_eq : b_seq (m + 1) = g (b_seq m) := by
        dsimp [b_seq]
        calc
          g^[m] (g 1) = g^[m+1] 1 := by rw [Function.iterate_succ_apply]
          _ = g (g^[m] 1) := by rw [Function.iterate_succ_apply']
      rw [h_succ_eq]
      exact h_const_preserved (b_seq m) (hb_seq_filt0 m) ih
  have hb_zero : b 0 = 1 := by
    let FB := Novikov.filtrationBasis (⊤ : AddSubgroup ℝ) K
    have h_tendsto_zero : Filter.Tendsto (fun n => b_seq n - b) Filter.atTop (nhds 0) := by
      have : (0 : RealNovikovSeries K) = b - b := (sub_self _).symm
      rw [this]
      exact Filter.Tendsto.sub hb_tendsto tendsto_const_nhds
    have h_basis := FB.nhds_zero_hasBasis.tendsto_right_iff.mp h_tendsto_zero
    have h_ev := h_basis (filtration (⊤ : AddSubgroup ℝ) K 1) ⟨1, rfl⟩
    rcases Filter.eventually_atTop.mp h_ev with ⟨N, hN⟩
    have h_diff : (b_seq N - b) ∈ filtration (⊤ : AddSubgroup ℝ) K 1 := hN N (le_refl N)
    have h_eval_zero : (b_seq N - b) 0 = 0 := h_diff 0 (by norm_num)
    have : b_seq N 0 - b 0 = 0 := by simpa [Pi.sub_apply] using h_eval_zero
    have h_eq : b_seq N 0 = b 0 := sub_eq_zero.mp this
    rw [← h_eq, hb_seq_zero N]
  have h_gb : g b = b := by
    have h_diff_zero : g b - b = 0 := by
      ext d
      let D : ℝ := max 1 ((d () : ℝ) + 1)
      have hD_pos : 0 ≤ D := le_trans zero_le_one (le_max_left _ _)
      have hD_gt : (d () : ℝ) < D := by
        calc
          (d () : ℝ) < (d () : ℝ) + 1 := lt_add_one _
          _ ≤ D := le_max_right _ _
      let FB := Novikov.filtrationBasis (⊤ : AddSubgroup ℝ) K
      have h_tendsto_zero : Filter.Tendsto (fun n => b_seq n - b) Filter.atTop (nhds 0) := by
        have : (0 : RealNovikovSeries K) = b - b := (sub_self _).symm
        rw [this]
        exact Filter.Tendsto.sub hb_tendsto tendsto_const_nhds
      have h_basis := FB.nhds_zero_hasBasis.tendsto_right_iff.mp h_tendsto_zero
      have h_ev := h_basis (filtration (⊤ : AddSubgroup ℝ) K D) ⟨D, rfl⟩
      rcases Filter.eventually_atTop.mp h_ev with ⟨N, hN⟩
      have h_diff : (b_seq N - b) ∈ filtration (⊤ : AddSubgroup ℝ) K D := hN N (le_refl N)
      have h_g_diff : g (b_seq N) - g b ∈ filtration (⊤ : AddSubgroup ℝ) K (Λ * D) := by
        apply contractionOperator_estimate Λ K n a ha c (b_seq N) b D hD_pos h_diff
      have h_g_eq : g (b_seq N) = b_seq (N + 1) := (Function.iterate_succ_apply' g N 1).symm
      rw [h_g_eq] at h_g_diff
      have h_diff_next : b_seq (N + 1) - b ∈ filtration (⊤ : AddSubgroup ℝ) K D := hN (N + 1) (by omega)
      have hΛD_ge_D : D ≤ Λ * D := by
        have hΛ : 1 ≤ Λ := hΛ1.out.le
        calc
          D = 1 * D := (one_mul D).symm
          _ ≤ Λ * D := mul_le_mul_of_nonneg_right hΛ hD_pos
      have h_g_diff' : b_seq (N + 1) - g b ∈ filtration (⊤ : AddSubgroup ℝ) K D :=
        filtration_mono (Γ := (⊤ : AddSubgroup ℝ)) (A := K) hΛD_ge_D h_g_diff
      have h_gb_diff : g b - b ∈ filtration (⊤ : AddSubgroup ℝ) K D := by
        have : g b - b = -(b_seq (N + 1) - g b) + (b_seq (N + 1) - b) := by abel
        rw [this]
        exact (filtration (⊤ : AddSubgroup ℝ) K D).add_mem
          ((filtration (⊤ : AddSubgroup ℝ) K D).neg_mem h_g_diff') h_diff_next
      exact h_gb_diff d hD_gt
    exact sub_eq_zero.mp h_diff_zero
  exact ⟨b, h_gb, hb_zero⟩

end ContractionOperator

section BSeq

/-- Auxiliary sequence `b₀,…,b_{n-1}` built from `b` via the forward recurrence
`b₀ = c⁻¹·F(b)·a₀`, `b_{k+1} = c⁻¹·(F(b_k) + F(b)·a_{k+1})`. Out-of-range
indices return 0. -/
noncomputable def bSeq (Λ : ℝ) [hΛ1 : Fact (Λ > 1)] (K : Type*) [Field K] (n : ℕ)
    (a : Fin n → RealNovikovSeries K) (c : Kˣ) (b : RealNovikovSeries K) : ℕ → RealNovikovSeries K
  | 0 =>
    let F := Novikov.frobeniusRingHom (Λ := Λ) (A := K)
    let cinv := algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)
    if h : 0 < n then cinv * (F b) * (a ⟨0, h⟩) else 0
  | k+1 =>
    let F := Novikov.frobeniusRingHom (Λ := Λ) (A := K)
    let cinv := algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)
    if h : k + 1 < n then
      cinv * (F (bSeq Λ K n a c b k) + (F b) * (a ⟨k+1, h⟩))
    else 0

lemma bSeq_zero (Λ : ℝ) [hΛ1 : Fact (Λ > 1)] (K : Type*) [Field K] (n : ℕ)
    (a : Fin n → RealNovikovSeries K) (c : Kˣ) (b : RealNovikovSeries K)
    (hn : 0 < n) : bSeq Λ K n a c b 0 =
    let F := Novikov.frobeniusRingHom (Λ := Λ) (A := K);
    let cinv := algebraMap K (RealNovikovSeries K) ((c : K)⁻¹);
    cinv * (F b) * (a ⟨0, hn⟩) := by
  simp [bSeq, hn]

lemma bSeq_succ (Λ : ℝ) [hΛ1 : Fact (Λ > 1)] (K : Type*) [Field K] (n : ℕ)
    (a : Fin n → RealNovikovSeries K) (c : Kˣ) (b : RealNovikovSeries K)
    (k : ℕ) (hk : k + 1 < n) : bSeq Λ K n a c b (k + 1) =
    let F := Novikov.frobeniusRingHom (Λ := Λ) (A := K);
    let cinv := algebraMap K (RealNovikovSeries K) ((c : K)⁻¹);
    cinv * (F (bSeq Λ K n a c b k) + (F b) * (a ⟨k+1, hk⟩)) := by
  simp [bSeq, hk]

lemma bSeq_lt_n (Λ : ℝ) [hΛ1 : Fact (Λ > 1)] (K : Type*) [Field K] (n : ℕ)
    (a : Fin n → RealNovikovSeries K) (c : Kˣ) (b : RealNovikovSeries K)
    (k : ℕ) (hk : n ≤ k) : bSeq Λ K n a c b k = 0 := by
  induction k with
  | zero =>
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hk
    subst hn0; simp [bSeq]
  | succ k ih =>
    have hlt : ¬ (k + 1 < n) := by omega
    simp [bSeq, hlt]

lemma bSeq_eq_formula (Λ : ℝ) [hΛ1 : Fact (Λ > 1)] (K : Type*) [Field K] (n : ℕ)
    (a : Fin n → RealNovikovSeries K) (c : Kˣ) (b : RealNovikovSeries K) (k : ℕ) (hk : k < n) :
    bSeq Λ K n a c b k =
    ∑ j : Fin (k + 1),
      (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (k + 1 - j.val) *
      (Novikov.frobeniusRingHom (Λ := Λ) (A := K))^[k + 1 - j.val] b *
      (Novikov.frobeniusRingHom (Λ := Λ) (A := K))^[k - j.val]
        (a ⟨j.val, lt_of_lt_of_le j.is_lt (Nat.succ_le_of_lt hk)⟩) := by
  let F : RealNovikovSeries K →+* RealNovikovSeries K :=
    Novikov.frobeniusRingHom (Λ := Λ) (A := K)
  let cinv : RealNovikovSeries K :=
    algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)
  have hF_cinv : F cinv = cinv := frobenius_algebraMap _
  induction k with
  | zero =>
    have h0n : 0 < n := by omega
    rw [bSeq_zero Λ K n a c b h0n]
    dsimp [cinv, F]
    simp
  | succ k ih =>
    have hk1n : k + 1 < n := hk
    have hk_n : k < n := Nat.lt_of_succ_lt hk
    rw [bSeq_succ Λ K n a c b k hk1n, ih hk_n]
    rw [mul_add, map_sum F, Finset.mul_sum]
    have h_split : (∑ j : Fin (k + 2),
        cinv ^ (k + 2 - j.val) * ((F : RealNovikovSeries K → RealNovikovSeries K))^[k + 2 - j.val] b *
        ((F : RealNovikovSeries K → RealNovikovSeries K))^[(k + 1) - j.val]
          (a ⟨j.val, lt_of_lt_of_le j.is_lt (Nat.succ_le_of_lt hk1n)⟩)) =
      (∑ j : Fin (k + 1),
        cinv ^ (k + 2 - j.val) * ((F : RealNovikovSeries K → RealNovikovSeries K))^[k + 2 - j.val] b *
        ((F : RealNovikovSeries K → RealNovikovSeries K))^[(k + 1) - j.val]
          (a ⟨j.val, lt_of_lt_of_le j.is_lt (Nat.succ_le_of_lt hk_n)⟩)) +
      cinv * (F b) * (a ⟨k + 1, hk1n⟩) := by
      rw [Fin.sum_univ_castSucc]
      simp [cinv, F]
    rw [h_split]
    change (∑ i : Fin (k+1), cinv * F (cinv ^ (k + 1 - i.val) * (F^[k + 1 - i.val] b) * F^[k - i.val] (a ⟨i.val, lt_of_lt_of_le i.is_lt (Nat.succ_le_of_lt hk_n)⟩))) + cinv * (F b * a ⟨k + 1, hk1n⟩) = _
    have hsum : (∑ i : Fin (k+1),
        cinv * F (cinv ^ (k + 1 - i.val) * (F^[k + 1 - i.val] b) * F^[k - i.val] (a ⟨i.val, lt_of_lt_of_le i.is_lt (Nat.succ_le_of_lt hk_n)⟩))) =
      (∑ j : Fin (k+1),
        cinv ^ (k + 2 - j.val) * (F^[k + 2 - j.val] b) * F^[k + 1 - j.val] (a ⟨j.val, lt_of_lt_of_le j.is_lt (Nat.succ_le_of_lt hk_n)⟩)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [F.map_mul, F.map_mul, F.map_pow, hF_cinv]
      rw [← Function.iterate_succ_apply' F, ← Function.iterate_succ_apply' F]
      have hi : i.val ≤ k := Nat.le_of_lt_succ i.is_lt
      have hk1 : (k + 1 - i.val).succ = k + 2 - i.val := by omega
      have hk2 : (k - i.val).succ = k + 1 - i.val := by omega
      have hk1_pow : k + 1 - i.val + 1 = k + 2 - i.val := by omega
      rw [← mul_assoc, ← mul_assoc, ← pow_succ']
      rw [hk1, hk2, hk1_pow]
    rw [hsum]
    rw [← mul_assoc]

lemma bSeq_last_eq_contractionOperator (Λ : ℝ) [hΛ1 : Fact (Λ > 1)] (K : Type*) [Field K]
    [IsAlgClosed K] (n : ℕ) (hn : 1 ≤ n) (a : Fin n → RealNovikovSeries K) (c : Kˣ)
    (b : RealNovikovSeries K) (h_gb : contractionOperator Λ K n a c b = b) :
    bSeq Λ K n a c b (n - 1) = b := by
  have hn0 : n - 1 < n := by omega
  rw [bSeq_eq_formula Λ K n a c b (n - 1) hn0]
  have hn_eq : n - 1 + 1 = n := by omega
  -- Reindex formula sum to Fin n using the map j ↦ ⟨j.val, lt_of_lt_of_le j.is_lt (Nat.succ_le_of_lt hn0)⟩
  -- This map is a bijection Fin (n-1+1) ≃ Fin n
  let φ : Fin (n-1+1) → Fin n := fun j =>
    ⟨j.val, lt_of_lt_of_le j.is_lt (Nat.succ_le_of_lt hn0)⟩
  have hφ_val (j : Fin (n-1+1)) : (φ j).val = j.val := rfl
  have hφ_inj : Function.Injective φ := by
    intro x y h; ext; simpa [φ] using congr_arg Fin.val h
  have hφ_surj : Function.Surjective φ := by
    intro i
    refine ⟨⟨i.val, ?_⟩, ?_⟩
    · have hi : i.val < n := i.is_lt
      omega
    · ext; simp [φ]
  have hsum : (∑ j : Fin (n-1+1),
      (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ ((n-1)+1 - j.val) *
      (Novikov.frobeniusRingHom (Λ := Λ) (A := K))^[((n-1)+1 - j.val)] b *
      (Novikov.frobeniusRingHom (Λ := Λ) (A := K))^[((n-1)-j.val)]
        (a (φ j))) = (∑ i : Fin n,
      (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ (n - i.val) *
      (Novikov.frobeniusRingHom (Λ := Λ) (A := K))^[n - i.val] b *
      (Novikov.frobeniusRingHom (Λ := Λ) (A := K))^[n - 1 - i.val] (a i)) := by
    have h_inj : ∀ (a : Fin (n-1+1)) (ha : a ∈ (Finset.univ : Finset (Fin (n-1+1)))),
        ∀ (b : Fin (n-1+1)) (hb : b ∈ (Finset.univ : Finset (Fin (n-1+1)))),
        (fun j _ => φ j) a ha = (fun j _ => φ j) b hb → a = b := by
      intro a ha b hb h
      have h' : φ a = φ b := by simpa using h
      exact hφ_inj h'
    have h_surj : ∀ (b : Fin n) (hb : b ∈ (Finset.univ : Finset (Fin n))),
        ∃ (a : Fin (n-1+1)) (ha : a ∈ (Finset.univ : Finset (Fin (n-1+1)))),
        (fun j _ => φ j) a ha = b := by
      intro b hb
      rcases hφ_surj b with ⟨a, ha⟩
      refine ⟨a, Finset.mem_univ _, ?_⟩
      simp [ha]
    exact Finset.sum_bij (fun j _ => φ j)
      (by intro j hj; simp)
      h_inj h_surj
      (by intro j hj; simp [φ, hn_eq])
  have hsum' : (∑ j : Fin (n-1+1),
      (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ ((n-1)+1 - j.val) *
      (Novikov.frobeniusRingHom (Λ := Λ) (A := K))^[((n-1)+1 - j.val)] b *
      (Novikov.frobeniusRingHom (Λ := Λ) (A := K))^[((n-1)-j.val)]
        (a ⟨j.val, lt_of_lt_of_le j.is_lt (Nat.succ_le_of_lt hn0)⟩)) =
    (∑ j : Fin (n-1+1),
      (algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)) ^ ((n-1)+1 - j.val) *
      (Novikov.frobeniusRingHom (Λ := Λ) (A := K))^[((n-1)+1 - j.val)] b *
      (Novikov.frobeniusRingHom (Λ := Λ) (A := K))^[((n-1)-j.val)]
        (a (φ j))) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [φ]
  rw [hsum', hsum]
  -- Goal is now exactly contractionOperator = b
  simpa [contractionOperator] using h_gb

/-- Sum over `Fin n` minus the last element equals sum over `Fin (n-1)` via
natural embedding. Used to reindex sums in the Frobenius eigenvector proof. -/
private lemma fin_erase_last_sum {α : Type*} [AddCommMonoid α] (n : ℕ) (hn : 1 ≤ n) (f : Fin n → α) :
    ∑ i ∈ ((Finset.univ : Finset (Fin n)).erase ⟨n-1, by omega⟩), f i =
    ∑ k : Fin (n-1), f ⟨k.val, by omega⟩ := by
  let embed (k : Fin (n-1)) : Fin n := ⟨k.val, by omega⟩
  refine (Finset.sum_bij (fun k _ => embed k) (fun k hk => ?_) (fun a ha b hb h => ?_) (fun i hi => ?_) (fun k _ => rfl)).symm
  · rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h_eq
    have hval : k.val = n-1 := congrArg Fin.val h_eq
    have : k.val < n-1 := k.is_lt
    linarith
  · -- injectivity: embed a = embed b → a = b
    -- h : embed a = embed b
    ext; simpa using congrArg Fin.val h
  · rw [Finset.mem_erase] at hi
    rcases hi with ⟨hi_ne, hi_mem⟩
    have hi_val : i.val < n-1 := by
      have h_lt_n : i.val < n := i.is_lt
      by_contra! h
      have : i.val = n-1 := by omega
      apply hi_ne
      ext
      exact this
    refine ⟨⟨i.val, hi_val⟩, Finset.mem_univ _, ?_⟩
    ext; rfl

lemma exists_frobenius_eigenvector_of_fixed_point (Λ : ℝ) [hΛ1 : Fact (Λ > 1)] (K : Type*)
    [Field K] [IsAlgClosed K] (M : NovikovIsocrystal (Λ := Λ) K) (m : M.M) (_hm : m ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (a : Fin n → RealNovikovSeries K) (c : Kˣ) (b : RealNovikovSeries K)
    (h_linrel : (M.F_M^[n] m) = ∑ i : Fin n, a i • (M.F_M^[i] m))
    (h_indep : LinearIndependent (RealNovikovSeries K) (fun (i : Fin n) => (M.F_M^[i] m)))
    (h_gb : contractionOperator Λ K n a c b = b) (hb : b ≠ 0) :
    ∃ (m' : M.M) (_hm' : m' ≠ 0),
      M.F_M m' = (algebraMap K (RealNovikovSeries K) (c : K)) • m' := by
  have hn_pos : 0 < n := by omega
  -- Shorthand for Frobenius, constant scalar, its inverse, and the b_i sequence
  let F : RealNovikovSeries K →+* RealNovikovSeries K :=
    Novikov.frobeniusRingHom (Λ := Λ) (A := K)
  let c' : RealNovikovSeries K :=
    algebraMap K (RealNovikovSeries K) (c : K)
  let cinv : RealNovikovSeries K :=
    algebraMap K (RealNovikovSeries K) ((c : K)⁻¹)
  have h_c'_cinv : c' * cinv = 1 := by
    dsimp [c', cinv]; simp
  let b_i (i : Fin n) : RealNovikovSeries K := bSeq Λ K n a c b i.val
  -- Recurrence relations satisfied by b_i
  have h_rec0 : c' * (b_i ⟨0, hn_pos⟩) = F b * (a ⟨0, hn_pos⟩) := by
    dsimp [b_i]
    rw [bSeq_zero Λ K n a c b hn_pos]
    calc
      c' * (cinv * (F b) * (a ⟨0, hn_pos⟩)) = (c' * cinv) * (F b) * (a ⟨0, hn_pos⟩) := by ring
      _ = 1 * (F b) * (a ⟨0, hn_pos⟩) := by rw [h_c'_cinv]
      _ = F b * (a ⟨0, hn_pos⟩) := by simp
  have h_rec_succ (k : ℕ) (hk : k + 1 < n) :
      c' * (b_i ⟨k + 1, hk⟩) = F (b_i ⟨k, Nat.lt_of_succ_lt hk⟩) + F b * (a ⟨k + 1, hk⟩) := by
    dsimp [b_i]
    rw [bSeq_succ Λ K n a c b k hk]
    calc
      c' * (cinv * (F (bSeq Λ K n a c b k) + F b * (a ⟨k + 1, hk⟩))) =
          (c' * cinv) * (F (bSeq Λ K n a c b k) + F b * (a ⟨k + 1, hk⟩)) := by ring
      _ = 1 * (F (bSeq Λ K n a c b k) + F b * (a ⟨k + 1, hk⟩)) := by rw [h_c'_cinv]
      _ = F (bSeq Λ K n a c b k) + F b * (a ⟨k + 1, hk⟩) := by simp
  -- b_{n-1} = b
  have h_b_last : b_i ⟨n - 1, by omega⟩ = b :=
    bSeq_last_eq_contractionOperator Λ K n hn a c b h_gb
  -- Define candidate eigenvector
  let m' : M.M := ∑ i : Fin n, b_i i • (M.F_M^[i] m)
  have hm'_ne_zero : m' ≠ 0 := by
    intro hm'_zero
    have h_all_zero : ∀ i : Fin n, b_i i = 0 := by
      classical
      let l : (Fin n) →₀ RealNovikovSeries K := {
        support := Finset.univ.filter (fun i => b_i i ≠ 0)
        toFun := b_i
        mem_support_toFun := fun i => by simp
      }
      have h_lc0 : Finsupp.linearCombination (RealNovikovSeries K)
          (fun (i : Fin n) => (M.F_M^[i] m)) l = 0 := by
        dsimp [Finsupp.linearCombination, Finsupp.sum, l]
        calc
          ((Finset.univ : Finset (Fin n)).filter (fun i => b_i i ≠ 0)).sum
              (fun x => b_i x • (M.F_M^[x] m))
              = (Finset.univ : Finset (Fin n)).sum (fun x =>
                (if b_i x ≠ 0 then b_i x • (M.F_M^[x] m) else 0)) := by
            rw [Finset.sum_filter]
          _ = (Finset.univ : Finset (Fin n)).sum (fun x => b_i x • (M.F_M^[x] m)) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            by_cases hx : b_i x = 0
            · simp [hx]
            · simp [hx]
          _ = (∑ x : Fin n, b_i x • (M.F_M^[x] m)) := by simp
          _ = m' := rfl
          _ = 0 := hm'_zero
      have h_l0 : l = 0 := by
        have h_inj : Function.Injective (Finsupp.linearCombination (RealNovikovSeries K)
            (fun (i : Fin n) => (M.F_M^[i] m))) := h_indep
        apply h_inj
        rw [h_lc0, map_zero]
      intro i
      have : l i = 0 := by simpa using congrFun (congrArg DFunLike.coe h_l0) i
      simpa [l] using this
    have hlast := h_all_zero ⟨n - 1, by omega⟩
    rw [h_b_last] at hlast
    exact hb hlast
  have hm'_eq : M.F_M m' = c' • m' := by
    dsimp [m']
    have hLHS : M.F_M (∑ i : Fin n, b_i i • (M.F_M^[i] m)) =
        ∑ i : Fin n, F (b_i i) • (M.F_M^[i.val + 1] m) := by
      calc
        M.F_M (∑ i : Fin n, b_i i • (M.F_M^[i] m)) =
            ∑ i : Fin n, M.F_M (b_i i • (M.F_M^[i] m)) := map_sum M.F_M _ _
        _ = ∑ i : Fin n, F (b_i i) • M.F_M (M.F_M^[i] m) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [M.F_M.map_smulₛₗ]
        _ = ∑ i : Fin n, F (b_i i) • (M.F_M^[i.val + 1] m) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Function.iterate_succ_apply' M.F_M i.val]
    have hRHS : c' • (∑ i : Fin n, b_i i • (M.F_M^[i] m)) =
        ∑ i : Fin n, (c' * b_i i) • (M.F_M^[i] m) := by
      simp [Finset.smul_sum, smul_smul]
    rw [hLHS, hRHS]
    -- Show LHS sum equals RHS sum
    have h_diff_eq : (∑ i : Fin n, F (b_i i) • (M.F_M^[i.val + 1] m)) -
        (∑ i : Fin n, (c' * b_i i) • (M.F_M^[i] m)) = 0 := by
      -- We prove the equality by expressing both sides as linear combinations of F_M^[j] m,
      -- then showing each coefficient equals c' * b_j by the recurrence relations.
      -- Use the identity: F_M^{i.val+1} m = M.F_M (F_M^{i.val} m) for i < n-1,
      -- and F_M^n m = Σ a_j • F_M^j m for the last term.
      --
      -- Strategy: split LHS into (i = last) + rest, expand last using h_linrel,
      -- then reorganize terms by the index of F_M^[j] m.
      let last_idx : Fin n := ⟨n-1, by omega⟩
      have h_last_val : last_idx.val + 1 = n := by
        dsimp [last_idx]
        omega
      have h_sum_split : (∑ i : Fin n, F (b_i i) • (M.F_M^[i.val + 1] m)) =
          (F b • (M.F_M^[n] m)) +
          ((Finset.univ : Finset (Fin n)).erase last_idx).sum (fun i =>
            F (b_i i) • (M.F_M^[i.val + 1] m)) := by
        calc
          (∑ i : Fin n, F (b_i i) • (M.F_M^[i.val + 1] m))
              = ((Finset.univ : Finset (Fin n)).erase last_idx).sum (fun i =>
                F (b_i i) • (M.F_M^[i.val + 1] m)) +
                F (b_i last_idx) • (M.F_M^[last_idx.val + 1] m) := by
            have htemp := (Finset.univ : Finset (Fin n)).sum_erase_add
              (fun i => F (b_i i) • (M.F_M^[i.val + 1] m))
              (Finset.mem_univ last_idx)
            rw [← htemp]
          _ = ((Finset.univ : Finset (Fin n)).erase last_idx).sum (fun i =>
                F (b_i i) • (M.F_M^[i.val + 1] m)) +
                (F b • (M.F_M^[n] m)) := by
            simp [last_idx, h_b_last, h_last_val]
          _ = (F b • (M.F_M^[n] m)) +
              ((Finset.univ : Finset (Fin n)).erase last_idx).sum (fun i =>
                F (b_i i) • (M.F_M^[i.val + 1] m)) := by rw [add_comm]
      rw [h_sum_split, h_linrel]
      simp_rw [Finset.smul_sum, smul_smul]
      -- Now the expression is:
      --   (∑ j:Fin n, (F b * a j) • F_M^[j] m)                                          [call this SB]
      -- + (∑ i in univ.erase last_idx, F (b_i i) • F_M^[i.val+1] m)                    [call this SA]
      -- - (∑ i:Fin n, (c' * b_i i) • F_M^[i] m)                                         [call this SC]
      -- = 0
      -- Note: SA sums over i ≠ last_idx, with F_M^[i.val+1] where i.val ∈ {0,...,n-2}.
      -- So F_M indices in SA are {1,...,n-1}.
      -- Reindex SA: replace i with Fin.pred (or use a bijection from Fin (n-1) to Fin n \ {last_idx})
      -- Specifically, for each k : Fin (n-1), Fin.castSucc k is in Fin n and not last_idx.
      -- Also, (Fin.castSucc k).val + 1 = (Fin.succ k).val.
      -- So SA = ∑_{k:Fin (n-1)} F (b_i (Fin.castSucc k)) • F_M^[Fin.succ k] m
      -- Then the total coefficient of F_M^[j] m for j ≠ 0 is:
      --   (F b * a j) + F (b_i (Fin.castSucc (j.pred ...))) - (c' * b_i j)
      -- which equals 0 by h_rec_succ.
      -- And for j = 0, coefficient is (F b * a 0) - (c' * b_i 0) = 0 by h_rec0.
      --
      -- To formalize, we write everything as a sum over Fin n, gathering coefficients.
      -- This is a purely algebraic identity; we use abel/ring to simplify.
      have h_expr_eq_zero : (
          (∑ j : Fin n, (F b * a j) • (M.F_M^[j] m)) +
          ((Finset.univ : Finset (Fin n)).erase last_idx).sum (fun i =>
            F (b_i i) • (M.F_M^[i.val + 1] m)) -
          (∑ i : Fin n, (c' * b_i i) • (M.F_M^[i] m))) = 0 := by
        have h_split (g : Fin n → M.M) : (∑ j : Fin n, g j) = g ⟨0, hn_pos⟩ + ∑ j : Fin (n-1), g ⟨j.val + 1, by omega⟩ := by
          rcases Nat.exists_eq_succ_of_ne_zero hn_pos.ne' with ⟨m, hm⟩
          subst hm; exact Fin.sum_univ_succ _
        have h1 := h_split (fun j => (F b * a j) • (M.F_M^[j.val] m))
        have h2 := h_split (fun j => (c' * b_i j) • (M.F_M^[j.val] m))
        rw [h1, h2]
        --
        -- Now we need to relate SA to a sum over Fin (n-1)
        have h_SA_eq : ((Finset.univ : Finset (Fin n)).erase last_idx).sum (fun i =>
            F (b_i i) • (M.F_M^[i.val + 1] m)) =
            (∑ k : Fin (n-1), F (b_i ⟨k.val, by omega⟩) • (M.F_M^[k.val + 1] m)) :=
          fin_erase_last_sum n hn (fun i => F (b_i i) • (M.F_M^[i.val + 1] m))
        rw [h_SA_eq]
        have h_zero_term : ((F b * a ⟨0, hn_pos⟩) • (M.F_M^[0] m) - (c' * b_i ⟨0, hn_pos⟩) • (M.F_M^[0] m)) = 0 := by
          have h_eq_m : (F b * a ⟨0, hn_pos⟩) = c' * (b_i ⟨0, hn_pos⟩) := by
            rw [h_rec0]
          rw [h_eq_m, sub_self]
        have h_sum_zero : (∑ k : Fin (n-1), (F b * a ⟨k.val + 1, by omega⟩) • (M.F_M^[k.val + 1] m)) +
                          (∑ k : Fin (n-1), F (b_i ⟨k.val, by omega⟩) • (M.F_M^[k.val + 1] m)) -
                          (∑ k : Fin (n-1), (c' * b_i ⟨k.val + 1, by omega⟩) • (M.F_M^[k.val + 1] m)) = 0 := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_eq_zero (fun k _ => ?_)
          have hk_lt : k.val + 1 < n := by
            have hk' := k.is_lt
            omega
          have hrec : c' * b_i ⟨k.val + 1, by omega⟩ = F (b_i ⟨k.val, by omega⟩) + F b * a ⟨k.val + 1, by omega⟩ :=
            h_rec_succ k.val hk_lt
          dsimp [b_i] at hrec ⊢
          rw [← add_smul, ← sub_smul, hrec]
          have h_eq_zero : F b * a ⟨k.val + 1, hk_lt⟩ + F (bSeq Λ K n a c b k.val) -
            (F (bSeq Λ K n a c b k.val) + F b * a ⟨k.val + 1, hk_lt⟩) = 0 := by abel
          rw [h_eq_zero, zero_smul]
        -- We just need to rearrange the terms to match h_zero_term + h_sum_zero
        calc
          (F b * a ⟨0, hn_pos⟩) • (M.F_M^[0] m) + ∑ j : Fin (n-1), (F b * a ⟨j.val + 1, by omega⟩) • (M.F_M^[j.val + 1] m) +
              ∑ k : Fin (n-1), F (b_i ⟨k.val, by omega⟩) • (M.F_M^[k.val + 1] m) -
            ((c' * b_i ⟨0, hn_pos⟩) • (M.F_M^[0] m) + ∑ j : Fin (n-1), (c' * b_i ⟨j.val + 1, by omega⟩) • (M.F_M^[j.val + 1] m))
          _ = ((F b * a ⟨0, hn_pos⟩) • (M.F_M^[0] m) - (c' * b_i ⟨0, hn_pos⟩) • (M.F_M^[0] m)) +
              ((∑ j : Fin (n-1), (F b * a ⟨j.val + 1, by omega⟩) • (M.F_M^[j.val + 1] m)) +
               (∑ k : Fin (n-1), F (b_i ⟨k.val, by omega⟩) • (M.F_M^[k.val + 1] m)) -
               (∑ j : Fin (n-1), (c' * b_i ⟨j.val + 1, by omega⟩) • (M.F_M^[j.val + 1] m))) := by abel
          _ = 0 + 0 := by rw [h_zero_term, h_sum_zero]
          _ = 0 := add_zero 0
      rw [h_expr_eq_zero]
    apply sub_eq_zero.mp
    exact h_diff_eq
  exact ⟨m', hm'_ne_zero, hm'_eq⟩

end BSeq

end Novikov

