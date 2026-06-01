import Novikov.Series.Field
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Preliminary lemmas for the Frobenius eigenvector theorem

Linear algebra and coefficient normalization steps used in the proof that
every nonzero Novikov isocrystal over an algebraically closed field admits
a Frobenius eigenvector.
-/

open scoped BigOperators

namespace Novikov
variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]

section LinearRelation

variable (R : Type*) [Field R] (V : Type*) [AddCommGroup V] [Module R V]
  [Module.Finite R V]

/-- In a finite-dimensional vector space `V` over a field `R`, for any nonzero
vector `v : V` and any function `φ : V → V`, there exists `n ≥ 1` and
scalars `a₀,…,a_{n-1} : R` such that `v, φ v, …, φ^{n-1} v` are linearly
independent over `R`, while `φ^n v = ∑_{i=0}^{n-1} a_i · φ^i v`. -/
lemma exists_linear_relation_of_finite_module (φ : V → V) (v : V) (hv : v ≠ 0) :
    ∃ (n : ℕ) (_hn : 1 ≤ n) (a : Fin n → R),
      LinearIndependent R (fun (i : Fin n) => φ^[i] v) ∧
      φ^[n] v = ∑ i : Fin n, a i • φ^[i] v := by
  let d := Module.finrank R V
  -- Any Fin (d+1) independent family would exceed finrank
  have h_dep : ¬ LinearIndependent R (fun (i : Fin (d + 1)) => φ^[i] v) := by
    intro h_indep
    have h_le : Fintype.card (Fin (d + 1)) ≤ Module.finrank R V :=
      h_indep.fintype_card_le_finrank
    have h_card : Fintype.card (Fin (d + 1)) = d + 1 := by simp
    rw [h_card] at h_le
    omega
  -- Find minimal n where dependence occurs
  have h_ex : ∃ k : ℕ, ¬ LinearIndependent R (fun (i : Fin (k + 1)) => φ^[i] v) :=
    ⟨d, h_dep⟩
  classical
    let n := Nat.find h_ex
    have hn_dep : ¬ LinearIndependent R (fun (i : Fin (n + 1)) => φ^[i] v) :=
      Nat.find_spec h_ex
    have hn_min : ∀ k < n, LinearIndependent R (fun (i : Fin (k + 1)) => φ^[i] v) := by
      intro k hk
      by_contra hk_dep
      exact Nat.find_min h_ex hk hk_dep
    have hn_pos : 1 ≤ n := by
      by_contra! h
      have hn0 : n = 0 := by omega
      rw [hn0] at hn_dep
      have h_single_indep : LinearIndependent R (fun (_ : Fin 1) => v) :=
        LinearIndependent.of_subsingleton (0 : Fin 1) hv
      apply hn_dep
      simpa [Function.iterate_zero] using h_single_indep
    -- The first n vectors are linearly independent
    have h_indep_first : LinearIndependent R (fun (i : Fin n) => φ^[i] v) := by
      have h_lt : n - 1 < n := by omega
      have h_prev := hn_min (n - 1) h_lt
      have hn_eq : (n - 1) + 1 = n := by omega
      rw [hn_eq] at h_prev
      exact h_prev
    -- Relate Fin (n+1) family to Fin.snoc
    set f : Fin n → V := fun (i : Fin n) => φ^[i] v
    have h_snoc_eq : Fin.snoc f (φ^[n] v) = (fun (i : Fin (n + 1)) => φ^[i] v) := by
      ext i
      induction i using Fin.lastCases with
      | last => simp [Fin.snoc]
      | cast i => simp [f, Fin.snoc]
    rw [← h_snoc_eq] at hn_dep
    -- Using linearIndependent_finSnoc
    rw [linearIndependent_finSnoc] at hn_dep
    by_cases h_indep_f : LinearIndependent R f
    · have h_span : φ^[n] v ∈ Submodule.span R (Set.range f) := by
        by_contra! h_not_span
        exact hn_dep ⟨h_indep_f, h_not_span⟩
      rw [Submodule.mem_span_range_iff_exists_fun] at h_span
      rcases h_span with ⟨a, ha⟩
      use n, hn_pos, a, h_indep_first
      simpa [f] using ha.symm
    · exfalso
      simpa [f] using h_indep_f h_indep_first

end LinearRelation

section Normalize

variable {K : Type*} [Field K]

/-- Given coefficients `a_i : RealNovikovSeries K` (i=0,…,n-1) with at least one nonzero,
find `r : ℝ` such that multiplying each `a_i` by `t^{r(Λ^n - Λ^i)}` yields series
all lying in `k[[t]]` (the nonnegative-degree subring) and at least one has
nonzero constant term. -/
lemma normalize_coeffs_by_scaling (n : ℕ) (_hn : 1 ≤ n) (a : Fin n → RealNovikovSeries K)
    (h_nonzero : ∃ i, a i ≠ 0) :
    ∃ (r : ℝ) (a' : Fin n → RealNovikovSeries K),
      (∀ i, a' i ∈ filtration (⊤ : AddSubgroup ℝ) K 0) ∧
      (∃ i, a' i 0 ≠ 0) ∧
      (∀ i, a' i = novikovMonomial (1 : K)
        (fun _ : Unit => ⟨r * (Λ ^ n - Λ ^ (i.val : ℕ)), AddSubgroup.mem_top _⟩) * a i) := by
  classical
  have hΛgt1 : 1 < Λ := hΛ1.out
  let s (i : Fin n) : ℝ := Λ ^ n - Λ ^ (i.val : ℕ)
  have hs_pos (i : Fin n) : 0 < s i := by
    dsimp [s]
    have h_pow_lt : Λ ^ (i.val : ℕ) < Λ ^ n :=
      pow_lt_pow_right₀ hΛgt1 (i.is_lt)
    linarith
  let crit_r (i : Fin n) : ℝ := -(minDegree (a i) () : ℝ) / s i
  let nonzero : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ 0)
  have h_nonzero_ne : nonzero.Nonempty := by
    rcases h_nonzero with ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let image : Finset ℝ := nonzero.image crit_r
  have h_image_ne : image.Nonempty :=
    Finset.Nonempty.image h_nonzero_ne crit_r
  let r := image.max' h_image_ne
  have h_r_mem : r ∈ image := Finset.max'_mem _ h_image_ne
  rcases Finset.mem_image.mp h_r_mem with ⟨j, hj, hj_eq⟩
  have hj_nonzero : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hr_ge (i : Fin n) (hi : a i ≠ 0) : crit_r i ≤ r :=
    Finset.le_max' _ (crit_r i) (Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩)
  have h_r_plus_min_nonneg (i : Fin n) (hi : a i ≠ 0) : r * s i + (minDegree (a i) () : ℝ) ≥ 0 := by
    have h := hr_ge i hi
    dsimp [crit_r] at h
    have h' : -(minDegree (a i) () : ℝ) ≤ r * s i := by
      calc
        -(minDegree (a i) () : ℝ) = (-(minDegree (a i) () : ℝ) / s i) * s i := by
          field_simp [(hs_pos i).ne']
        _ ≤ r * s i := mul_le_mul_of_nonneg_right h (hs_pos i).le
    linarith
  have h_r_plus_min_eq_zero : r * s j + (minDegree (a j) () : ℝ) = 0 := by
    dsimp [crit_r] at hj_eq
    calc
      r * s j + (minDegree (a j) () : ℝ)
          = (-(minDegree (a j) () : ℝ) / s j) * s j + (minDegree (a j) () : ℝ) := by rw [hj_eq]
      _ = -(minDegree (a j) () : ℝ) + (minDegree (a j) () : ℝ) := by field_simp [(hs_pos j).ne']
      _ = 0 := by ring
  let s_deg (i : Fin n) : Unit → ↥(⊤ : AddSubgroup ℝ) :=
    fun _ : Unit => ⟨r * s i, AddSubgroup.mem_top _⟩
  let a' (i : Fin n) : RealNovikovSeries K :=
    novikovMonomial (1 : K) (s_deg i) * a i
  have h_shift (i : Fin n) (d : Unit → ↥(⊤ : AddSubgroup ℝ)) :
      a' i d = a i (d - s_deg i) := by
    dsimp [a']
    calc
      (novikovMonomial (1 : K) (s_deg i) * a i) d
          = (novikovMonomial (1 : K) (s_deg i) * a i) (s_deg i + (d - s_deg i)) := by simp
      _ = AddMonoidHom.mul (1 : K) (a i (d - s_deg i)) := by
        simpa using novikovSeriesMul_left_monomial (1 : K) (a i) AddMonoidHom.mul (s_deg i)
          (d - s_deg i)
      _ = a i (d - s_deg i) := by simp
  refine ⟨r, a', ?_, ?_, fun i => rfl⟩
  · intro i d hd
    rw [h_shift i d]
    by_cases hi : a i = 0
    · simp [hi]
    · apply minDegree_lt_apply _ hi
      simp [s_deg, s]
      have := h_r_plus_min_nonneg i hi
      linarith
  · use j
    rw [h_shift j 0]
    have h_val_eq : (minDegree (a j) () : ℝ) = - r * (Λ ^ n - Λ ^ (j.val : ℕ)) := by
      dsimp [s] at h_r_plus_min_eq_zero
      linarith
    have h_minus_eq : (0 : Unit → ↥(⊤ : AddSubgroup ℝ)) - s_deg j = minDegree (a j) := by
      ext x; dsimp [s_deg, s]; simp [h_val_eq]
    rw [h_minus_eq]
    exact leadingCoeff_ne_zero (a j) hj_nonzero

variable [IsAlgClosed K]

/-- In an algebraically closed field K, for n ≥ 1 and scalars a_i ∈ K (not all zero),
there exists nonzero c ∈ Kˣ such that c^n = Σ_{i=0}^{n-1} a_i · c^i. -/
lemma exists_nonzero_solution_of_algClosed {n : ℕ} (hn : 1 ≤ n) (a : Fin n → K)
    (h_nonzero : ∃ i, a i ≠ 0) : ∃ c : Kˣ, (c : K)^n = ∑ i : Fin n, a i * (c : K)^(i.val) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases ha0 : a 0 = 0
    · -- Case a₀ = 0: shift coefficients and apply induction
      let b (i : Fin n) : K := a (Fin.succ i)
      have hb_nonzero : ∃ i, b i ≠ 0 := by
        rcases h_nonzero with ⟨i, hi⟩
        by_cases hi0 : i = 0
        · subst hi0; exact (hi ha0).elim
        · rcases Fin.exists_succ_eq.mpr hi0 with ⟨j, hj⟩
          use j; dsimp [b]; rw [hj]; exact hi
      have hn' : 1 ≤ n := by
        by_cases hn0 : n = 0
        · subst hn0
          rcases hb_nonzero with ⟨j, hj⟩
          exact Fin.elim0 j
        · omega
      rcases ih hn' b hb_nonzero with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      calc
        (c : K)^(n+1) = (c : K) * (c : K)^n := by ring
        _ = (c : K) * (∑ j : Fin n, b j * (c : K)^(j.val)) := by rw [hc]
        _ = ∑ j : Fin n, (c : K) * (b j * (c : K)^(j.val)) := by rw [Finset.mul_sum]
        _ = ∑ j : Fin n, b j * ((c : K) * (c : K)^(j.val)) :=
          Finset.sum_congr rfl (fun j _ => by ring)
        _ = ∑ j : Fin n, a (Fin.succ j) * (c : K)^((Fin.succ j).val : ℕ) := by
          simp [b, Fin.val_succ, pow_succ, mul_comm, mul_left_comm]
        _ = ∑ i : Fin (n+1), a i * (c : K)^(i.val) := by
          rw [Fin.sum_univ_succ]
          simp [ha0]
    · -- Case a₀ ≠ 0: use polynomial P(x) = x^{n+1} - Σ a_i · x^i
      let P : Polynomial K := Polynomial.X^(n+1) -
        ∑ i : Fin (n+1), Polynomial.C (a i) * Polynomial.X^(i.val : ℕ)
      have h_degree_ne_zero : P.degree ≠ 0 := by
        have hdeg_sum : Polynomial.degree (∑ i : Fin (n+1),
            Polynomial.C (a i) * Polynomial.X^(i.val : ℕ)) ≤ (n : ℕ) := by
          refine (Polynomial.degree_sum_le _ _).trans ?_
          refine Finset.sup_le fun i _ => ?_
          calc
            Polynomial.degree (Polynomial.C (a i) * Polynomial.X^(i.val : ℕ)) ≤ (i.val : ℕ) :=
              Polynomial.degree_C_mul_X_pow_le (i.val : ℕ) (a i)
            _ ≤ (n : ℕ) := by exact mod_cast Nat.le_of_lt_succ i.is_lt
        have h_degsum_lt : Polynomial.degree (∑ i : Fin (n+1),
            Polynomial.C (a i) * Polynomial.X^(i.val : ℕ)) <
            Polynomial.degree (Polynomial.X^(n+1 : ℕ) : Polynomial K) := by
          rw [Polynomial.degree_X_pow (n+1 : ℕ)]
          exact lt_of_le_of_lt hdeg_sum (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n))
        have hdeg_P : Polynomial.degree P =
            Polynomial.degree (Polynomial.X^(n+1 : ℕ) : Polynomial K) :=
          Polynomial.degree_sub_eq_left_of_degree_lt h_degsum_lt
        rw [hdeg_P, Polynomial.degree_X_pow (n+1 : ℕ)]
        exact mod_cast Nat.succ_ne_zero n
      rcases IsAlgClosed.exists_root P h_degree_ne_zero with ⟨c, hc⟩
      have hc_ne_zero : c ≠ 0 := by
        intro hc0
        have h_eval : P.eval 0 = - a 0 := by
          dsimp [P]
          simp [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_finsetSum, Fin.sum_univ_succ, Fin.val_succ,
            zero_pow (Nat.succ_ne_zero _)]
        have h_root : P.eval c = 0 := hc
        rw [hc0] at h_root
        rw [h_eval] at h_root
        exact ha0 (neg_eq_zero.mp h_root)
      use Units.mk0 c hc_ne_zero
      simpa [P, Polynomial.eval_finsetSum, sub_eq_zero] using hc

end Normalize

end Novikov
