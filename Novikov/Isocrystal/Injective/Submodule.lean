import Novikov.Isocrystal.Basic
import Novikov.Isocrystal.Frobenius
import Novikov.Series.Module
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Frobenius-limit submodule lemma (Lemma 3.6)

Formalizes the result from paper.tex:710-722. A closed `A`-submodule of
`M₀⟪t⟫` stable under Frobenius and `t^d`-shifts has the form `S₀⟪t⟫`
for some `A`-submodule `S₀ ⊆ M₀`.
-/

namespace Novikov
variable {Λ : ℝ} [hΛ1 : Fact (Λ > 1)]

section FrobeniusLimit

variable {A : Type*} [CommRing A] {M₀ : Type*} [AddCommGroup M₀] [Module A M₀]

/-- Given an `A`-submodule `S₀ ⊆ M₀`, the corresponding `A`-submodule of
`RealNovikovSeries M₀` consisting of series whose every coefficient lies in `S₀`. -/
def submoduleSeries (S₀ : Submodule A M₀) : Submodule A (RealNovikovSeries M₀) where
  carrier := { s | ∀ d, s.val d ∈ S₀ }
  zero_mem' := by intro d; exact S₀.zero_mem
  add_mem' {s t} hs ht d := by
    change s.val d + t.val d ∈ S₀
    exact S₀.add_mem (hs d) (ht d)
  smul_mem' a s hs d := by
    rw [smul_val_apply]
    exact S₀.smul_mem a (hs d)

@[simp]
lemma mem_submoduleSeries {S₀ : Submodule A M₀} {s : RealNovikovSeries M₀} :
    s ∈ submoduleSeries S₀ ↔ ∀ d, s.val d ∈ S₀ := Iff.rfl

/-- Hypotheses for Lemma 3.6: closed `A`-submodule of `RealNovikovSeries M₀`
stable under the Frobenius and under multiplication by every monomial `t^d`. -/
structure FrobeniusLimitHyp (S : Submodule A (RealNovikovSeries M₀)) : Prop where
  closed : IsClosed (S : Set (RealNovikovSeries M₀))
  stable_F : ∀ s ∈ S, frobenius Λ s ∈ S
  stable_shift : ∀ (d : ℝ) (s : RealNovikovSeries M₀),
    s ∈ S →
    (novikovMonomial (1 : A) (fun _ : Unit => ⟨d, AddSubgroup.mem_top _⟩) : RealNovikovSeries A) • s ∈ S

/-- Iteration of the Frobenius map: `(F^k s).val d = s.val (d / Λ^k)`. -/
lemma frobenius_iterate_val (s : RealNovikovSeries M₀) (k : ℕ)
    (d : Unit → (⊤ : AddSubgroup ℝ)) :
    ((frobenius Λ)^[k] s).val d =
      s.val (fun _ : Unit => ⟨(d () : ℝ) / Λ ^ k, AddSubgroup.mem_top _⟩) := by
  induction k generalizing d with
  | zero =>
    simp [Function.iterate_zero_apply, pow_zero, div_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', frobenius_apply_val, ih]
    apply congr_arg
    funext i; rcases i
    apply Subtype.ext
    change (d ()).val / Λ / Λ ^ k = (d ()).val / Λ ^ (k + 1)
    rw [pow_succ, ← div_div, div_right_comm]

/-- If a series `s` is in filtration `0` (vanishes for `d() < 0`), then the iterated
Frobenius `F^k s` converges in the `t`-adic topology to the constant series of its
degree-0 coefficient. -/
lemma frobenius_iterate_tendsto_const (s : RealNovikovSeries M₀)
    (h_filt : s ∈ filtration (⊤ : AddSubgroup ℝ) M₀ 0) :
    Filter.Tendsto (fun k => ((frobenius Λ)^[k] s : RealNovikovSeries M₀))
      Filter.atTop
      (nhds (novikovMonomial (s.val (0 : Unit → (⊤ : AddSubgroup ℝ)))
        (0 : Unit → (⊤ : AddSubgroup ℝ)) : RealNovikovSeries M₀)) := by
  haveI : IsTopologicalAddGroup (RealNovikovSeries M₀) := is_topological_add_group
  set m₀ : M₀ := s.val (0 : Unit → (⊤ : AddSubgroup ℝ)) with hm₀_def
  set lim : RealNovikovSeries M₀ :=
    novikovMonomial m₀ (0 : Unit → (⊤ : AddSubgroup ℝ)) with hlim_def
  rw [← Filter.tendsto_sub_const_iff lim]
  simp only [sub_self]
  rw [(filtrationBasis (⊤ : AddSubgroup ℝ) M₀).nhds_zero_hasBasis.tendsto_right_iff]
  rintro V ⟨D, rfl⟩
  -- The Novikov property: only finitely many supports of `s` with value below `D`.
  have h_supp_finite : { d' : Unit → (⊤ : AddSubgroup ℝ) | s.val d' ≠ 0 ∧ (d' () : ℝ) < D }.Finite :=
    finite_support_below s D
  -- Positive supports below `D`.
  set PosSupp : Set (Unit → (⊤ : AddSubgroup ℝ)) :=
    { d' | s.val d' ≠ 0 ∧ 0 < (d' () : ℝ) ∧ (d' () : ℝ) < D } with hPosSupp_def
  have hPosSupp_finite : PosSupp.Finite :=
    h_supp_finite.subset (fun d' h => ⟨h.1, h.2.2⟩)
  -- Choose `ε > 0` such that `(0, ε) ∩ PosSupp = ∅`.
  obtain ⟨ε, hε_pos, hε_lower⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ∀ d' ∈ PosSupp, ε ≤ (d' () : ℝ) := by
    by_cases hPS : PosSupp.Nonempty
    · let f : (Unit → (⊤ : AddSubgroup ℝ)) → ℝ := fun d' => (d' () : ℝ)
      set PSFinset := hPosSupp_finite.toFinset with hPSFinset_def
      have hPSFne : PSFinset.Nonempty := by
        rcases hPS with ⟨x, hx⟩
        exact ⟨x, by simpa [PSFinset, hPSFinset_def] using hx⟩
      have h_img_ne : (PSFinset.image f).Nonempty :=
        Finset.Nonempty.image hPSFne f
      refine ⟨(PSFinset.image f).min' h_img_ne, ?_, ?_⟩
      · obtain ⟨v, hv_mem, hv_eq⟩ := Finset.mem_image.mp
          ((PSFinset.image f).min'_mem h_img_ne)
        have hv : v ∈ PosSupp := by simpa [PSFinset, hPSFinset_def] using hv_mem
        rw [← hv_eq]; exact hv.2.1
      · intro d' hd'
        have hd'_in : d' ∈ PSFinset := by simpa [PSFinset, hPSFinset_def] using hd'
        exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨d', hd'_in, rfl⟩)
    · exact ⟨1, by norm_num, fun d' hd' => absurd ⟨d', hd'⟩ hPS⟩
  -- Choose `K` with `Λ^K > D/ε` for all k ≥ K.
  have hΛ_pos : (0 : ℝ) < Λ := by have := hΛ1.out; linarith
  have hΛ_gt_one : 1 < Λ := hΛ1.out
  have h_tend_pow : Filter.Tendsto (fun k => Λ ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hΛ_gt_one
  obtain ⟨K, hK⟩ :=
    Filter.eventually_atTop.mp (h_tend_pow.eventually_gt_atTop (D / ε))
  refine Filter.eventually_atTop.mpr ⟨K, ?_⟩
  intro k hk d hd
  change ((frobenius Λ)^[k] s).val d - lim.val d = 0
  by_cases hd0 : d = (0 : Unit → (⊤ : AddSubgroup ℝ))
  · -- d = 0: (F^k s).val 0 = s.val 0 = m₀ = lim.val 0.
    subst hd0
    have h_Fk0 : ((frobenius Λ)^[k] s).val (0 : Unit → (⊤ : AddSubgroup ℝ)) = m₀ :=
      frobenius_iterate_apply_zero (Λ := Λ) s k
    rw [h_Fk0]
    have h_lim0 : lim.val (0 : Unit → (⊤ : AddSubgroup ℝ)) = m₀ := by
      simp [lim, novikovMonomial]
    rw [h_lim0, sub_self]
  · -- d ≠ 0 ⇒ lim.val d = 0; need (F^k s).val d = 0.
    have h_lim_d : lim.val d = 0 := by simp [lim, novikovMonomial, hd0]
    rw [h_lim_d, sub_zero]
    rw [frobenius_iterate_val s k d]
    set d' : Unit → (⊤ : AddSubgroup ℝ) :=
      fun _ : Unit => ⟨(d () : ℝ) / Λ ^ k, AddSubgroup.mem_top _⟩ with hd'_def
    have hΛk_pos : (0 : ℝ) < Λ ^ k := pow_pos hΛ_pos k
    by_cases hd_neg : (d () : ℝ) < 0
    · apply h_filt
      change (d () : ℝ) / Λ ^ k < 0
      exact div_neg_of_neg_of_pos hd_neg hΛk_pos
    · push Not at hd_neg
      have hd_ne_real : (d () : ℝ) ≠ 0 := by
        intro h
        apply hd0
        funext i; rcases i
        exact Subtype.ext (by simpa using h)
      have hd_pos : 0 < (d () : ℝ) := lt_of_le_of_ne hd_neg (Ne.symm hd_ne_real)
      have h_d'_pos : 0 < (d' () : ℝ) := div_pos hd_pos hΛk_pos
      have hΛk_ge_K : Λ ^ K ≤ Λ ^ k :=
        pow_le_pow_right₀ (le_of_lt hΛ_gt_one) hk
      have hK_pow : D / ε < Λ ^ K := hK K (le_refl K)
      have h_d'_lt_ε : (d' () : ℝ) < ε := by
        change (d () : ℝ) / Λ ^ k < ε
        rw [div_lt_iff₀ hΛk_pos]
        calc (d () : ℝ) < D := hd
          _ = ε * (D / ε) := by field_simp
          _ < ε * Λ ^ K := mul_lt_mul_of_pos_left hK_pow hε_pos
          _ ≤ ε * Λ ^ k := mul_le_mul_of_nonneg_left hΛk_ge_K (le_of_lt hε_pos)
      by_contra h_ne_zero
      have h_d'_lt_D : (d' () : ℝ) < D := by
        rcases le_or_gt ε D with hεD | hεD
        · exact lt_of_lt_of_le h_d'_lt_ε hεD
        · have hΛk_ge_one : (1 : ℝ) ≤ Λ ^ k := one_le_pow₀ (le_of_lt hΛ_gt_one)
          change (d () : ℝ) / Λ ^ k < D
          calc (d () : ℝ) / Λ ^ k ≤ (d () : ℝ) / 1 :=
                div_le_div_of_nonneg_left hd_pos.le zero_lt_one hΛk_ge_one
            _ = (d () : ℝ) := by simp
            _ < D := hd
      have h_d'_in : d' ∈ PosSupp := ⟨h_ne_zero, h_d'_pos, h_d'_lt_D⟩
      have : ε ≤ (d' () : ℝ) := hε_lower d' h_d'_in
      linarith

/-- For a series in `S` vanishing below degree 0, the constant series with its
degree-0 coefficient also lies in `S`. -/
lemma const_coeff_mem_S (S : Submodule A (RealNovikovSeries M₀))
    (hS : FrobeniusLimitHyp (Λ := Λ) S) (s : RealNovikovSeries M₀) (hs : s ∈ S)
    (h_filt : s ∈ filtration (⊤ : AddSubgroup ℝ) M₀ 0) :
    (novikovMonomial (s.val (0 : Unit → (⊤ : AddSubgroup ℝ)))
      (0 : Unit → (⊤ : AddSubgroup ℝ)) : RealNovikovSeries M₀) ∈ S := by
  -- Each F^k s lies in S (by Frobenius stability), and F^k s tends to the constant series.
  -- Closedness of S finishes the proof.
  have h_seq : ∀ k, ((frobenius Λ)^[k] s : RealNovikovSeries M₀) ∈ S := by
    intro k
    induction k with
    | zero => exact hs
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hS.stable_F _ ih
  have h_tend := frobenius_iterate_tendsto_const (Λ := Λ) s h_filt
  exact hS.closed.mem_of_tendsto h_tend (Filter.Eventually.of_forall h_seq)

/-- Auxiliary version of `coeff_mem_S` parametrized by a natural number bounding
the cardinality of the support of `s` strictly below `d`. -/
private lemma coeff_mem_S_aux (n : ℕ)
    (S : Submodule A (RealNovikovSeries M₀)) (hS : FrobeniusLimitHyp (Λ := Λ) S)
    (s : RealNovikovSeries M₀) (hs : s ∈ S) (d : Unit → (⊤ : AddSubgroup ℝ))
    (h_card_le : (finite_support_below s (d () : ℝ)).toFinset.card ≤ n) :
    (novikovMonomial (s.val d) (0 : Unit → (⊤ : AddSubgroup ℝ)) : RealNovikovSeries M₀) ∈ S := by
  induction n generalizing s d with
  | zero =>
    -- No support strictly below `d`: after shifting by `t^{-d ()}`, the series
    -- lies in filtration 0, and we apply `const_coeff_mem_S`.
    have h_card_zero : (finite_support_below s (d () : ℝ)).toFinset.card = 0 :=
      Nat.le_zero.mp h_card_le
    have h_empty : (finite_support_below s (d () : ℝ)).toFinset = ∅ :=
      Finset.card_eq_zero.mp h_card_zero
    by_cases hsd : s.val d = 0
    · have h : (novikovMonomial (s.val d) (0 : Unit → (⊤ : AddSubgroup ℝ))
          : RealNovikovSeries M₀) = 0 := by
        rw [hsd]; ext d'; simp [novikovMonomial]
      rw [h]; exact S.zero_mem
    -- Construct shifted series and verify in filtration 0.
    set t_neg_d : RealNovikovSeries A :=
      novikovMonomial (1 : A) (fun _ : Unit => ⟨-(d () : ℝ), AddSubgroup.mem_top _⟩) with
      ht_neg_d_def
    set s_shift : RealNovikovSeries M₀ := t_neg_d • s with hs_shift_def
    have hs_shift_in_S : s_shift ∈ S := hS.stable_shift (-(d () : ℝ)) s hs
    -- General coefficient: `(t_neg_d • s).val d' = s.val (d' + d)`.
    have h_shift_val : ∀ d' : Unit → (⊤ : AddSubgroup ℝ),
        s_shift.val d' = s.val (d' + d) := by
      intro d'
      have hmul := Novikov.novikovSeriesMul_left_monomial (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit)
        (a := (1 : A)) (f := s) (α := Novikov.smulAddHom (A := A) (M := M₀))
        (d := (fun _ : Unit => ⟨-(d () : ℝ), AddSubgroup.mem_top _⟩))
        (e := d' + d)
      have h_sum_eq : (fun _ : Unit => ⟨-(d () : ℝ), AddSubgroup.mem_top _⟩
          : Unit → (⊤ : AddSubgroup ℝ)) + (d' + d) = d' := by
        funext i; rcases i
        apply Subtype.ext
        change -(d () : ℝ) + ((d' () : ℝ) + (d () : ℝ)) = (d' () : ℝ)
        ring
      rw [h_sum_eq] at hmul
      change (novikovSeriesMul t_neg_d s (Novikov.smulAddHom (A := A) (M := M₀))).val d' =
        s.val (d' + d)
      rw [hmul]
      simp [Novikov.smulAddHom, _root_.smulAddHom_apply]
    have hs_shift_val_0 :
        s_shift.val (0 : Unit → (⊤ : AddSubgroup ℝ)) = s.val d := by
      rw [h_shift_val]; simp
    have hs_shift_filt : s_shift ∈ filtration (⊤ : AddSubgroup ℝ) M₀ 0 := by
      intro d' hd'_neg
      rw [h_shift_val]
      -- (d' + d) () : ℝ = d'() + d() < d() since d'() < 0.
      by_contra h_ne_zero
      have h_dd_lt : ((d' + d) () : ℝ) < (d () : ℝ) := by
        change (d' () : ℝ) + (d () : ℝ) < (d () : ℝ)
        linarith [hd'_neg]
      have h_in_set : (d' + d) ∈
          ({ d'' : Unit → (⊤ : AddSubgroup ℝ) | s.val d'' ≠ 0 ∧ (d'' () : ℝ) < (d () : ℝ) } :
            Set _) := ⟨h_ne_zero, h_dd_lt⟩
      have h_in_fset : (d' + d) ∈ (finite_support_below s (d () : ℝ)).toFinset := by
        simpa using h_in_set
      rw [h_empty] at h_in_fset
      exact absurd h_in_fset (Finset.notMem_empty _)
    have h := const_coeff_mem_S (Λ := Λ) S hS s_shift hs_shift_in_S hs_shift_filt
    rw [hs_shift_val_0] at h
    exact h
  | succ n ih =>
    by_cases h_empty_supp : (finite_support_below s (d () : ℝ)).toFinset = ∅
    · -- Empty support: use the IH with the trivial card bound `0 ≤ n`.
      refine ih s hs d ?_
      rw [h_empty_supp]; simp
    -- Otherwise pick `d_min` minimizing real-degree among supports of `s` below `d`.
    obtain ⟨d_min, hd_min_in_fset, hd_min_min⟩ :=
      (finite_support_below s (d () : ℝ)).toFinset.exists_min_image
        (fun d' : Unit → (⊤ : AddSubgroup ℝ) => (d' () : ℝ))
        (Finset.nonempty_iff_ne_empty.mpr h_empty_supp)
    -- Unpack `d_min ∈ supp_below s (d ())`.
    have hd_min_mem : s.val d_min ≠ 0 ∧ (d_min () : ℝ) < (d () : ℝ) := by
      have : d_min ∈ ({ d' : Unit → (⊤ : AddSubgroup ℝ)
          | s.val d' ≠ 0 ∧ (d' () : ℝ) < (d () : ℝ) } : Set _) := by
        simpa using hd_min_in_fset
      exact this
    -- Card bound for supports of `s` strictly below `d_min ()`: at most `n`.
    have h_card_at_d_min :
        (finite_support_below s (d_min () : ℝ)).toFinset.card ≤ n := by
      have h_subset :
          (finite_support_below s (d_min () : ℝ)).toFinset ⊆
          ((finite_support_below s (d () : ℝ)).toFinset).erase d_min := by
        intro d'' hd''
        have hd''_in_set : d'' ∈ ({ d' : Unit → (⊤ : AddSubgroup ℝ)
            | s.val d' ≠ 0 ∧ (d' () : ℝ) < (d_min () : ℝ) } : Set _) := by
          simpa using hd''
        have hd''_lt_d : (d'' () : ℝ) < (d () : ℝ) :=
          lt_trans hd''_in_set.2 hd_min_mem.2
        have hd''_ne : d'' ≠ d_min := by
          intro h_eq; rw [h_eq] at hd''_in_set; exact lt_irrefl _ hd''_in_set.2
        rw [Finset.mem_erase]
        refine ⟨hd''_ne, ?_⟩
        have : d'' ∈ ({ d' : Unit → (⊤ : AddSubgroup ℝ)
            | s.val d' ≠ 0 ∧ (d' () : ℝ) < (d () : ℝ) } : Set _) :=
          ⟨hd''_in_set.1, hd''_lt_d⟩
        simpa using this
      calc (finite_support_below s (d_min () : ℝ)).toFinset.card
          ≤ ((finite_support_below s (d () : ℝ)).toFinset.erase d_min).card :=
            Finset.card_le_card h_subset
        _ = (finite_support_below s (d () : ℝ)).toFinset.card - 1 :=
            Finset.card_erase_of_mem hd_min_in_fset
        _ ≤ (n + 1) - 1 := Nat.sub_le_sub_right h_card_le 1
        _ = n := by omega
    -- IH applied at `d_min` yields `novikovMonomial (s.val d_min) 0 ∈ S`.
    have h_min_in_S : (novikovMonomial (s.val d_min)
        (0 : Unit → (⊤ : AddSubgroup ℝ)) : RealNovikovSeries M₀) ∈ S :=
      ih s hs d_min h_card_at_d_min
    -- Shift to `novikovMonomial (s.val d_min) d_min ∈ S` via `stable_shift`.
    have h_min_shifted : (novikovMonomial (s.val d_min) d_min
        : RealNovikovSeries M₀) ∈ S := by
      have h_shift := hS.stable_shift (d_min () : ℝ)
        (novikovMonomial (s.val d_min) (0 : Unit → (⊤ : AddSubgroup ℝ))
          : RealNovikovSeries M₀) h_min_in_S
      have hd_eq : (fun _ : Unit => ⟨(d_min () : ℝ), AddSubgroup.mem_top _⟩
          : Unit → (⊤ : AddSubgroup ℝ)) = d_min := by
        funext i; rcases i; rfl
      rw [hd_eq] at h_shift
      -- Use `novikovSeriesMul_monomial` to simplify the product of monomials.
      have h_mono : (novikovMonomial (1 : A) d_min : RealNovikovSeries A) •
          (novikovMonomial (s.val d_min) 0 : RealNovikovSeries M₀) =
          (novikovMonomial (s.val d_min) d_min : RealNovikovSeries M₀) := by
        simpa [add_zero, Novikov.smulAddHom, _root_.smulAddHom_apply] using
          novikovSeriesMul_monomial (1 : A) (s.val d_min)
            (Novikov.smulAddHom (A := A) (M := M₀)) d_min 0
      rw [h_mono] at h_shift
      exact h_shift
    -- Subtract: `s' := s - novikovMonomial (s.val d_min) d_min ∈ S`.
    set s' : RealNovikovSeries M₀ :=
      s - novikovMonomial (s.val d_min) d_min with hs'_def
    have hs'_in_S : s' ∈ S := S.sub_mem hs h_min_shifted
    -- Show `s'.val d = s.val d` (since `d ≠ d_min`, as `d_min () < d ()`).
    have hd_ne_d_min : d ≠ d_min := by
      intro h
      rw [h] at hd_min_mem
      exact lt_irrefl _ hd_min_mem.2
    have hs'_val_d : s'.val d = s.val d := by
      have h_mono_d : (novikovMonomial (s.val d_min) d_min
          : RealNovikovSeries M₀).val d = 0 := by
        simp [novikovMonomial, hd_ne_d_min]
      change (s - novikovMonomial (s.val d_min) d_min).val d = s.val d
      change s.val d - (novikovMonomial (s.val d_min) d_min : RealNovikovSeries M₀).val d = s.val d
      rw [h_mono_d, sub_zero]
    -- Card of supp_below s' d ≤ n.
    have h_card_s' : (finite_support_below s' (d () : ℝ)).toFinset.card ≤ n := by
      have h_subset :
          (finite_support_below s' (d () : ℝ)).toFinset ⊆
          ((finite_support_below s (d () : ℝ)).toFinset).erase d_min := by
        intro d'' hd''
        have hd''_in_set : d'' ∈ ({ d' : Unit → (⊤ : AddSubgroup ℝ)
            | s'.val d' ≠ 0 ∧ (d' () : ℝ) < (d () : ℝ) } : Set _) := by
          simpa using hd''
        -- Either d'' = d_min (impossible since s'.val d_min = 0), or s'.val d'' = s.val d''.
        have hd''_ne : d'' ≠ d_min := by
          intro h_eq
          apply hd''_in_set.1
          rw [h_eq]
          change (s - novikovMonomial (s.val d_min) d_min).val d_min = 0
          change s.val d_min -
            (novikovMonomial (s.val d_min) d_min : RealNovikovSeries M₀).val d_min = 0
          have h_mono : (novikovMonomial (s.val d_min) d_min : RealNovikovSeries M₀).val d_min =
              s.val d_min := by
            simp [novikovMonomial]
          rw [h_mono]; simp
        have h_eq_val : s'.val d'' = s.val d'' := by
          change (s - novikovMonomial (s.val d_min) d_min).val d'' = s.val d''
          have : (novikovMonomial (s.val d_min) d_min : RealNovikovSeries M₀).val d'' = 0 := by
            simp [novikovMonomial, hd''_ne]
          change s.val d'' -
            (novikovMonomial (s.val d_min) d_min : RealNovikovSeries M₀).val d'' = s.val d''
          rw [this, sub_zero]
        rw [Finset.mem_erase]
        refine ⟨hd''_ne, ?_⟩
        have : d'' ∈ ({ d' : Unit → (⊤ : AddSubgroup ℝ)
            | s.val d' ≠ 0 ∧ (d' () : ℝ) < (d () : ℝ) } : Set _) :=
          ⟨h_eq_val ▸ hd''_in_set.1, hd''_in_set.2⟩
        simpa using this
      calc (finite_support_below s' (d () : ℝ)).toFinset.card
          ≤ ((finite_support_below s (d () : ℝ)).toFinset.erase d_min).card :=
            Finset.card_le_card h_subset
        _ = (finite_support_below s (d () : ℝ)).toFinset.card - 1 :=
            Finset.card_erase_of_mem hd_min_in_fset
        _ ≤ (n + 1) - 1 := Nat.sub_le_sub_right h_card_le 1
        _ = n := by omega
    -- Apply IH at s' to conclude.
    have h := ih s' hs'_in_S d h_card_s'
    rw [hs'_val_d] at h
    exact h

/--
Intermediate step for Lemma 3.6: every coefficient of an element in `S` lies
in the projection submodule `S₀`. The full proof uses the closedness of `S`
and the convergence `m₁ = lim_k F^k (t^{-d_1} s)`.
-/
lemma coeff_mem_S (S : Submodule A (RealNovikovSeries M₀)) (hS : FrobeniusLimitHyp (Λ := Λ) S)
    (s : RealNovikovSeries M₀) (hs : s ∈ S) (d : Unit → (⊤ : AddSubgroup ℝ)) :
    (novikovMonomial (s.val d) (0 : Unit → (⊤ : AddSubgroup ℝ)) : RealNovikovSeries M₀) ∈ S :=
  coeff_mem_S_aux (Λ := Λ) (finite_support_below s (d () : ℝ)).toFinset.card S hS s hs d (le_refl _)

/-- The projection submodule `S₀ ⊆ M₀` from `S ⊆ RealNovikovSeries M₀`:
all `m : M₀` such that the constant series `m` belongs to `S`. -/
def S_zero_submodule (S : Submodule A (RealNovikovSeries M₀)) : Submodule A M₀ where
  carrier := { m | (novikovMonomial m (0 : Unit → (⊤ : AddSubgroup ℝ))
    : RealNovikovSeries M₀) ∈ S }
  zero_mem' := by
    change (novikovMonomial (0 : M₀) (0 : Unit → (⊤ : AddSubgroup ℝ))
      : RealNovikovSeries M₀) ∈ S
    have h : (novikovMonomial (0 : M₀) (0 : Unit → (⊤ : AddSubgroup ℝ))
        : RealNovikovSeries M₀) = 0 := by
      ext d
      simp [novikovMonomial]
    rw [h]; exact S.zero_mem
  add_mem' {m n} hm hn := by
    change (novikovMonomial (m + n) (0 : Unit → (⊤ : AddSubgroup ℝ))
      : RealNovikovSeries M₀) ∈ S
    have h : (novikovMonomial (m + n) (0 : Unit → (⊤ : AddSubgroup ℝ))
        : RealNovikovSeries M₀) =
        (novikovMonomial m (0 : Unit → (⊤ : AddSubgroup ℝ)) : RealNovikovSeries M₀) +
        (novikovMonomial n (0 : Unit → (⊤ : AddSubgroup ℝ)) : RealNovikovSeries M₀) := by
      ext d
      by_cases hd : d = (0 : Unit → (⊤ : AddSubgroup ℝ))
      · subst hd
        simp [novikovMonomial]
      · simp [novikovMonomial, hd]
    rw [h]; exact S.add_mem hm hn
  smul_mem' a m hm := by
    change (novikovMonomial (a • m) (0 : Unit → (⊤ : AddSubgroup ℝ))
      : RealNovikovSeries M₀) ∈ S
    have h_eq : (novikovMonomial (a • m) 0 : RealNovikovSeries M₀) =
        a • (novikovMonomial m 0 : RealNovikovSeries M₀) := by
      ext d; rw [smul_val_apply]; simp [novikovMonomial]
    rw [h_eq]
    exact S.smul_mem a hm

/-- Every monomial `(s.val d) • t^d` of a series `s` lying in `submoduleSeries (S_zero_submodule S)`
is itself in `S`. -/
lemma monomial_mem_S (S : Submodule A (RealNovikovSeries M₀)) (hS : FrobeniusLimitHyp (Λ := Λ) S)
    (s : RealNovikovSeries M₀) (hs : s ∈ submoduleSeries (S_zero_submodule S))
    (d : Unit → (⊤ : AddSubgroup ℝ)) :
    (novikovMonomial (s.val d) d : RealNovikovSeries M₀) ∈ S := by
  -- The constant series `novikovMonomial (s.val d) 0` is in `S` since `s.val d ∈ S_zero_submodule S`.
  have h0 : (novikovMonomial (s.val d) (0 : Unit → (⊤ : AddSubgroup ℝ))
      : RealNovikovSeries M₀) ∈ S := hs d
  -- Shift by `t^(d ())` using `stable_shift`.
  have hd_eq : (fun _ : Unit => ⟨((d () : ℝ)), AddSubgroup.mem_top _⟩
      : Unit → (⊤ : AddSubgroup ℝ)) = d := by
    ext i; rcases i; rfl
  have h1 := hS.stable_shift (d () : ℝ)
    (novikovMonomial (s.val d) (0 : Unit → (⊤ : AddSubgroup ℝ)) : RealNovikovSeries M₀) h0
  rw [hd_eq] at h1
  have h_mono : (novikovMonomial (1 : A) d : RealNovikovSeries A) •
      (novikovMonomial (s.val d) 0 : RealNovikovSeries M₀) =
      (novikovMonomial (s.val d) d : RealNovikovSeries M₀) := by
    simpa [add_zero, Novikov.smulAddHom, _root_.smulAddHom_apply] using
      novikovSeriesMul_monomial (1 : A) (s.val d)
        (Novikov.smulAddHom (A := A) (M := M₀)) d 0
  rw [h_mono] at h1
  exact h1

/--
Lemma 3.6 (`Lem:FrobeniusLimit`): If `S ⊆ M₀⟪t⟫` is a closed `A`-submodule
stable under `F` and under `t^d`-shifts, then `S = (S_zero_submodule S)⟪t⟫`.
-/
lemma frobenius_limit (S : Submodule A (RealNovikovSeries M₀))
    (hS : FrobeniusLimitHyp (Λ := Λ) S) :
    S = submoduleSeries (S_zero_submodule S) := by
  apply le_antisymm
  · -- s ∈ S → every coefficient of s lies in S_zero_submodule S
    intro s hs d
    exact coeff_mem_S (Λ := Λ) S hS s hs d
  · -- s ∈ submoduleSeries (S_zero_submodule S) → s ∈ S.
    intro s hs
    haveI : IsTopologicalAddGroup (RealNovikovSeries M₀) := is_topological_add_group
    -- Partial sums of monomials over supports `d'` with `d' () < D`.
    let s_partial : ℝ → RealNovikovSeries M₀ := fun D =>
      ∑ d' ∈ (finite_support_below s D).toFinset,
        (novikovMonomial (s.val d') d' : RealNovikovSeries M₀)
    -- Each partial sum lies in `S`.
    have h_partial_in_S : ∀ D, s_partial D ∈ S := by
      intro D
      apply Submodule.sum_mem
      intros d' _
      exact monomial_mem_S (Λ := Λ) S hS s hs d'
    -- The coefficient of `s_partial D` at any `d` with `d () < D` equals `s.val d`.
    have h_partial_val : ∀ D d, (d () : ℝ) < D → (s_partial D).val d = s.val d := by
      intro D d hd_lt
      -- Express `(s_partial D).val d` as a sum of monomial values.
      change (∑ d' ∈ (finite_support_below s D).toFinset,
          (novikovMonomial (s.val d') d' : RealNovikovSeries M₀)).val d = s.val d
      have h_sum_val :
          (∑ d' ∈ (finite_support_below s D).toFinset,
              (novikovMonomial (s.val d') d' : RealNovikovSeries M₀)).val d =
          ∑ d' ∈ (finite_support_below s D).toFinset,
            (novikovMonomial (s.val d') d' : RealNovikovSeries M₀).val d := by
        induction (finite_support_below s D).toFinset using Finset.induction_on with
        | empty => simp
        | insert a F ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          change ((novikovMonomial _ _ : RealNovikovSeries M₀) + _).val d = _
          rw [show ((novikovMonomial _ _ + _ : RealNovikovSeries M₀)).val d
            = (novikovMonomial _ _ : RealNovikovSeries M₀).val d + _ from rfl, ih]
      rw [h_sum_val]
      -- Each monomial value: novikovMonomial(s.val d', d').val d = if d = d' then s.val d' else 0.
      have h_term : ∀ d' : Unit → (⊤ : AddSubgroup ℝ),
          (novikovMonomial (s.val d') d' : RealNovikovSeries M₀).val d =
          if d = d' then s.val d' else 0 := by
        intro d'
        change (if d = d' then s.val d' else 0) = _
        rfl
      simp_rw [h_term]
      by_cases hs_d : s.val d = 0
      · -- d ∉ support → sum = 0 = s.val d.
        have h_not_mem : d ∉ (finite_support_below s D).toFinset := by
          intro h_mem
          have : d ∈ ({ d' : Unit → (⊤ : AddSubgroup ℝ)
              | s.val d' ≠ 0 ∧ (d' () : ℝ) < D } : Set _) := by simpa using h_mem
          exact this.1 hs_d
        rw [hs_d]
        rw [Finset.sum_ite_eq (finite_support_below s D).toFinset d (fun d' => s.val d')]
        simp [h_not_mem]
      · -- d ∈ support → sum picks out s.val d.
        have h_mem : d ∈ (finite_support_below s D).toFinset := by
          have hd_in_set : d ∈ ({ d' : Unit → (⊤ : AddSubgroup ℝ)
              | s.val d' ≠ 0 ∧ (d' () : ℝ) < D } : Set _) := ⟨hs_d, hd_lt⟩
          simpa using hd_in_set
        rw [Finset.sum_ite_eq (finite_support_below s D).toFinset d (fun d' => s.val d')]
        simp [h_mem]
    -- For any `D`, `s - s_partial D ∈ filtration D`.
    have h_diff_in_filt : ∀ D, s - s_partial D ∈ filtration (⊤ : AddSubgroup ℝ) M₀ D := by
      intro D d hd_lt
      change s.val d - (s_partial D).val d = 0
      rw [h_partial_val D d hd_lt, sub_self]
    -- Convergence: Tendsto (n : ℕ ↦ s_partial n) atTop (nhds s).
    have h_tend : Filter.Tendsto (fun n : ℕ => s_partial (n : ℝ))
        Filter.atTop (nhds s) := by
      rw [← Filter.tendsto_sub_const_iff s]
      simp only [sub_self]
      rw [(filtrationBasis (⊤ : AddSubgroup ℝ) M₀).nhds_zero_hasBasis.tendsto_right_iff]
      rintro V ⟨D, rfl⟩
      refine Filter.eventually_atTop.mpr ?_
      obtain ⟨N, hN⟩ := exists_nat_gt D
      refine ⟨N, ?_⟩
      intro n hn d hd
      have h_n_ge : D < (n : ℝ) := by
        have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      -- s_partial n - s ∈ filtration n ⊆ filtration D since D < n.
      have hd_lt_n : (d () : ℝ) < (n : ℝ) := lt_trans hd h_n_ge
      change (s_partial (n : ℝ)).val d - s.val d = 0
      rw [h_partial_val (n : ℝ) d hd_lt_n, sub_self]
    exact hS.closed.mem_of_tendsto h_tend
      (Filter.Eventually.of_forall (fun n => h_partial_in_S (n : ℝ)))

end FrobeniusLimit

end Novikov
