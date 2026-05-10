import Novikov.Series.OneVar
import Novikov.Series.Ring
import Novikov.Series.Exact

open Novikov
open Topology

namespace Novikov
variable {Λ : ℝ} [hΛ : Fact (Λ > 0)]

/- Fix a real number `Λ > 1`. We want to define a ring homomorphism
   `OneVarNovikovSeries ℝ A → OneVarNovikovSeries ℝ A` sending each monomial to
   its `Λ`th power. Even though it acts by the identity on the coefficient ring
   `A`, we still call it the Frobenius homomorphism. -/

section CommGroup
variable {A : Type*} [AddCommGroup A]

/-- The function underlying the Frobenius endomorphism. -/
noncomputable def frobeniusFun (Λ : ℝ) (f : RealNovikovSeries A) : (Unit → ↥(⊤ : AddSubgroup ℝ)) → A :=
  fun d => f (fun _ => ⟨(d () : ℝ) / Λ, AddSubgroup.mem_top _⟩)

lemma isNovikovSeries_frobenius (f : RealNovikovSeries A) :
    isNovikovSeries (frobeniusFun Λ f) := by
  intro s hs C
  set s' : Unit → ℝ := fun _ => s () * Λ with hs'
  have hΛpos : 0 < Λ := hΛ.out
  have h_pos : ∀ i, 0 < s' i := fun _ => mul_pos (hs ()) hΛpos
  have hf := f.prop s' h_pos C
  let g : (Unit → ↥(⊤ : AddSubgroup ℝ)) → (Unit → ↥(⊤ : AddSubgroup ℝ)) :=
    fun d => fun _ => ⟨(d () : ℝ) / Λ, AddSubgroup.mem_top _⟩
  have hg : Function.Injective g := by
    intro d1 d2 h
    ext i
    have h1 := Subtype.ext_iff.1 (congr_fun h i)
    simp only [g] at h1
    field_simp [hΛpos.ne'] at h1
    exact h1
  have h_S : {d | frobeniusFun Λ f d ≠ 0 ∧ ∑ i, s i * ↑(d i) < C} = g ⁻¹' {d | f d ≠ 0 ∧ ∑ i, s' i * ↑(d i) < C} := by
    ext d
    simp only [Set.mem_preimage, Set.mem_setOf_eq, frobeniusFun, s', g]
    apply and_congr_right
    intro _
    simp only [Fintype.sum_unique]
    field_simp [hΛpos.ne']
  change {d | frobeniusFun Λ f d ≠ 0 ∧ ∑ i, s i * ↑(d i) < C}.Finite
  rw [h_S]
  exact Set.Finite.preimage (fun _ _ _ _ h => hg h) hf

/-- The Frobenius endomorphism on `OneVarNovikovSeries ℝ A`. -/
noncomputable def frobenius (Λ : ℝ) [hΛ : Fact (Λ > 0)] : RealNovikovSeries A →+ RealNovikovSeries A where
  toFun f := ⟨frobeniusFun Λ f, isNovikovSeries_frobenius f⟩
  map_zero' := by
    ext d
    rfl
  map_add' f g := by
    ext d
    rfl

@[simp]
lemma frobenius_apply_val (f : RealNovikovSeries A) (d : Unit → ↥(⊤ : AddSubgroup ℝ)) :
    (frobenius Λ f) d = f (fun _ => ⟨(d () : ℝ) / Λ, AddSubgroup.mem_top _⟩) := rfl

lemma frobenius_monomial (a : A) (d : Unit → ↥(⊤ : AddSubgroup ℝ)) :
    frobenius Λ (novikovMonomial a d) = novikovMonomial a (fun _ => ⟨(d () : ℝ) * Λ, AddSubgroup.mem_top _⟩) := by
  ext d'
  simp only [frobenius_apply_val, novikovMonomial, Subtype.coe_mk]
  have hΛpos : Λ ≠ 0 := hΛ.out.ne'
  have h_iff : (fun _ => ⟨↑(d' ()) / Λ, AddSubgroup.mem_top _⟩) = d ↔ d' = fun _ => ⟨↑(d ()) * Λ, AddSubgroup.mem_top _⟩ := by
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
  change (frobenius Λ f).val (fun _ => (0 : ↥(⊤ : AddSubgroup ℝ))) = f.val (fun _ => (0 : ↥(⊤ : AddSubgroup ℝ)))
  dsimp [frobenius, frobeniusFun]
  have h : (fun (_ : Unit) => ⟨(0 : ℝ) / Λ, AddSubgroup.mem_top _⟩) = (fun (_ : Unit) => (0 : ↥(⊤ : AddSubgroup ℝ))) := by
    ext x; fin_cases x; simp
  rw [h]

/-- Iterating the Frobenius endomorphism preserves the degree-0 coefficient. -/
lemma frobenius_iterate_apply_zero (f : RealNovikovSeries A) (k : ℕ) :
    (frobenius Λ)^[k] f 0 = f 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', frobenius_apply_zero, ih]

/-- The Frobenius endomorphism scales the filtration by `Λ`: if `f` vanishes on
all degrees `< D`, then `frobenius Λ f` vanishes on all degrees `< Λ * D`. -/
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

/- Next we show that the Frobenius homomorphism is continuous. -/

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

/- We also show that given a group homomorphism `A →+ B` the induced map on
   Novikov series respects the Frobenius actions on both sides. -/

variable {B : Type*} [AddCommGroup B]

lemma frobenius_comp_map (g : A →+ B) (f : RealNovikovSeries A) :
    frobenius Λ (Novikov.map g f) = Novikov.map g (frobenius Λ f) := by
  ext d
  simp only [frobenius_apply_val, map_apply]

/- We prove that the fixed points of the Frobenius endomorphism is just the set
   of constant Novikov series. This uses that `Λ > 1`. -/

lemma frobenius_fixed_points [hΛ1 : Fact (Λ > 1)] (f : RealNovikovSeries A) :
    frobenius Λ f = f ↔ ∃ a : A, f = novikovMonomial a 0 := by
  constructor
  · intro h
    use f 0
    ext d
    by_cases hd : d = 0
    · rw [hd]
      simp [novikovMonomial]
    · have h_eq : ∀ n : ℕ, f (fun _ => ⟨(d () : ℝ) / Λ^n, AddSubgroup.mem_top _⟩) = f d := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [pow_succ, ← div_div]
          have h1 : (frobenius Λ f) (fun x ↦ ⟨↑(d ()) / Λ ^ n, AddSubgroup.mem_top _⟩) = f (fun x ↦ ⟨↑(d ()) / Λ ^ n / Λ, AddSubgroup.mem_top _⟩) := by
            simp [frobenius_apply_val]
          rw [← h1, h]
          exact ih
      let S := { d' | f d' ≠ 0 ∧ (d' () : ℝ) < |(d () : ℝ)| + 1 }
      let s : Unit → ℝ := fun _ => 1
      have hs : ∀ i, 0 < s i := fun _ => zero_lt_one
      have h_sum : ∀ d' : Unit → ↥(⊤ : AddSubgroup ℝ), ∑ i, s i * (d' i : ℝ) = (d' () : ℝ) := by
        intro d'
        simp only [Fintype.sum_unique, s, one_mul]
      have h_eqS : S = {d' | f d' ≠ 0 ∧ ∑ i, s i * (d' i : ℝ) < |(d () : ℝ)| + 1} := by
        apply Set.ext
        intro d'
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h_sum]
      have hS : S.Finite := by
        rw [h_eqS]
        exact f.prop s hs (|(d () : ℝ)| + 1)
      by_contra h_nz
      simp only [novikovMonomial, hd, ↓reduceIte, ne_eq] at h_nz
      have h_in_S : ∀ n : ℕ, (fun _ => ⟨(d () : ℝ) / Λ^n, AddSubgroup.mem_top _⟩) ∈ S := by
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
      let f_seq : ℕ → (Unit → ↥(⊤ : AddSubgroup ℝ)) := fun n => fun _ => ⟨(d () : ℝ) / Λ^n, AddSubgroup.mem_top _⟩
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

end CommGroup

section Multiplication

lemma frobenius_mul_bil {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : RealNovikovSeries A)
    (g : RealNovikovSeries B) (α : A →+ B →+ C) :
    frobenius Λ (novikovSeriesMul f g α) = novikovSeriesMul (frobenius Λ f) (frobenius Λ g) α := by
  ext d
  rw [frobenius_apply_val]
  simp only [novikovSeriesMul, novikovSeriesMulFun]
  let h1 := (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val) f.prop g.prop (fun x => ⟨↑(d ()) / Λ, AddSubgroup.mem_top _⟩)).toFinset
  let h2 := (finite_pair_sum_eq (T1 := fnSupport (frobenius Λ f).val) (T2 := fnSupport (frobenius Λ g).val) (frobenius Λ f).prop (frobenius Λ g).prop d).toFinset
  apply Finset.sum_bij (fun p _ => (fun x => ⟨↑(p.1 x) * Λ, AddSubgroup.mem_top _⟩, fun x => ⟨↑(p.2 x) * Λ, AddSubgroup.mem_top _⟩))
  · -- hi: image lands in h2
    intro p hp
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp ⊢
    rcases hp with ⟨h_sum, hf, hg⟩
    refine ⟨?_, ?_, ?_⟩
    · ext i
      have h_sum_i := congr_fun h_sum i
      have h_sum_v : (p.1 i : ℝ) + (p.2 i : ℝ) = (d i : ℝ) / Λ := Subtype.ext_iff.1 h_sum_i
      change (((p.1 i : ℝ) * Λ) + ((p.2 i : ℝ) * Λ)) = (d i : ℝ)
      have hΛ_ne_zero : Λ ≠ 0 := hΛ.out.ne'
      calc (p.1 i : ℝ) * Λ + (p.2 i : ℝ) * Λ
        _ = ((p.1 i : ℝ) + (p.2 i : ℝ)) * Λ := by ring
        _ = ((d i : ℝ) / Λ) * Λ := by rw [h_sum_v]
        _ = (d i : ℝ) := div_mul_cancel₀ _ hΛ_ne_zero
    · rw [frobenius_apply_val]
      have h_eq : (fun x : Unit => ⟨((p.1 x : ℝ) * Λ) / Λ, AddSubgroup.mem_top _⟩) = p.1 := by
        ext i
        change ((p.1 i : ℝ) * Λ) / Λ = (p.1 i : ℝ)
        have hΛ_ne_zero : Λ ≠ 0 := hΛ.out.ne'
        exact mul_div_cancel_right₀ _ hΛ_ne_zero
      rw [h_eq]
      exact hf
    · rw [frobenius_apply_val]
      have h_eq : (fun x : Unit => ⟨((p.2 x : ℝ) * Λ) / Λ, AddSubgroup.mem_top _⟩) = p.2 := by
        ext i
        change ((p.2 i : ℝ) * Λ) / Λ = (p.2 i : ℝ)
        have hΛ_ne_zero : Λ ≠ 0 := hΛ.out.ne'
        exact mul_div_cancel_right₀ _ hΛ_ne_zero
      rw [h_eq]
      exact hg
  · -- injective
    intro p1 hp1 p2 hp2 h_eq
    simp only [Prod.mk.injEq] at h_eq
    ext i
    · have h_eq1 : (p1.1 i : ℝ) * Λ = (p2.1 i : ℝ) * Λ := by
        have h := congr_fun h_eq.1 i
        exact Subtype.ext_iff.1 h
      have hΛ_ne_zero : Λ ≠ 0 := hΛ.out.ne'
      exact mul_right_cancel₀ hΛ_ne_zero h_eq1
    · have h_eq2 : (p1.2 i : ℝ) * Λ = (p2.2 i : ℝ) * Λ := by
        have h := congr_fun h_eq.2 i
        exact Subtype.ext_iff.1 h
      have hΛ_ne_zero : Λ ≠ 0 := hΛ.out.ne'
      exact mul_right_cancel₀ hΛ_ne_zero h_eq2
  · -- surjective
    intro q hq
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq
    rcases hq with ⟨h_sum, hf, hg⟩
    use (fun x => ⟨↑(q.1 x) / Λ, AddSubgroup.mem_top _⟩, fun x => ⟨↑(q.2 x) / Λ, AddSubgroup.mem_top _⟩)
    refine ⟨?_, ?_⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      refine ⟨?_, ?_, ?_⟩
      · ext i
        have h_sum_i := congr_fun h_sum i
        have h_sum_v : (q.1 i : ℝ) + (q.2 i : ℝ) = (d i : ℝ) := Subtype.ext_iff.1 h_sum_i
        change (((q.1 i : ℝ) / Λ) + ((q.2 i : ℝ) / Λ)) = (d i : ℝ) / Λ
        calc (q.1 i : ℝ) / Λ + (q.2 i : ℝ) / Λ
          _ = ((q.1 i : ℝ) + (q.2 i : ℝ)) / Λ := by ring
          _ = (d i : ℝ) / Λ := by rw [h_sum_v]
      · exact hf
      · exact hg
    · apply Prod.ext
      · ext i
        change ((q.1 i : ℝ) / Λ) * Λ = (q.1 i : ℝ)
        have hΛ_ne_zero : Λ ≠ 0 := hΛ.out.ne'
        exact div_mul_cancel₀ _ hΛ_ne_zero
      · ext i
        change ((q.2 i : ℝ) / Λ) * Λ = (q.2 i : ℝ)
        have hΛ_ne_zero : Λ ≠ 0 := hΛ.out.ne'
        exact div_mul_cancel₀ _ hΛ_ne_zero
  · -- term equality
    intro p hp
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
    rw [frobenius_apply_val, frobenius_apply_val]
    have h_eq1 : (fun x : Unit => ⟨((p.1 x : ℝ) * Λ) / Λ, AddSubgroup.mem_top _⟩) = p.1 := by
      ext i
      change ((p.1 i : ℝ) * Λ) / Λ = (p.1 i : ℝ)
      have hΛ_ne_zero : Λ ≠ 0 := hΛ.out.ne'
      exact mul_div_cancel_right₀ _ hΛ_ne_zero
    have h_eq2 : (fun x : Unit => ⟨((p.2 x : ℝ) * Λ) / Λ, AddSubgroup.mem_top _⟩) = p.2 := by
      ext i
      change ((p.2 i : ℝ) * Λ) / Λ = (p.2 i : ℝ)
      have hΛ_ne_zero : Λ ≠ 0 := hΛ.out.ne'
      exact mul_div_cancel_right₀ _ hΛ_ne_zero
    rw [h_eq1, h_eq2]

end Multiplication

section CommRing
variable {A : Type*} [CommRing A]

lemma frobenius_mul (f g : RealNovikovSeries A) :
    frobenius Λ (f * g) = frobenius Λ f * frobenius Λ g :=
  frobenius_mul_bil f g AddMonoidHom.mul

/-- The Frobenius endomorphism on `OneVarNovikovSeries ℝ A`. -/
noncomputable def frobeniusRingHom : RealNovikovSeries A →+* RealNovikovSeries A :=
  { frobenius Λ with
    map_one' := by
      change frobenius Λ (novikovMonomial 1 0) = novikovMonomial 1 0
      rw [frobenius_monomial]
      congr
      ext
      simp
    map_mul' := fun f g => frobenius_mul_bil f g AddMonoidHom.mul }

lemma frobenius_algebraMap (a : A) :
    frobeniusRingHom (Λ := Λ) (algebraMap A (RealNovikovSeries A) a) = algebraMap A (RealNovikovSeries A) a := by
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
    (frobeniusRingHom (Λ := Λ) (A := A))^[k] f ∈ filtration (⊤ : AddSubgroup ℝ) A (Λ ^ k * D) := by
  simpa using frobenius_iterate_filtration f D hf k

/-- The Frobenius iterated `k` times scales the exponent of a monomial `t^d`
to `t^{Λ^k * d}`. -/
lemma frobenius_iterate_monomial_one (d : ℝ) (k : ℕ) :
    (Novikov.frobenius Λ)^[k] (novikovMonomial (1 : A) (fun _ : Unit => ⟨d, AddSubgroup.mem_top _⟩)) =
    novikovMonomial (1 : A) (fun _ : Unit => ⟨Λ ^ k * d, AddSubgroup.mem_top _⟩) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    rw [frobenius_monomial (A := A)]
    rw [ih (d * Λ)]
    congr; ext x; simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]

/-- The Frobenius endomorphism on `OneVarNovikovSeries ℝ A` as an algebra homomorphism. -/
noncomputable def frobeniusAlgHom : RealNovikovSeries A →ₐ[A] RealNovikovSeries A where
  toRingHom := frobeniusRingHom (Λ := Λ)
  commutes' := frobenius_algebraMap

end CommRing

end Novikov
