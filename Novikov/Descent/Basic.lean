import Novikov.Descent.Abstract.Constant
import Novikov.Descent.Abstract.FullFaithful
import Novikov.Descent.Abstract.Descent
import Novikov.Series.Substitute
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Novikov descent data

A Novikov descent datum is a descent datum for the cosimplicial ring
of Novikov series in 1, 2, and 3 variables.
-/

namespace Novikov.Descent

open CategoryTheory Novikov TensorProduct
open Novikov.Descent.Abstract

variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ]

section SubstituteApply

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {Γ : S}

omit [Fintype ι'] in
lemma pushExponents_apply_of_injective {φ : ι → ι'} (hφ : Function.Injective φ)
    (g : ι → Γ) (i : ι) :
    pushExponents φ g (φ i) = g i := by
  classical
  simp only [pushExponents]
  apply Finset.sum_eq_single i
  · intro k hk hki
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact (hki (hφ hk)).elim
  · intro hi
    exact (hi (by simp)).elim

omit [Fintype ι'] in
lemma pushExponents_eq_zero_of_not_mem {φ : ι → ι'} (g : ι → Γ) (j : ι')
    (hj : ∀ i, φ i ≠ j) :
    pushExponents φ g j = 0 := by
  classical
  simp only [pushExponents]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact (hj i hi).elim

/-- If the variable map is injective, substitution has exactly one possible
coefficient contribution: pull back along the image coordinates, provided all
coordinates outside the image vanish. -/
lemma substitute_apply_of_injective [DecidableEq ι'] {φ : ι → ι'}
    (hφ : Function.Injective φ) {A : Type*} [AddCommGroup A]
    (f : NovikovSeries Γ ι A) (d' : ι' → Γ) :
    (substitute φ f).val d' =
      if ∀ j, (∀ i, φ i ≠ j) → d' j = 0 then
        f.val (fun i => d' (φ i))
      else 0 := by
  classical
  have hpre (hzero : ∀ j, (∀ i, φ i ≠ j) → d' j = 0) :
      pushExponents φ (fun i => d' (φ i)) = d' := by
    funext j
    by_cases hj : ∃ i, φ i = j
    · rcases hj with ⟨i, rfl⟩
      exact pushExponents_apply_of_injective hφ (fun i => d' (φ i)) i
    · have hj' : ∀ i, φ i ≠ j := by
        intro i hi
        exact hj ⟨i, hi⟩
      rw [pushExponents_eq_zero_of_not_mem (fun i => d' (φ i)) j hj', hzero j hj']
  have huniq {g : ι → Γ} (hg : pushExponents φ g = d') :
      g = fun i => d' (φ i) := by
    funext i
    rw [← pushExponents_apply_of_injective hφ g i, hg]
  simp only [substitute, substituteFun]
  by_cases hzero : ∀ j, (∀ i, φ i ≠ j) → d' j = 0
  · rw [if_pos hzero]
    exact Finset.sum_eq_single (fun i => d' (φ i))
      (by
        intro g hg hg_ne
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg
        exact (hg_ne (huniq hg.1)).elim)
      (by
        intro h_not_mem
        by_cases hf : f.val (fun i => d' (φ i)) = 0
        · exact hf
        · exfalso
          exact h_not_mem (by
            simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
            exact ⟨hpre hzero, hf⟩))
  · rw [if_neg hzero]
    apply Finset.sum_eq_zero
    intro g hg
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg
    exfalso
    apply hzero
    intro j hj
    rw [← congr_fun hg.1 j]
    exact pushExponents_eq_zero_of_not_mem g j hj

/-- Coefficient formula for substitution along the constant map `Unit → ι'`
sending the unique point to `k`: the coefficient at `d` is the level-one
coefficient at `d k`, provided every other coordinate vanishes. -/
lemma substitute_const_apply [DecidableEq ι'] (k : ι') {A : Type*} [AddCommGroup A]
    (f : NovikovSeries Γ Unit A) (d : ι' → Γ) :
    (substitute (fun _ : Unit => k) f).val d =
      if ∀ j, j ≠ k → d j = 0 then f.val (fun _ : Unit => d k) else 0 := by
  rw [substitute_apply_of_injective (φ := fun _ : Unit => k)
    (hφ := fun x y _ => by cases x; cases y; rfl) f d]
  have hiff : (∀ j, (∀ _ : Unit, (k : ι') ≠ j) → d j = 0) ↔ (∀ j, j ≠ k → d j = 0) := by
    constructor
    · intro h j hj; exact h j (fun _ => Ne.symm hj)
    · intro h j hj; exact h j (Ne.symm (hj ()))
  simp only [hiff]

end SubstituteApply

/-- The cosimplicial ring of Novikov series.

```
       π₁
  R₁ ------> R₂
       π₂

           π₁₂
         ------>
  R₁  →  R₂  π₁₃  R₃
         ------>
           π₂₃

  R₁ ------> R₃
       ρ₁, ρ₂, ρ₃
```

where `R₁ = A((t))`, `R₂ = A((t))((u))`, `R₃ = A((t))((u))((v))`. -/
noncomputable def novikovCosimplicialRing (Γ : S) (A : Type*) [CommRing A] :
    CosimplicialRing where
  R₁ := NovikovSeries Γ Unit A
  R₂ := NovikovSeries Γ (Fin 2) A
  R₃ := NovikovSeries Γ (Fin 3) A
  π₁ := substituteRingHom (Γ := Γ) (A := A) (fun _ : Unit => (0 : Fin 2))
  π₂ := substituteRingHom (Γ := Γ) (A := A) (fun _ : Unit => (1 : Fin 2))
  π₁₂ := substituteRingHom (Γ := Γ) (A := A) Fin.castSucc
  π₁₃ := substituteRingHom (Γ := Γ) (A := A) (Fin.succAbove 1)
  π₂₃ := substituteRingHom (Γ := Γ) (A := A) Fin.succ
  π₁₃_π₁_eq_π₁₂_π₁ := by
    apply RingHom.ext; intro x
    simp only [RingHom.coe_comp, Function.comp_apply, substituteRingHom]
    have h : (Fin.succAbove 1) ∘ (fun _ : Unit => (0 : Fin 2)) =
        Fin.castSucc ∘ (fun _ : Unit => (0 : Fin 2)) := by
      ext ⟨⟩; decide
    calc
      substitute (Fin.succAbove 1) (substitute (fun _ : Unit => (0 : Fin 2)) x)
          = substitute ((Fin.succAbove 1) ∘ (fun _ : Unit => (0 : Fin 2))) x := by
        rw [← substitute_comp]
      _ = substitute (Fin.castSucc ∘ (fun _ : Unit => (0 : Fin 2))) x := by rw [h]
      _ = substitute Fin.castSucc (substitute (fun _ : Unit => (0 : Fin 2)) x) := by
        rw [substitute_comp]
  π₁₂_π₂_eq_π₂₃_π₁ := by
    apply RingHom.ext; intro x
    simp only [RingHom.coe_comp, Function.comp_apply, substituteRingHom]
    have h : Fin.castSucc ∘ (fun _ : Unit => (1 : Fin 2)) =
        Fin.succ ∘ (fun _ : Unit => (0 : Fin 2)) := by
      ext ⟨⟩; decide
    calc
      substitute Fin.castSucc (substitute (fun _ : Unit => (1 : Fin 2)) x)
          = substitute (Fin.castSucc ∘ (fun _ : Unit => (1 : Fin 2))) x := by
        rw [← substitute_comp]
      _ = substitute (Fin.succ ∘ (fun _ : Unit => (0 : Fin 2))) x := by rw [h]
      _ = substitute Fin.succ (substitute (fun _ : Unit => (0 : Fin 2)) x) := by
        rw [substitute_comp]
  π₁₃_π₂_eq_π₂₃_π₂ := by
    apply RingHom.ext; intro x
    simp only [RingHom.coe_comp, Function.comp_apply, substituteRingHom]
    have h : (Fin.succAbove 1) ∘ (fun _ : Unit => (1 : Fin 2)) =
        Fin.succ ∘ (fun _ : Unit => (1 : Fin 2)) := by
      ext ⟨⟩; decide
    calc
      substitute (Fin.succAbove 1) (substitute (fun _ : Unit => (1 : Fin 2)) x)
          = substitute ((Fin.succAbove 1) ∘ (fun _ : Unit => (1 : Fin 2))) x := by
        rw [← substitute_comp]
      _ = substitute (Fin.succ ∘ (fun _ : Unit => (1 : Fin 2))) x := by rw [h]
      _ = substitute Fin.succ (substitute (fun _ : Unit => (1 : Fin 2)) x) := by
        rw [substitute_comp]

section CoefficientFormulas

variable (Γ : S) {A : Type*} [CommRing A]

/-- Coefficient formula for the second face map `π₂ : R₁ → R₂`. -/
lemma novikovCosimplicialRing_π₂_apply (f : (novikovCosimplicialRing Γ A).R₁)
    (d : Fin 2 → Γ) :
    ((novikovCosimplicialRing Γ A).π₂ f).val d =
      if d 0 = 0 then f.val (fun _ : Unit => d 1) else 0 := by
  change (substitute (fun _ : Unit => (1 : Fin 2)) f).val d = _
  rw [substitute_const_apply]
  have hcond : (∀ j : Fin 2, j ≠ 1 → d j = 0) ↔ d 0 = 0 := by
    constructor
    · intro h; exact h 0 (by decide)
    · intro h j hj; fin_cases j
      · exact h
      · exact (hj rfl).elim
  simp only [hcond]

/-- Coefficient formula for `π₁₃ : R₂ → R₃`. -/
lemma novikovCosimplicialRing_π₁₃_apply (f : (novikovCosimplicialRing Γ A).R₂)
    (d : Fin 3 → Γ) :
    ((novikovCosimplicialRing Γ A).π₁₃ f).val d =
      if d 1 = 0 then f.val (fun i : Fin 2 => if i = 0 then d 0 else d 2) else 0 := by
  let φ : Fin 2 → Fin 3 := Fin.succAbove 1
  change (substitute φ f).val d =
    if d 1 = 0 then f.val (fun i : Fin 2 => if i = 0 then d 0 else d 2) else 0
  rw [substitute_apply_of_injective (A := A) (φ := φ)
    (hφ := Fin.succAbove_right_injective) f d]
  by_cases h1 : d 1 = 0
  · have hcond : ∀ j, (∀ i, φ i ≠ j) → d j = 0 := by
      intro j hj
      fin_cases j
      · exact (hj 0 rfl).elim
      · exact h1
      · exact (hj 1 rfl).elim
    rw [if_pos hcond, if_pos h1]
    rw [show (fun i => d (φ i)) = (fun i : Fin 2 => if i = 0 then d 0 else d 2) by
      ext i
      fin_cases i <;> rfl]
  · have hcond : ¬ (∀ j, (∀ i, φ i ≠ j) → d j = 0) := by
      intro hz
      exact h1 (hz 1 (by intro i; fin_cases i <;> decide))
    rw [if_neg hcond, if_neg h1]

/-- Coefficient formula for `π₂₃ : R₂ → R₃`. -/
lemma novikovCosimplicialRing_π₂₃_apply (f : (novikovCosimplicialRing Γ A).R₂)
    (d : Fin 3 → Γ) :
    ((novikovCosimplicialRing Γ A).π₂₃ f).val d =
      if d 0 = 0 then f.val (fun i : Fin 2 => if i = 0 then d 1 else d 2) else 0 := by
  let φ : Fin 2 → Fin 3 := Fin.succ
  change (substitute φ f).val d =
    if d 0 = 0 then f.val (fun i : Fin 2 => if i = 0 then d 1 else d 2) else 0
  rw [substitute_apply_of_injective (A := A) (φ := φ)
    (hφ := fun _ _ h => Fin.succ_injective _ h) f d]
  by_cases h0 : d 0 = 0
  · have hcond : ∀ j, (∀ i, φ i ≠ j) → d j = 0 := by
      intro j hj
      fin_cases j
      · exact h0
      · exact (hj 0 rfl).elim
      · exact (hj 1 rfl).elim
    rw [if_pos hcond, if_pos h0]
    rw [show (fun i => d (φ i)) = (fun i : Fin 2 => if i = 0 then d 1 else d 2) by
      ext i
      fin_cases i <;> rfl]
  · have hcond : ¬ (∀ j, (∀ i, φ i ≠ j) → d j = 0) := by
      intro hz
      exact h0 (hz 0 (by intro i; fin_cases i <;> decide))
    rw [if_neg hcond, if_neg h0]

/-- Coefficient formula for `ρ₃ : R₁ → R₃`. -/
lemma novikovCosimplicialRing_ρ₃_apply (f : (novikovCosimplicialRing Γ A).R₁)
    (d : Fin 3 → Γ) :
    ((novikovCosimplicialRing Γ A).ρ₃ f).val d =
      if d 0 = 0 ∧ d 1 = 0 then f.val (fun _ : Unit => d 2) else 0 := by
  have hρ : (novikovCosimplicialRing Γ A).ρ₃ f =
      substitute (fun _ : Unit => (2 : Fin 3)) f := by
    change substituteRingHom Fin.succ (substituteRingHom (fun _ : Unit => (1 : Fin 2)) f) =
      substituteRingHom (fun _ : Unit => (2 : Fin 3)) f
    simp only [substituteRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← substitute_comp]
    rfl
  rw [hρ, substitute_const_apply]
  have hcond : (∀ j : Fin 3, j ≠ 2 → d j = 0) ↔ (d 0 = 0 ∧ d 1 = 0) := by
    constructor
    · intro h; exact ⟨h 0 (by decide), h 1 (by decide)⟩
    · intro h j hj; fin_cases j
      · exact h.1
      · exact h.2
      · exact (hj rfl).elim
  simp only [hcond]

/-- Coefficient formula for `ρ₁ : R₁ → R₃`. -/
lemma novikovCosimplicialRing_ρ₁_apply (f : (novikovCosimplicialRing Γ A).R₁)
    (d : Fin 3 → Γ) :
    ((novikovCosimplicialRing Γ A).ρ₁ f).val d =
      if d 1 = 0 ∧ d 2 = 0 then f.val (fun _ : Unit => d 0) else 0 := by
  have hρ : (novikovCosimplicialRing Γ A).ρ₁ f =
      substitute (fun _ : Unit => (0 : Fin 3)) f := by
    change substituteRingHom Fin.castSucc (substituteRingHom (fun _ : Unit => (0 : Fin 2)) f) =
      substituteRingHom (fun _ : Unit => (0 : Fin 3)) f
    simp only [substituteRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← substitute_comp]
    rfl
  rw [hρ, substitute_const_apply]
  have hcond : (∀ j : Fin 3, j ≠ 0 → d j = 0) ↔ (d 1 = 0 ∧ d 2 = 0) := by
    constructor
    · intro h; exact ⟨h 1 (by decide), h 2 (by decide)⟩
    · intro h j hj; fin_cases j
      · exact (hj rfl).elim
      · exact h.1
      · exact h.2
  simp only [hcond]

/-- Coefficient formula for `ρ₂ : R₁ → R₃`. -/
lemma novikovCosimplicialRing_ρ₂_apply (f : (novikovCosimplicialRing Γ A).R₁)
    (d : Fin 3 → Γ) :
    ((novikovCosimplicialRing Γ A).ρ₂ f).val d =
      if d 0 = 0 ∧ d 2 = 0 then f.val (fun _ : Unit => d 1) else 0 := by
  have hρ : (novikovCosimplicialRing Γ A).ρ₂ f =
      substitute (fun _ : Unit => (1 : Fin 3)) f := by
    change substituteRingHom Fin.succ (substituteRingHom (fun _ : Unit => (0 : Fin 2)) f) =
      substituteRingHom (fun _ : Unit => (1 : Fin 3)) f
    simp only [substituteRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← substitute_comp]
    rfl
  rw [hρ, substitute_const_apply]
  have hcond : (∀ j : Fin 3, j ≠ 1 → d j = 0) ↔ (d 0 = 0 ∧ d 2 = 0) := by
    constructor
    · intro h; exact ⟨h 0 (by decide), h 2 (by decide)⟩
    · intro h j hj; fin_cases j
      · exact h.1
      · exact (hj rfl).elim
      · exact h.2
  simp only [hcond]

end CoefficientFormulas

/-- The extended cosimplicial ring of Novikov series, with `R₀ = A` and
`π₀ = algebraMapNovikov : A → A((t))`. -/
noncomputable def novikovExtendedCosimplicialRing (Γ : S) (A : Type*) [CommRing A] :
    ExtendedCosimplicialRing where
  toCosimplicialRing := novikovCosimplicialRing Γ A
  R₀ := A
  π₀ := algebraMapNovikov
  π₁_π₀_eq_π₂_π₀ := by
    ext a
    change substituteRingHom _ (algebraMapNovikov a) = substituteRingHom _ (algebraMapNovikov a)
    simp only [substituteRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      substitute_algebraMap]

/-- The equalizer of the two face maps `π₁, π₂` in the Novikov cosimplicial ring
is exactly the image of `algebraMapNovikov`. If a series is the same whether we
embed it as the first or second variable, it must be a constant series. -/
lemma novikovCosimplicialRing_equalizer (Γ : S) {A : Type*} [CommRing A]
    (x : NovikovSeries Γ Unit A)
    (h : (novikovCosimplicialRing Γ A).π₁ x = (novikovCosimplicialRing Γ A).π₂ x) :
    ∃ a : A, x = algebraMapNovikov a := by
  refine ⟨x.val 0, ?_⟩
  ext d
  simp only [algebraMapNovikov, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  by_cases hd : d = 0
  · simp [hd]
  · simp only [hd, ite_false]
    -- Evaluate h at g' : Fin 2 → Γ with g'(0) = d(), g'(1) = 0
    -- LHS gives x.val d, RHS gives 0
    let g' : Fin 2 → Γ := fun j => if j = 0 then d () else 0
    have h' : (substitute (fun _ : Unit => (0 : Fin 2)) x).val g' =
              (substitute (fun _ : Unit => (1 : Fin 2)) x).val g' := by
      have := congr_fun (congr_arg Subtype.val h) g'
      simp only [novikovCosimplicialRing, substituteRingHom] at this
      exact this
    -- Auxiliary: sum over Unit is just the single value
    have sum_unit (g : Unit → Γ) : ∑ i : Unit, g i = g () := by
      simp
    -- Key lemma about pushExponents for the constant-0 map
    have push0 (g : Unit → Γ) : pushExponents (fun _ : Unit => (0 : Fin 2)) g =
        fun j : Fin 2 => if j = 0 then g () else 0 := by
      funext j; simp only [pushExponents]
      by_cases hj : j = 0
      · subst hj
        convert sum_unit g using 1
      · simp only [hj, ↓reduceIte]
        convert Finset.sum_empty using 1
        congr 1; ext ⟨⟩; simp [Ne.symm hj]
    -- Key lemma about pushExponents for the constant-1 map
    have push1 (g : Unit → Γ) : pushExponents (fun _ : Unit => (1 : Fin 2)) g =
        fun j : Fin 2 => if j = 1 then g () else 0 := by
      funext j; simp only [pushExponents]
      by_cases hj : j = 1
      · subst hj
        convert sum_unit g using 1
      · simp only [hj, ↓reduceIte]
        convert Finset.sum_empty using 1
        congr 1; ext ⟨⟩; simp [Ne.symm hj]
    -- If pushExponents (fun _ => 0) g = g', then g () = d ()
    have push0_inj (g : Unit → Γ) (hpg : pushExponents (fun _ : Unit => (0 : Fin 2)) g = g') :
        g = d := by
      funext ⟨⟩
      have h0 := congr_fun hpg 0
      rw [push0] at h0
      simp only [g', ↓reduceIte] at h0
      exact h0
    -- LHS: (substitute (fun _ => 0) x).val g' = x.val d
    have h_lhs : (substitute (fun _ : Unit => (0 : Fin 2)) x).val g' = x.val d := by
      simp only [substitute, substituteFun]
      rw [Finset.sum_eq_single d]
      · intro g hg hgd
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg
        exact (hgd (push0_inj g hg.1)).elim
      · intro habs
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_and, ne_eq, not_not] at habs
        exact habs (push0 d)
    -- RHS: (substitute (fun _ => 1) x).val g' = 0
    have h_rhs : (substitute (fun _ : Unit => (1 : Fin 2)) x).val g' = 0 := by
      simp only [substitute, substituteFun]
      apply Finset.sum_eq_zero
      intro g hg
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hg
      -- pushExponents (fun _ => 1) g = g' means g'(1) = g() and g'(0) = 0
      -- But g'(0) = d() ≠ 0, contradiction
      have h0 := congr_fun hg.1 0
      rw [push1] at h0
      simp only [g', ↓reduceIte] at h0
      -- h0 : 0 = d ()
      exfalso; apply hd
      funext ⟨⟩
      simp only [Pi.zero_apply]
      exact h0.symm
    rw [← h_lhs, h', h_rhs]

/-- A Novikov descent datum is a descent datum for the Novikov cosimplicial ring. -/
abbrev NovikovDescentDatum (Γ : S) (A : Type*) [CommRing A] :=
  DescentDatum (novikovCosimplicialRing Γ A)

/-- The constant-descent functor from finite projective `A`-modules to Novikov descent data. -/
noncomputable def vectToNovikovDescent (Γ : S) (A : Type*) [CommRing A] :
    Novikov.Miscellany.FiniteProjectiveModule A ⥤ NovikovDescentDatum Γ A := by
  change Novikov.Miscellany.FiniteProjectiveModule (novikovExtendedCosimplicialRing Γ A).R₀ ⥤
    DescentDatum (novikovExtendedCosimplicialRing Γ A).toCosimplicialRing
  exact constantDescentDatumFunctor (novikovExtendedCosimplicialRing Γ A)

lemma algebraMapNovikov_injective (Γ : S) (A : Type*) [CommRing A] :
    Function.Injective (algebraMapNovikov : A → NovikovSeries Γ Unit A) := by
  intro a b h
  have h0 := congr_fun (congr_arg Subtype.val h) 0
  simpa [algebraMapNovikov] using h0

lemma novikovExtendedCosimplicialRing_equalizer_bijective (Γ : S) (A : Type*) [CommRing A] :
    let E := novikovExtendedCosimplicialRing Γ A
    Function.Bijective (equalizerMap E) := by
  intro E
  constructor
  · intro a b h
    apply_fun Subtype.val at h
    apply algebraMapNovikov_injective Γ A
    exact h
  · rintro ⟨x, h⟩
    rcases novikovCosimplicialRing_equalizer Γ x h with ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha.symm⟩

/-- The constant-descent functor from finite projective `A`-modules to Novikov
descent data is fully faithful. -/
noncomputable def vectToNovikovDescent_fullyFaithful (Γ : S) (A : Type*) [CommRing A] :
    (vectToNovikovDescent Γ A).FullyFaithful :=
  constantDescentDatumFunctor_fullyFaithful
    (novikovExtendedCosimplicialRing Γ A)
    (novikovExtendedCosimplicialRing_equalizer_bijective Γ A)

end Novikov.Descent
