import Novikov.Descent.Product.Ring
import Mathlib.Tactic.Linarith

/-!
# Support and range combinatorics for product-field descent

This file characterizes the coefficientwise image of Novikov series over a
product ring by uniform finiteness of the fiber-support union.  It then develops
the support-theoretic and numerical lemmas used by the product-field descent
estimate, independently of the chosen fiber trivializations and their
compatibility proof.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract
open scoped BigOperators

namespace Novikov.Descent

noncomputable section

universe u v

variable {S : Type*} [SetLike S ℝ] {Γ : S}

section CoefficientwiseRange

variable [AddSubmonoidClass S ℝ]
variable {ι : Type*} [Fintype ι]
variable {I : Type u} (K : I → Type v) [∀ i, CommRing (K i)]

/-- The union of the supports of a family of Novikov series over the factors of a
product ring. -/
def coeffwiseSupportUnion (x : ∀ i, NovikovSeries Γ ι (K i)) : Set (ι → Γ) :=
  {d | ∃ i, (x i).val d ≠ 0}

/-- A family of fiberwise Novikov series lies in the coefficientwise image if it
comes from a single Novikov series over the product coefficient ring. -/
def InCoeffwiseRange (x : ∀ i, NovikovSeries Γ ι (K i)) : Prop :=
  ∃ y : NovikovSeries Γ ι (∀ i, K i), coeffwisePiRingHom K y = x

/-- Noncomputable lift of a family in the coefficientwise range. -/
noncomputable def coeffwiseRangeLift (x : ∀ i, NovikovSeries Γ ι (K i))
    (hx : InCoeffwiseRange K x) : NovikovSeries Γ ι (∀ i, K i) :=
  Classical.choose hx

@[simp]
lemma coeffwiseRangeLift_spec (x : ∀ i, NovikovSeries Γ ι (K i))
    (hx : InCoeffwiseRange K x) :
    coeffwisePiRingHom K (coeffwiseRangeLift K x hx) = x :=
  Classical.choose_spec hx

/-- If the union of the fiber supports is Novikov-finite, then the family comes
from a Novikov series over the product ring. -/
private lemma inCoeffwiseRange_of_hasNovikovFiniteness_supportUnion
    (x : ∀ i, NovikovSeries Γ ι (K i))
    (hx : hasNovikovFiniteness (coeffwiseSupportUnion K x)) :
    InCoeffwiseRange K x := by
  let yFun : (ι → Γ) → (∀ i, K i) := fun d i => (x i).val d
  have hy : isNovikovSeries yFun := by
    refine hx.subset ?_
    intro d hd
    change yFun d ≠ 0 at hd
    by_contra hnot
    change ¬ ∃ i, (x i).val d ≠ 0 at hnot
    simp only [not_exists, not_ne_iff] at hnot
    exact hd (funext hnot)
  refine ⟨⟨yFun, hy⟩, ?_⟩
  ext i d
  rfl

/-- Any family in the coefficientwise range has Novikov-finite union support. -/
private lemma hasNovikovFiniteness_supportUnion_of_inCoeffwiseRange
    {x : ∀ i, NovikovSeries Γ ι (K i)} (hx : InCoeffwiseRange K x) :
    hasNovikovFiniteness (coeffwiseSupportUnion K x) := by
  rcases hx with ⟨y, hy⟩
  refine y.prop.subset ?_
  intro d hd
  rcases hd with ⟨i, hi⟩
  have hcomp : ((coeffwiseEvalRingHom K i y).val d) = (x i).val d := by
    simpa [coeffwisePiRingHom, coeffwiseEvalRingHom] using
      congrArg (fun z => (z i).val d) hy
  intro hy0
  apply hi
  rw [← hcomp]
  simp [coeffwiseEvalRingHom, mapRingHom_apply, hy0]

/-- A family of fiber Novikov series is in the coefficientwise image iff its union
support is Novikov-finite. -/
lemma inCoeffwiseRange_iff_hasNovikovFiniteness_supportUnion
    (x : ∀ i, NovikovSeries Γ ι (K i)) :
    InCoeffwiseRange K x ↔ hasNovikovFiniteness (coeffwiseSupportUnion K x) :=
  ⟨hasNovikovFiniteness_supportUnion_of_inCoeffwiseRange K,
    inCoeffwiseRange_of_hasNovikovFiniteness_supportUnion K x⟩

lemma inCoeffwiseRange_finset_sum {α : Type*} (s : Finset α)
    (x : α → ∀ i, NovikovSeries Γ ι (K i))
    (hx : ∀ a, InCoeffwiseRange K (x a)) :
    InCoeffwiseRange K (fun i => (∑ a ∈ s, x a i)) := by
  refine ⟨(∑ a ∈ s, coeffwiseRangeLift K (x a) (hx a)), ?_⟩
  ext i d
  simp

/-- Multiplication by a series that already comes from the product coefficient
ring preserves the coefficientwise range. -/
lemma inCoeffwiseRange_mul_left (a : NovikovSeries Γ ι (∀ i, K i))
    {x : ∀ i, NovikovSeries Γ ι (K i)} (hx : InCoeffwiseRange K x) :
    InCoeffwiseRange K (fun i => coeffwiseEvalRingHom K i a * x i) := by
  refine ⟨a * coeffwiseRangeLift K x hx, ?_⟩
  rw [map_mul, coeffwiseRangeLift_spec]
  rfl

end CoefficientwiseRange

/-- A Novikov-finite support is bounded below for every positive linear weight. -/
lemma hasNovikovFiniteness.exists_weighted_lower_bound {ι : Type*} [Fintype ι]
    {T : Set (ι → Γ)} (hT : hasNovikovFiniteness T)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ C : ℝ, ∀ d ∈ T, C ≤ ∑ i, w i * (d i : ℝ) := by
  let W : (ι → Γ) → ℝ := fun d => ∑ i, w i * (d i : ℝ)
  let B : Set (ι → Γ) := {d | d ∈ T ∧ W d < 0}
  have hB : B.Finite := hT w hw 0
  obtain ⟨C, hC⟩ := (hB.image W).bddBelow
  refine ⟨min C 0, ?_⟩
  intro d hd
  by_cases hneg : W d < 0
  · exact (min_le_left C 0).trans (hC ⟨d, ⟨hd, hneg⟩, rfl⟩)
  · exact (min_le_right C 0).trans (le_of_not_gt hneg)

/-- A finite family of predicates with lower bounds admits one common lower
bound. -/
lemma exists_common_lower_bound_fintype {α β : Type*} [Fintype α]
    (W : β → ℝ) (P : α → β → Prop)
    (h : ∀ a, ∃ C : ℝ, ∀ b, P a b → C ≤ W b) :
    ∃ C : ℝ, ∀ a b, P a b → C ≤ W b := by
  choose C hC using h
  obtain ⟨C₀, hC₀⟩ := Finite.exists_ge C
  exact ⟨C₀, fun a b hab => (hC₀ a).trans (hC a b hab)⟩

/-- Weight `(x,y) ↦ 2*x + y`, expressed as a positive weight vector. -/
def twoOneWeight : Fin 2 → ℝ := fun i => if i = 0 then 2 else 1

lemma twoOneWeight_pos (i : Fin 2) : 0 < twoOneWeight i := by
  by_cases hi : i = 0
  · simp [twoOneWeight, hi]
  · simp [twoOneWeight, hi]

/-- Abstract numerical core of the generator lower-bound argument.  If each
minimal generator exponent is related to a transition exponent whose support is
bounded below for `(x,y) ↦ 2*x + y`, then all generator exponents are bounded
below by the same constant. -/
private lemma lower_bound_of_transition_relation {I J : Type*}
    (G : I → J → Set ℝ) (A : I → J → J → Set (ℝ × ℝ)) (C : ℝ)
    (hA : ∀ i j k p, p ∈ A i j k → C ≤ 2 * p.1 + p.2)
    (hrel : ∀ i j x, x ∈ G i j →
      ∃ k p y, p ∈ A i j k ∧ y ∈ G i k ∧ p.1 = x ∧ p.2 + y = 0)
    (hmin : ∀ i, (∃ x, ∃ j, x ∈ G i j) →
      ∃ D, (∃ j, D ∈ G i j) ∧ ∀ x j, x ∈ G i j → D ≤ x) :
    ∀ i j x, x ∈ G i j → C ≤ x := by
  intro i j x hx
  rcases hmin i ⟨x, j, hx⟩ with ⟨D, ⟨jD, hDjD⟩, hDmin⟩
  rcases hrel i jD D hDjD with ⟨k, p, y, hpA, hyG, hp1, hp2⟩
  have hC : C ≤ 2 * p.1 + p.2 := hA i jD k p hpA
  have hDy : D ≤ y := hDmin y k hyG
  have hDx : D ≤ x := hDmin x j hx
  rw [hp1] at hC
  linarith

/-- In one exponent variable, Novikov finiteness follows from finiteness below
each strict cutoff. -/
private lemma hasNovikovFiniteness_unit_of_finite_below
    {T : Set (Unit → Γ)}
    (h : ∀ C : ℝ, {d ∈ T | (d () : ℝ) < C}.Finite) :
    hasNovikovFiniteness T := by
  intro s hs C
  refine Set.Finite.subset (h (C / s ())) ?_
  intro d hd
  rcases hd with ⟨hdT, hdlt⟩
  refine ⟨hdT, ?_⟩
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton] at hdlt
  exact (lt_div_iff₀' (hs ())).2 hdlt

/-- In one exponent variable, Novikov finiteness implies finiteness below each
strict cutoff. -/
private lemma finite_below_of_hasNovikovFiniteness_unit
    {T : Set (Unit → Γ)} (hT : hasNovikovFiniteness T) (C : ℝ) :
    {d ∈ T | (d () : ℝ) < C}.Finite := by
  simpa using hT (fun _ : Unit => (1 : ℝ)) (fun _ => zero_lt_one) C

/-- In one exponent variable, Novikov finiteness implies finiteness below each
closed cutoff. -/
private lemma finite_le_of_hasNovikovFiniteness_unit
    {T : Set (Unit → Γ)} (hT : hasNovikovFiniteness T) (C : ℝ) :
    {d ∈ T | (d () : ℝ) ≤ C}.Finite := by
  refine Set.Finite.subset (finite_below_of_hasNovikovFiniteness_unit hT (C + 1)) ?_
  intro d hd
  exact ⟨hd.1, lt_of_le_of_lt hd.2 (by linarith)⟩

/-- In one exponent variable, Novikov finiteness follows from finiteness below
each closed cutoff. -/
private lemma hasNovikovFiniteness_unit_of_finite_le
    [AddSubmonoidClass S ℝ] {T : Set (Unit → Γ)}
    (h : ∀ C : ℝ, {d ∈ T | (d () : ℝ) ≤ C}.Finite) :
    hasNovikovFiniteness T :=
  hasNovikovFiniteness_unit_of_finite_below (fun C =>
    Set.Finite.subset (h C) (fun _ hd => ⟨hd.1, le_of_lt hd.2⟩))

/-- Real-valued support of a one-variable Novikov series. -/
def oneVarSupportReal {A : Type*} [AddCommGroup A] [AddSubmonoidClass S ℝ]
    (x : NovikovSeries Γ Unit A) : Set ℝ :=
  {r | ∃ d, x d ≠ 0 ∧ r = (d () : ℝ)}

/-- Real-valued support union of a finite family of one-variable Novikov series. -/
private def oneVarSupportRealUnion {J A : Type*} [Fintype J] [AddCommGroup A]
    [AddSubmonoidClass S ℝ] (x : J → NovikovSeries Γ Unit A) : Set ℝ :=
  {r | ∃ j d, x j d ≠ 0 ∧ r = (d () : ℝ)}

private lemma oneVarSupportReal_subset_union {J A : Type*} [Fintype J] [AddCommGroup A]
    [AddSubmonoidClass S ℝ] (x : J → NovikovSeries Γ Unit A) (j : J) :
    oneVarSupportReal (x j) ⊆ oneVarSupportRealUnion x := by
  intro r hr
  rcases hr with ⟨d, hd, rfl⟩
  exact ⟨j, d, hd, rfl⟩

/-- A finite family of one-variable Novikov supports is finite below each closed
real cutoff, after coercing exponents to real numbers. -/
private lemma oneVarSupportRealUnion_finite_le {J A : Type*} [Fintype J] [AddCommGroup A]
    [AddSubmonoidClass S ℝ] (x : J → NovikovSeries Γ Unit A) (C : ℝ) :
    {r ∈ oneVarSupportRealUnion x | r ≤ C}.Finite := by
  let B : J → Set (Unit → Γ) := fun j => {d | x j d ≠ 0 ∧ (d () : ℝ) ≤ C}
  have hB : ∀ j, (B j).Finite := fun j => finite_le_of_hasNovikovFiniteness_unit (x j).prop C
  let U : Set ℝ := ⋃ j, (fun d : Unit → Γ => (d () : ℝ)) '' B j
  have hU : U.Finite := by
    simpa [U] using Set.finite_iUnion (fun j => (hB j).image (fun d : Unit → Γ => (d () : ℝ)))
  refine Set.Finite.subset hU ?_
  intro r hr
  rcases hr with ⟨hrT, hrle⟩
  rcases hrT with ⟨j, d, hd, rfl⟩
  exact Set.mem_iUnion.2 ⟨j, ⟨d, ⟨hd, hrle⟩, rfl⟩⟩

/-- A nonempty finite family of one-variable Novikov supports has a least real
exponent after coercing exponents to real numbers. -/
private lemma oneVarSupportRealUnion_exists_min {J A : Type*} [Fintype J] [AddCommGroup A]
    [AddSubmonoidClass S ℝ]
    (x : J → NovikovSeries Γ Unit A) (hne : (oneVarSupportRealUnion x).Nonempty) :
    ∃ D ∈ oneVarSupportRealUnion x, ∀ r ∈ oneVarSupportRealUnion x, D ≤ r := by
  rcases hne with ⟨r0, hr0⟩
  let Tle : Set ℝ := {r | r ∈ oneVarSupportRealUnion x ∧ r ≤ r0}
  have hTle_fin : Tle.Finite := oneVarSupportRealUnion_finite_le x r0
  have hTle_ne : Tle.Nonempty := ⟨r0, hr0, le_rfl⟩
  rcases Set.exists_min_image Tle (fun r : ℝ => r) hTle_fin hTle_ne with
    ⟨D, hDle, hDmin⟩
  refine ⟨D, hDle.1, ?_⟩
  intro r hr
  by_cases hrle : r ≤ r0
  · exact hDmin r ⟨hr, hrle⟩
  · have hDr0 : D ≤ r0 := hDle.2
    have hr0r : r0 < r := lt_of_not_ge hrle
    exact le_trans hDr0 (le_of_lt hr0r)

/-- A nonempty finite family of one-variable Novikov supports has a least real
exponent, stated in terms of the individual support sets. -/
private lemma oneVarSupportRealUnion_exists_min_for_family {J A : Type*} [Fintype J]
    [AddCommGroup A] [AddSubmonoidClass S ℝ]
    (x : J → NovikovSeries Γ Unit A)
    (hne : ∃ r, ∃ j, r ∈ oneVarSupportReal (x j)) :
    ∃ D, (∃ j, D ∈ oneVarSupportReal (x j)) ∧
      ∀ r j, r ∈ oneVarSupportReal (x j) → D ≤ r := by
  rcases hne with ⟨r0, j0, hr0⟩
  have hneU : (oneVarSupportRealUnion x).Nonempty :=
    ⟨r0, oneVarSupportReal_subset_union x j0 hr0⟩
  rcases oneVarSupportRealUnion_exists_min x hneU with ⟨D, hDU, hDmin⟩
  rcases hDU with ⟨jD, dD, hdD, hD⟩
  refine ⟨D, ?_, ?_⟩
  · exact ⟨jD, dD, hdD, hD⟩
  · intro r j hr
    exact hDmin r (oneVarSupportReal_subset_union x j hr)

/-- Instantiation of `lower_bound_of_transition_relation` for finite families of
one-variable Novikov series. -/
lemma lower_bound_of_series_transition_relation
    {I J : Type*} [Fintype J]
    {A : I → Type*} [∀ i, AddCommGroup (A i)] [AddSubmonoidClass S ℝ]
    (g : ∀ i, J → NovikovSeries Γ Unit (A i))
    (T : I → J → J → Set (ℝ × ℝ)) (C : ℝ)
    (hT : ∀ i j k p, p ∈ T i j k → C ≤ 2 * p.1 + p.2)
    (hrel : ∀ i j x, x ∈ oneVarSupportReal (g i j) →
      ∃ k p y, p ∈ T i j k ∧ y ∈ oneVarSupportReal (g i k) ∧ p.1 = x ∧ p.2 + y = 0) :
    ∀ i j x, x ∈ oneVarSupportReal (g i j) → C ≤ x := by
  intro i j x hx
  refine lower_bound_of_transition_relation
      (fun i j => oneVarSupportReal (g i j)) T C hT hrel ?_ i j x hx
  intro i hne
  exact oneVarSupportRealUnion_exists_min_for_family (g i) hne

/-- Real-valued support union of a finite family of two-variable Novikov series. -/
def twoVarSupportRealUnion {J A : Type*} [Fintype J] [AddCommGroup A]
    [AddSubmonoidClass S ℝ] (a : J → NovikovSeries Γ (Fin 2) A) : Set (ℝ × ℝ) :=
  {p | ∃ j d, a j d ≠ 0 ∧ p = ((d 0 : ℝ), (d 1 : ℝ))}

/-- A finite family of two-variable Novikov supports is finite under each closed
`x + y` cutoff, after coercing exponents to real numbers. -/
private lemma twoVarSupportRealUnion_finite_weighted_le {J A : Type*} [Fintype J] [AddCommGroup A]
    [AddSubmonoidClass S ℝ] (a : J → NovikovSeries Γ (Fin 2) A) (C : ℝ) :
    {p ∈ twoVarSupportRealUnion a | p.1 + p.2 ≤ C}.Finite := by
  let B : J → Set (Fin 2 → Γ) := fun j =>
    {d | a j d ≠ 0 ∧ (d 0 : ℝ) + (d 1 : ℝ) ≤ C}
  have hB : ∀ j, (B j).Finite := by
    intro j
    refine Set.Finite.subset ((a j).prop (fun _ : Fin 2 => (1 : ℝ)) (fun _ => zero_lt_one) (C + 1)) ?_
    intro d hd
    rcases hd with ⟨hdnz, hdle⟩
    refine ⟨hdnz, ?_⟩
    rw [Fin.sum_univ_two]
    simp only [one_mul]
    linarith
  let U : Set (ℝ × ℝ) := ⋃ j, (fun d : Fin 2 → Γ => ((d 0 : ℝ), (d 1 : ℝ))) '' B j
  have hU : U.Finite := by
    simpa [U] using Set.finite_iUnion
      (fun j => (hB j).image (fun d : Fin 2 → Γ => ((d 0 : ℝ), (d 1 : ℝ))))
  refine Set.Finite.subset hU ?_
  intro p hp
  rcases hp with ⟨hpT, hple⟩
  rcases hpT with ⟨j, d, hdnz, rfl⟩
  exact Set.mem_iUnion.2 ⟨j, ⟨d, ⟨hdnz, hple⟩, rfl⟩⟩

/-- A numerical lower bound on the one-variable exponent yields finiteness of
possible second-coordinate values below each combined cutoff. -/
lemma twoVarSupportRealUnion_y_finite_of_lower_bound'
    {JA A : Type*} [Fintype JA] [AddCommGroup A] [AddSubmonoidClass S ℝ]
    (a : JA → NovikovSeries Γ (Fin 2) A)
    (D C : ℝ) :
    {y | ∃ p x,
        p ∈ twoVarSupportRealUnion a ∧ D ≤ x ∧ y = p.2 ∧ p.1 + x + p.2 ≤ C}.Finite := by
  let P : Set (ℝ × ℝ) := {p ∈ twoVarSupportRealUnion a | p.1 + p.2 ≤ C - D}
  have hP : P.Finite := twoVarSupportRealUnion_finite_weighted_le a (C - D)
  refine Set.Finite.subset (hP.image Prod.snd) ?_
  intro y hy
  rcases hy with ⟨p, x, hp, hDx, rfl, hsum⟩
  refine ⟨p, ⟨hp, ?_⟩, rfl⟩
  linarith

/-- The real-exponent map on one-variable exponents has finite preimages of
finite sets. -/
lemma unitExponentReal_preimage_finite (Y : Set ℝ) (hY : Y.Finite) :
    {d : Unit → Γ | (d () : ℝ) ∈ Y}.Finite := by
  refine hY.preimage ?_
  intro d hd e he hde
  ext u
  have hu : u = () := Subsingleton.elim u ()
  subst hu
  exact hde

/-- Coefficient of a finite sum of Novikov series. -/
private lemma novikovSeries_univ_sum_apply {ι A α : Type*} [Fintype ι] [AddCommGroup A] [Fintype α]
    [AddSubmonoidClass S ℝ] (f : α → NovikovSeries Γ ι A) (d : ι → Γ) :
    (∑ a : α, f a).val d = ∑ a : α, (f a).val d := by
  classical
  simp

/-- A nonzero coefficient of a finite sum of products has a supporting
summand and a decomposition of its exponent. -/
private lemma exists_mul_support_of_sum_coeff_ne
    {ι J A : Type*} [Fintype ι] [Fintype J] [CommRing A]
    [AddSubmonoidClass S ℝ]
    (a b : J → NovikovSeries Γ ι A) (d : ι → Γ)
    (h : ((∑ k : J, a k * b k) : NovikovSeries Γ ι A).val d ≠ 0) :
    ∃ k e q, (a k).val e ≠ 0 ∧ (b k).val q ≠ 0 ∧ e + q = d := by
  have hsum_eval :
      ((∑ k : J, a k * b k) : NovikovSeries Γ ι A).val d =
        ∑ k : J, ((a k * b k) : NovikovSeries Γ ι A).val d :=
    novikovSeries_univ_sum_apply (fun k : J => a k * b k) d
  have hsum_ne :
      (∑ k : J, ((a k * b k) : NovikovSeries Γ ι A).val d) ≠ 0 := by
    intro hzero
    apply h
    rw [hsum_eval, hzero]
  rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_ne with ⟨k, _hk_mem, hk_ne⟩
  have hprod_mem : d ∈ ((a k * b k) : NovikovSeries Γ ι A).support := hk_ne
  have hsub := support_mul_subset (a k) (b k) (AddMonoidHom.mul) hprod_mem
  rw [Set.mem_add] at hsub
  rcases hsub with ⟨e, he, q, hq, heq⟩
  rw [NovikovSeries.mem_support] at he hq
  exact ⟨k, e, q, he, hq, heq⟩

/-- A coordinate identity of the form `π₁ g_j = ∑ₖ a_jk π₂ g_k`
produces the forward support relation used in the lower-bound argument. -/
lemma forward_relation_of_coord_eq {J A : Type*} [Fintype J] [CommRing A]
    (g : J → (realC A).R₁) (a : J → J → (realC A).R₂)
    (hcoord : ∀ j, (realC A).π₁ (g j) = ∑ k : J, a j k * (realC A).π₂ (g k)) :
    ∀ j x, x ∈ oneVarSupportReal (Γ := (⊤ : AddSubgroup ℝ)) (g j) →
      ∃ k p y,
        (∃ d : Fin 2 → (⊤ : AddSubgroup ℝ), (a j k).val d ≠ 0 ∧
          p = ((d 0 : ℝ), (d 1 : ℝ))) ∧
        y ∈ oneVarSupportReal (Γ := (⊤ : AddSubgroup ℝ)) (g k) ∧
        p.1 = x ∧ p.2 + y = 0 := by
  intro j x hx
  rcases hx with ⟨dx, hdx, rfl⟩
  let d2 : Fin 2 → (⊤ : AddSubgroup ℝ) := fun r => if r = 0 then dx () else 0
  have hd2_zero : d2 1 = 0 := by simp [d2]
  have hd2_dx : (fun _ : Unit => d2 0) = dx := by
    ext u
    simp [d2]
  have hπ1_ne : ((realC A).π₁ (g j)).val d2 ≠ 0 := by
    rw [novikovCosimplicialRing_π₁_apply]
    simp [hd2_zero, hd2_dx, hdx]
  have hval := congrArg (fun z : (realC A).R₂ => z.val d2) (hcoord j)
  have hrhs_ne : ((∑ k : J, a j k * (realC A).π₂ (g k)) : (realC A).R₂).val d2 ≠ 0 := by
    intro hzero
    apply hπ1_ne
    simpa using hval.trans hzero
  rcases exists_mul_support_of_sum_coeff_ne
      (fun k : J => a j k) (fun k : J => (realC A).π₂ (g k)) d2 hrhs_ne with
    ⟨k, e, q, heA, hqπ2, heq⟩
  rw [novikovCosimplicialRing_π₂_apply] at hqπ2
  have hq0 : q 0 = 0 := by
    by_contra hq0
    simp [hq0] at hqπ2
  have hgq : (g k).val (fun _ : Unit => q 1) ≠ 0 := by
    simpa [hq0] using hqπ2
  let p : ℝ × ℝ := ((e 0 : ℝ), (e 1 : ℝ))
  let y : ℝ := (q 1 : ℝ)
  refine ⟨k, p, y, ?_, ?_, ?_, ?_⟩
  · exact ⟨e, heA, rfl⟩
  · exact ⟨fun _ : Unit => q 1, hgq, rfl⟩
  · dsimp [p, d2] at heq ⊢
    have h0 := congrFun heq 0
    have h0' : e 0 = dx () := by simpa [hq0, d2] using h0
    exact congrArg Subtype.val h0'
  · dsimp [p, y] at heq ⊢
    have h1 := congrFun heq 1
    have h1' : e 1 + q 1 = 0 := by simpa [d2] using h1
    have h1r := congrArg Subtype.val h1'
    simpa using h1r

/-- A coordinate identity of the form `π₂ g_j = ∑ₖ b_jk π₁ g_k`
produces the inverse support relation used in the finite-below argument. -/
lemma inverse_relation_of_coord_eq {J A : Type*} [Fintype J] [CommRing A]
    (g : J → (realC A).R₁) (b : J → J → (realC A).R₂)
    (hcoord : ∀ j, (realC A).π₂ (g j) = ∑ k : J, b j k * (realC A).π₁ (g k)) :
    ∀ j y, y ∈ oneVarSupportReal (Γ := (⊤ : AddSubgroup ℝ)) (g j) →
      ∃ k p x,
        (∃ d : Fin 2 → (⊤ : AddSubgroup ℝ), (b j k).val d ≠ 0 ∧
          p = ((d 0 : ℝ), (d 1 : ℝ))) ∧
        x ∈ oneVarSupportReal (Γ := (⊤ : AddSubgroup ℝ)) (g k) ∧
        p.1 + x = 0 ∧ p.2 = y := by
  intro j y hy
  rcases hy with ⟨dy, hdy, rfl⟩
  let d2 : Fin 2 → (⊤ : AddSubgroup ℝ) := fun r => if r = 0 then 0 else dy ()
  have hd2_zero : d2 0 = 0 := by simp [d2]
  have hd2_dy : (fun _ : Unit => d2 1) = dy := by
    ext u
    simp [d2]
  have hπ2_ne : ((realC A).π₂ (g j)).val d2 ≠ 0 := by
    rw [novikovCosimplicialRing_π₂_apply]
    simp [hd2_zero, hd2_dy, hdy]
  have hval := congrArg (fun z : (realC A).R₂ => z.val d2) (hcoord j)
  have hrhs_ne : ((∑ k : J, b j k * (realC A).π₁ (g k)) : (realC A).R₂).val d2 ≠ 0 := by
    intro hzero
    apply hπ2_ne
    simpa using hval.trans hzero
  rcases exists_mul_support_of_sum_coeff_ne
      (fun k : J => b j k) (fun k : J => (realC A).π₁ (g k)) d2 hrhs_ne with
    ⟨k, e, q, heB, hqπ1, heq⟩
  rw [novikovCosimplicialRing_π₁_apply] at hqπ1
  have hq1 : q 1 = 0 := by
    by_contra hq1
    simp [hq1] at hqπ1
  have hgq : (g k).val (fun _ : Unit => q 0) ≠ 0 := by
    simpa [hq1] using hqπ1
  let p : ℝ × ℝ := ((e 0 : ℝ), (e 1 : ℝ))
  let x : ℝ := (q 0 : ℝ)
  refine ⟨k, p, x, ?_, ?_, ?_, ?_⟩
  · exact ⟨e, heB, rfl⟩
  · exact ⟨fun _ : Unit => q 0, hgq, rfl⟩
  · dsimp [p, x] at heq ⊢
    have h0 := congrFun heq 0
    have h0' : e 0 + q 0 = 0 := by simpa [d2] using h0
    have h0r := congrArg Subtype.val h0'
    simpa using h0r
  · dsimp [p, d2] at heq ⊢
    have h1 := congrFun heq 1
    have h1' : e 1 = dy () := by simpa [hq1, d2] using h1
    exact congrArg Subtype.val h1'

variable {I : Type u} (K : I → Type v) [∀ i, CommRing (K i)]

/-- A one-variable family of fiber Novikov series lies in the coefficientwise
range if the union of its fiber supports is finite below each closed cutoff. -/
lemma inCoeffwiseRange_unit_of_finite_le [AddSubmonoidClass S ℝ]
    {x : ∀ i, NovikovSeries Γ Unit (K i)}
    (h : ∀ C : ℝ, {d ∈ coeffwiseSupportUnion K x | (d () : ℝ) ≤ C}.Finite) :
    InCoeffwiseRange K x := by
  rw [inCoeffwiseRange_iff_hasNovikovFiniteness_supportUnion]
  exact hasNovikovFiniteness_unit_of_finite_le h

end

end Novikov.Descent
