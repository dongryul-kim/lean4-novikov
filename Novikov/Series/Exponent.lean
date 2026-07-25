import Novikov.Series.Module

open BigOperators Pointwise

/-!
# Extension of Novikov exponents

This file defines extension by zero from Novikov series with exponents in an
additive submonoid `Γ ⊆ ℝ` to Novikov series with arbitrary real exponents.  It
also characterizes the range as the real-exponent series supported on `Γ` and
defines coefficient restriction in the other direction.
-/

namespace Novikov

variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ]
variable (Γ : S)

/-- The canonical additive embedding of an exponent submonoid into the real
exponent group. -/
def realExponentInclusion : Γ →+ (⊤ : AddSubgroup ℝ) where
  toFun d := ⟨(d : ℝ), by simp⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- Include an exponent vector with entries in `Γ` into a real exponent vector. -/
def includeExponent {ι : Type*} (d : ι → Γ) : ι → (⊤ : AddSubgroup ℝ) :=
  fun i => realExponentInclusion Γ (d i)

lemma includeExponent_injective {ι : Type*} :
    Function.Injective (includeExponent (ι := ι) Γ) := by
  intro d e h
  funext i
  exact Subtype.ext
    (congrArg (fun z : (⊤ : AddSubgroup ℝ) => (z : ℝ)) (congrFun h i))

/-- Coordinatewise exponent inclusion as an additive homomorphism. -/
def includeExponentAddHom {ι : Type*} :
    (ι → Γ) →+ (ι → (⊤ : AddSubgroup ℝ)) where
  toFun := includeExponent Γ
  map_zero' := by
    funext i
    apply Subtype.ext
    simp [includeExponent, realExponentInclusion]
  map_add' d e := by
    funext i
    apply Subtype.ext
    simp [includeExponent, realExponentInclusion]

@[simp]
lemma includeExponentAddHom_apply {ι : Type*} (d : ι → Γ) :
    includeExponentAddHom Γ d = includeExponent Γ d := rfl

@[simp]
lemma includeExponent_zero {ι : Type*} :
    includeExponent Γ (0 : ι → Γ) = 0 :=
  (includeExponentAddHom Γ).map_zero

@[simp]
lemma includeExponent_add {ι : Type*} (d e : ι → Γ) :
    includeExponent Γ (d + e) = includeExponent Γ d + includeExponent Γ e :=
  (includeExponentAddHom Γ).map_add d e

/-- A real-exponent Novikov series is supported on `Γ` if every coordinate of
any exponent with nonzero coefficient belongs to `Γ`. -/
def HasExponentSupport {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) ι M) : Prop :=
  ∀ d, x.val d ≠ 0 → ∀ i, (d i : ℝ) ∈ Γ

private noncomputable def extendExponentsFun {ι M : Type*} [Fintype ι]
    [AddCommGroup M] (x : NovikovSeries Γ ι M)
    (d : ι → (⊤ : AddSubgroup ℝ)) : M := by
  classical
  exact if h : ∀ i, (d i : ℝ) ∈ Γ then
    x.val (fun i => ⟨(d i : ℝ), h i⟩)
  else 0

private lemma isNovikovSeries_extendExponentsFun {ι M : Type*} [Fintype ι]
    [AddCommGroup M] (x : NovikovSeries Γ ι M) :
    isNovikovSeries (extendExponentsFun Γ x) := by
  classical
  intro w hw C
  let T : Set (ι → Γ) :=
    {d | x.val d ≠ 0 ∧ ∑ i, w i * (d i : ℝ) < C}
  have hT : T.Finite := x.prop w hw C
  apply (hT.image (includeExponent Γ)).subset
  intro d hd
  simp only [Set.mem_setOf_eq] at hd ⊢
  have hmem : ∀ i, (d i : ℝ) ∈ Γ := by
    by_contra h
    exact hd.1 (by simp [extendExponentsFun, h])
  let dΓ : ι → Γ := fun i => ⟨(d i : ℝ), hmem i⟩
  refine ⟨dΓ, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa [extendExponentsFun, hmem, dΓ] using hd.1
    · simpa [dΓ] using hd.2
  · funext i
    rfl

/-- Extend a `Γ`-exponent Novikov series to real exponents by zero. -/
noncomputable def extendExponents {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (x : NovikovSeries Γ ι M) :
    NovikovSeries (⊤ : AddSubgroup ℝ) ι M :=
  ⟨extendExponentsFun Γ x, isNovikovSeries_extendExponentsFun Γ x⟩

@[simp]
lemma extendExponents_apply_include {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (x : NovikovSeries Γ ι M) (d : ι → Γ) :
    (extendExponents Γ x).val (includeExponent Γ d) = x.val d := by
  classical
  simp [extendExponents, extendExponentsFun, includeExponent, realExponentInclusion]

lemma extendExponents_apply_of_not_mem {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (x : NovikovSeries Γ ι M) (d : ι → (⊤ : AddSubgroup ℝ))
    (h : ¬ ∀ i, (d i : ℝ) ∈ Γ) :
    (extendExponents Γ x).val d = 0 := by
  classical
  simp [extendExponents, extendExponentsFun, h]

lemma extendExponents_injective {ι M : Type*} [Fintype ι] [AddCommGroup M] :
    Function.Injective
      (extendExponents Γ : NovikovSeries Γ ι M →
        NovikovSeries (⊤ : AddSubgroup ℝ) ι M) := by
  intro x y h
  apply NovikovSeries.ext
  intro d
  have hd := congrFun (congrArg Subtype.val h) (includeExponent Γ d)
  simpa using hd

lemma hasExponentSupport_extendExponents {ι M : Type*} [Fintype ι]
    [AddCommGroup M] (x : NovikovSeries Γ ι M) :
    HasExponentSupport Γ (extendExponents Γ x) := by
  intro d hd i
  by_contra hi
  apply hd
  exact extendExponents_apply_of_not_mem Γ x d (fun h => hi (h i))

private def restrictExponentsFun {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) ι M) (d : ι → Γ) : M :=
  x.val (includeExponent Γ d)

private lemma isNovikovSeries_restrictExponentsFun {ι M : Type*} [Fintype ι]
    [AddCommGroup M] (x : NovikovSeries (⊤ : AddSubgroup ℝ) ι M) :
    isNovikovSeries (restrictExponentsFun Γ x) := by
  intro w hw C
  let T : Set (ι → Γ) :=
    {d | x.val (includeExponent Γ d) ≠ 0 ∧
      ∑ i, w i * (d i : ℝ) < C}
  let U : Set (ι → (⊤ : AddSubgroup ℝ)) :=
    {d | x.val d ≠ 0 ∧ ∑ i, w i * (d i : ℝ) < C}
  have hU : U.Finite := x.prop w hw C
  have himage : ((includeExponent Γ) '' T).Finite := by
    apply hU.subset
    rintro d ⟨e, he, rfl⟩
    exact ⟨he.1, by simpa [includeExponent, realExponentInclusion] using he.2⟩
  apply himage.of_finite_image
  exact (includeExponent_injective Γ).injOn

/-- Restrict a real-exponent Novikov series to coefficients with exponents in
`Γ`. -/
def restrictExponents {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) ι M) : NovikovSeries Γ ι M :=
  ⟨restrictExponentsFun Γ x, isNovikovSeries_restrictExponentsFun Γ x⟩

@[simp]
lemma restrictExponents_apply {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) ι M) (d : ι → Γ) :
    (restrictExponents Γ x).val d = x.val (includeExponent Γ d) := rfl

@[simp]
lemma restrictExponents_zero {ι M : Type*} [Fintype ι] [AddCommGroup M] :
    restrictExponents Γ
      (0 : NovikovSeries (⊤ : AddSubgroup ℝ) ι M) = 0 := by
  ext d
  rfl

lemma restrictExponents_add {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (x y : NovikovSeries (⊤ : AddSubgroup ℝ) ι M) :
    restrictExponents Γ (x + y) =
      restrictExponents Γ x + restrictExponents Γ y := by
  ext d
  rfl

/-- Restriction of real exponents to `Γ` as an additive homomorphism. -/
def restrictExponentsAddHom {ι M : Type*} [Fintype ι] [AddCommGroup M] :
    NovikovSeries (⊤ : AddSubgroup ℝ) ι M →+ NovikovSeries Γ ι M where
  toFun := restrictExponents Γ
  map_zero' := restrictExponents_zero Γ
  map_add' := restrictExponents_add Γ

@[simp]
lemma restrictExponentsAddHom_apply {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) ι M) :
    restrictExponentsAddHom Γ x = restrictExponents Γ x := rfl

@[simp]
lemma restrictExponents_extendExponents {ι M : Type*} [Fintype ι]
    [AddCommGroup M] (x : NovikovSeries Γ ι M) :
    restrictExponents Γ (extendExponents Γ x) = x := by
  classical
  ext d
  simp

lemma extendExponents_restrictExponents {ι M : Type*} [Fintype ι]
    [AddCommGroup M] (x : NovikovSeries (⊤ : AddSubgroup ℝ) ι M)
    (hx : HasExponentSupport Γ x) :
    extendExponents Γ (restrictExponents Γ x) = x := by
  classical
  ext d
  by_cases hmem : ∀ i, (d i : ℝ) ∈ Γ
  · let dΓ : ι → Γ := fun i => ⟨(d i : ℝ), hmem i⟩
    have hinc : includeExponent Γ dΓ = d := by
      funext i
      rfl
    rw [show d = includeExponent Γ dΓ from hinc.symm]
    simp
  · rw [extendExponents_apply_of_not_mem Γ _ d hmem]
    symm
    by_contra hd
    exact hmem (hx d hd)

lemma mem_range_extendExponents_iff {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (x : NovikovSeries (⊤ : AddSubgroup ℝ) ι M) :
    x ∈ Set.range
        (extendExponents Γ : NovikovSeries Γ ι M →
          NovikovSeries (⊤ : AddSubgroup ℝ) ι M) ↔
      HasExponentSupport Γ x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact hasExponentSupport_extendExponents Γ y
  · intro hx
    exact ⟨restrictExponents Γ x, extendExponents_restrictExponents Γ x hx⟩

@[simp]
lemma extendExponents_zero {ι M : Type*} [Fintype ι] [AddCommGroup M] :
    extendExponents Γ (0 : NovikovSeries Γ ι M) = 0 := by
  classical
  ext d
  by_cases hmem : ∀ i, (d i : ℝ) ∈ Γ
  · simp [extendExponents, extendExponentsFun, hmem]
  · simp [extendExponents_apply_of_not_mem Γ _ d hmem]

lemma extendExponents_add {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (x y : NovikovSeries Γ ι M) :
    extendExponents Γ (x + y) = extendExponents Γ x + extendExponents Γ y := by
  classical
  ext d
  by_cases hmem : ∀ i, (d i : ℝ) ∈ Γ
  · simp [extendExponents, extendExponentsFun, hmem]
  · simp [extendExponents_apply_of_not_mem Γ _ d hmem]

/-- Extension by zero as an additive homomorphism. -/
noncomputable def extendExponentsAddHom {ι M : Type*} [Fintype ι] [AddCommGroup M] :
    NovikovSeries Γ ι M →+ NovikovSeries (⊤ : AddSubgroup ℝ) ι M where
  toFun := extendExponents Γ
  map_zero' := extendExponents_zero Γ
  map_add' := extendExponents_add Γ

@[simp]
lemma extendExponentsAddHom_apply {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (x : NovikovSeries Γ ι M) :
    extendExponentsAddHom Γ x = extendExponents Γ x := rfl

/-- Extension of exponents commutes with convolution by a biadditive
coefficient map. -/
lemma extendExponents_novikovSeriesMul {ι A B C : Type*} [Fintype ι]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : NovikovSeries Γ ι A) (g : NovikovSeries Γ ι B)
    (α : A →+ B →+ C) :
    extendExponents Γ (novikovSeriesMul f g α) =
      novikovSeriesMul (extendExponents Γ f) (extendExponents Γ g) α := by
  classical
  ext d
  by_cases hmem : ∀ i, (d i : ℝ) ∈ Γ
  · let dΓ : ι → Γ := fun i => ⟨(d i : ℝ), hmem i⟩
    have hd : includeExponent Γ dΓ = d := by
      funext i
      rfl
    rw [← hd, extendExponents_apply_include]
    let sourcePairs : Finset ((ι → Γ) × (ι → Γ)) :=
      (finite_pair_sum_eq (T1 := fnSupport f.val) (T2 := fnSupport g.val)
        f.prop g.prop dΓ).toFinset
    let targetPairs : Finset
        ((ι → (⊤ : AddSubgroup ℝ)) × (ι → (⊤ : AddSubgroup ℝ))) :=
      (finite_pair_sum_eq
        (T1 := fnSupport (extendExponents Γ f).val)
        (T2 := fnSupport (extendExponents Γ g).val)
        (extendExponents Γ f).prop (extendExponents Γ g).prop
        (includeExponent Γ dΓ)).toFinset
    let emb : ((ι → Γ) × (ι → Γ)) →
        ((ι → (⊤ : AddSubgroup ℝ)) × (ι → (⊤ : AddSubgroup ℝ))) :=
      fun p => (includeExponent Γ p.1, includeExponent Γ p.2)
    have hemb : Function.Injective emb := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      simp only [emb, Prod.mk.injEq] at h ⊢
      exact ⟨includeExponent_injective Γ h.1, includeExponent_injective Γ h.2⟩
    have hpairs : targetPairs = sourcePairs.image emb := by
      ext p
      simp only [targetPairs, sourcePairs, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq, Finset.mem_image]
      constructor
      · intro hp
        have hp1mem : ∀ i, (p.1 i : ℝ) ∈ Γ :=
          hasExponentSupport_extendExponents Γ f p.1 hp.2.1
        have hp2mem : ∀ i, (p.2 i : ℝ) ∈ Γ :=
          hasExponentSupport_extendExponents Γ g p.2 hp.2.2
        let p1Γ : ι → Γ := fun i => ⟨(p.1 i : ℝ), hp1mem i⟩
        let p2Γ : ι → Γ := fun i => ⟨(p.2 i : ℝ), hp2mem i⟩
        have hp1 : includeExponent Γ p1Γ = p.1 := by
          funext i
          rfl
        have hp2 : includeExponent Γ p2Γ = p.2 := by
          funext i
          rfl
        refine ⟨(p1Γ, p2Γ), ?_, ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · apply includeExponent_injective Γ
            rw [includeExponent_add, hp1, hp2]
            exact hp.1
          · have h := hp.2.1
            rw [← hp1, extendExponents_apply_include] at h
            exact h
          · have h := hp.2.2
            rw [← hp2, extendExponents_apply_include] at h
            exact h
        · exact Prod.ext hp1 hp2
      · rintro ⟨p, hp, rfl⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [← includeExponent_add, hp.1]
        · change (extendExponents Γ f).val (includeExponent Γ p.1) ≠ 0
          simpa using hp.2.1
        · change (extendExponents Γ g).val (includeExponent Γ p.2) ≠ 0
          simpa using hp.2.2
    change (∑ p ∈ sourcePairs, α (f p.1) (g p.2)) =
      ∑ p ∈ targetPairs,
        α ((extendExponents Γ f) p.1) ((extendExponents Γ g) p.2)
    rw [hpairs, Finset.sum_image hemb.injOn]
    apply Finset.sum_congr rfl
    intro p hp
    simp [emb]
  · rw [extendExponents_apply_of_not_mem Γ _ d hmem]
    symm
    apply not_ne_iff.mp
    intro hne
    have hdSupport : d ∈
        (novikovSeriesMul (extendExponents Γ f)
          (extendExponents Γ g) α).support := by
      rw [NovikovSeries.mem_support]
      exact hne
    have hdSum := support_mul_subset
      (extendExponents Γ f) (extendExponents Γ g) α hdSupport
    rw [Set.mem_add] at hdSum
    obtain ⟨d₁, hd₁, d₂, hd₂, hdadd⟩ := hdSum
    apply hmem
    intro i
    have hd₁ne : (extendExponents Γ f).val d₁ ≠ 0 := by
      simpa only [NovikovSeries.mem_support] using hd₁
    have hd₂ne : (extendExponents Γ g).val d₂ ≠ 0 := by
      simpa only [NovikovSeries.mem_support] using hd₂
    have hd₁mem : (d₁ i : ℝ) ∈ Γ :=
      hasExponentSupport_extendExponents Γ f d₁ hd₁ne i
    have hd₂mem : (d₂ i : ℝ) ∈ Γ :=
      hasExponentSupport_extendExponents Γ g d₂ hd₂ne i
    have hi : (d₁ i : ℝ) + (d₂ i : ℝ) = (d i : ℝ) := by
      exact congrArg (fun z : (⊤ : AddSubgroup ℝ) => (z : ℝ))
        (congrFun hdadd i)
    rw [← hi]
    exact add_mem hd₁mem hd₂mem

@[simp]
lemma extendExponents_novikovMonomial {ι M : Type*} [Fintype ι]
    [AddCommGroup M] (a : M) (d : ι → Γ) :
    extendExponents Γ (novikovMonomial a d) =
      novikovMonomial a (includeExponent Γ d) := by
  classical
  ext e
  by_cases hmem : ∀ i, (e i : ℝ) ∈ Γ
  · let eΓ : ι → Γ := fun i => ⟨(e i : ℝ), hmem i⟩
    have he : includeExponent Γ eΓ = e := by
      funext i
      rfl
    rw [← he, extendExponents_apply_include]
    change (if eΓ = d then a else 0) =
      if includeExponent Γ eΓ = includeExponent Γ d then a else 0
    by_cases h : eΓ = d
    · subst d
      simp
    · have h' : includeExponent Γ eΓ ≠ includeExponent Γ d :=
        fun hinc => h (includeExponent_injective Γ hinc)
      simp [h, h']
  · rw [extendExponents_apply_of_not_mem Γ _ e hmem]
    change 0 = if e = includeExponent Γ d then a else 0
    have hne : e ≠ includeExponent Γ d := by
      intro he
      apply hmem
      intro i
      rw [he]
      exact (d i).property
    simp [hne]

@[simp]
lemma extendExponents_one {ι A : Type*} [Fintype ι] [CommRing A] :
    extendExponents Γ (1 : NovikovSeries Γ ι A) = 1 := by
  change extendExponents Γ (novikovMonomial 1 0) = novikovMonomial 1 0
  rw [extendExponents_novikovMonomial, includeExponent_zero]

@[simp]
lemma extendExponents_mul {ι A : Type*} [Fintype ι] [CommRing A]
    (f g : NovikovSeries Γ ι A) :
    extendExponents Γ (f * g) = extendExponents Γ f * extendExponents Γ g :=
  extendExponents_novikovSeriesMul Γ f g AddMonoidHom.mul

/-- Extension by zero as a ring homomorphism. -/
noncomputable def extendExponentsRingHom {ι A : Type*} [Fintype ι] [CommRing A] :
    NovikovSeries Γ ι A →+* NovikovSeries (⊤ : AddSubgroup ℝ) ι A where
  toFun := extendExponents Γ
  map_zero' := extendExponents_zero Γ
  map_one' := extendExponents_one Γ
  map_add' := extendExponents_add Γ
  map_mul' := extendExponents_mul Γ

@[simp]
lemma extendExponentsRingHom_apply {ι A : Type*} [Fintype ι] [CommRing A]
    (f : NovikovSeries Γ ι A) :
    extendExponentsRingHom Γ f = extendExponents Γ f := rfl

lemma extendExponentsRingHom_injective {ι A : Type*} [Fintype ι] [CommRing A] :
    Function.Injective (extendExponentsRingHom Γ :
      NovikovSeries Γ ι A → NovikovSeries (⊤ : AddSubgroup ℝ) ι A) :=
  extendExponents_injective Γ

@[simp]
lemma extendExponents_algebraMapNovikov {ι A : Type*} [Fintype ι] [CommRing A]
    (a : A) :
    extendExponents Γ
        (algebraMapNovikov (Γ := Γ) (ι := ι) a) =
      algebraMapNovikov (Γ := (⊤ : AddSubgroup ℝ)) (ι := ι) a := by
  change extendExponents Γ (novikovMonomial a 0) = novikovMonomial a 0
  rw [extendExponents_novikovMonomial, includeExponent_zero]

@[simp]
lemma extendExponents_smul {ι A M : Type*} [Fintype ι] [CommRing A]
    [AddCommGroup M] [Module A M] (f : NovikovSeries Γ ι A)
    (m : NovikovSeries Γ ι M) :
    extendExponents Γ (f • m) =
      extendExponents Γ f • extendExponents Γ m :=
  extendExponents_novikovSeriesMul Γ f m smulAddHom

/-- Extension by zero on module-valued series as a semilinear map over exponent
extension on scalar series. -/
noncomputable def extendExponentsLinearMap {ι A M : Type*} [Fintype ι]
    [CommRing A] [AddCommGroup M] [Module A M] :
    NovikovSeries Γ ι M →ₛₗ[extendExponentsRingHom (A := A) (ι := ι) Γ]
      NovikovSeries (⊤ : AddSubgroup ℝ) ι M where
  toFun := extendExponents Γ
  map_add' := extendExponents_add Γ
  map_smul' := extendExponents_smul (A := A) Γ

@[simp]
lemma extendExponentsLinearMap_apply {ι A M : Type*} [Fintype ι]
    [CommRing A] [AddCommGroup M] [Module A M]
    (m : NovikovSeries Γ ι M) :
    extendExponentsLinearMap (A := A) Γ m = extendExponents Γ m := rfl

lemma extendExponentsLinearMap_injective {ι A M : Type*} [Fintype ι]
    [CommRing A] [AddCommGroup M] [Module A M] :
    Function.Injective (extendExponentsLinearMap (A := A) Γ :
      NovikovSeries Γ ι M → NovikovSeries (⊤ : AddSubgroup ℝ) ι M) :=
  extendExponents_injective Γ

end Novikov
