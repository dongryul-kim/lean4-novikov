import Novikov.Series.Substitute

/-! # Coefficientwise product maps for Novikov series

For a family of commutative rings `K : I → Type*`, a Novikov series over the
product ring `∀ i, K i` can be evaluated coefficientwise at each component `i`,
yielding a Novikov series over `K i`.  Bundling these evaluations gives an
injective ring homomorphism

```
NovikovSeries Γ ι (∀ i, K i) →+* (∀ i, NovikovSeries Γ ι (K i)).
```

This map is *not* an isomorphism in general: a family of Novikov series over the
individual `K i` need not satisfy a uniform Novikov finiteness condition.  The
injection is the basic tool for descent over a product of fields, where
`A((t))` is embedded into `∏ K_i((t))`.
-/

namespace Novikov

universe u v

variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ]
variable {Γ : S} {ι : Type*} [Fintype ι]
variable {I : Type u} (K : I → Type v) [∀ i, CommRing (K i)]

/-- Coefficientwise evaluation: project a Novikov series over the product ring
`∀ j, K j` at component `i`, applying `Pi.evalRingHom` to every coefficient. -/
noncomputable def coeffwiseEvalRingHom (i : I) :
    NovikovSeries Γ ι (∀ j, K j) →+* NovikovSeries Γ ι (K i) :=
  mapRingHom (Γ := Γ) (ι := ι) (Pi.evalRingHom K i)

/-- Coefficientwise evaluation sends a constant series to the constant series of
its evaluated coefficient. -/
@[simp]
lemma coeffwiseEvalRingHom_algebraMapNovikov (i : I) (a : ∀ i, K i) :
    coeffwiseEvalRingHom (Γ := Γ) (ι := ι) K i
        (algebraMapNovikov (Γ := Γ) (ι := ι) a) =
      algebraMapNovikov (Γ := Γ) (ι := ι) (a i) := by
  ext d
  by_cases hd : d = 0
  · simp [coeffwiseEvalRingHom, mapRingHom_apply, algebraMapNovikov, hd]
  · simp [coeffwiseEvalRingHom, mapRingHom_apply, algebraMapNovikov, hd]

/-- The bundled product of the coefficientwise evaluation maps,
`NovikovSeries Γ ι (∀ i, K i) →+* (∀ i, NovikovSeries Γ ι (K i))`. -/
noncomputable def coeffwisePiRingHom :
    NovikovSeries Γ ι (∀ i, K i) →+* (∀ i, NovikovSeries Γ ι (K i)) :=
  Pi.ringHom fun i => coeffwiseEvalRingHom K i

/-- The coefficientwise product map is injective: a Novikov series over the
product ring is determined by its component projections. -/
lemma coeffwisePiRingHom_injective :
    Function.Injective (coeffwisePiRingHom (Γ := Γ) (ι := ι) K) := by
  intro f g h
  ext d i
  exact congrArg (fun z => (z i).val d) h

/-! ## Compatibility with substitution

The coefficientwise evaluation maps commute with substitution in the variable
set.  Since every cosimplicial face map of the Novikov cosimplicial ring is a
substitution `substituteRingHom φ`, this single lemma yields compatibility with
all face maps. -/

/-- A coefficientwise ring homomorphism commutes with substitution.  The two
sides differ only in the summation domain (`map g` may kill coefficients), but
the omitted terms map to zero, so the sums agree. -/
lemma mapRingHom_substitute {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B)
    (φ : ι → ι') (f : NovikovSeries Γ ι A) :
    mapRingHom g (substitute φ f) = substitute φ (mapRingHom g f) := by
  ext d
  rw [mapRingHom_apply]
  show g ((substitute φ f).val d) = (substitute φ (mapRingHom g f)).val d
  simp only [substitute, substituteFun]
  rw [map_sum]
  symm
  apply Finset.sum_subset
  · intro e he
    rw [mem_finite_substitution_support] at he ⊢
    refine ⟨he.1, ?_⟩
    intro hfe
    apply he.2
    rw [mapRingHom_apply, hfe, map_zero]
  · intro e he hne
    rw [mem_finite_substitution_support] at he
    rw [mem_finite_substitution_support, not_and] at hne
    have := hne he.1
    rw [not_not] at this
    exact this

/-- Coefficientwise evaluation commutes with substitution.  Specialized to the
cosimplicial face maps, this expresses that the projection
`A((t)) → K_i((t))` is a map of cosimplicial rings. -/
lemma coeffwiseEvalRingHom_substituteRingHom {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (i : I) (φ : ι → ι') (f : NovikovSeries Γ ι (∀ j, K j)) :
    coeffwiseEvalRingHom K i (substituteRingHom φ f) =
      substituteRingHom φ (coeffwiseEvalRingHom K i f) :=
  mapRingHom_substitute (Pi.evalRingHom K i) φ f

end Novikov
