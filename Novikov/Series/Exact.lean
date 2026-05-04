
import Novikov.Series.Basic

/-!
# Exactness of the Novikov series functor

We show that the functor $A \mapsto \text{NovikovSeries } \Gamma \ \iota \ A$ is exact.
-/

namespace Novikov

variable {ι A B C : Type*} [Fintype ι] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S}

/-- If `g` is a Novikov series, then its composition with a group homomorphism is also a
Novikov series. -/
lemma isNovikovSeries.comp {f : A →+ B} {g : (ι → Γ) → A} (hg : isNovikovSeries g) :
    isNovikovSeries (f ∘ g) := by
  intro s hs C
  refine Set.Finite.subset (hg s hs C) ?_
  rintro d ⟨hd, hlt⟩
  refine ⟨?_, hlt⟩
  contrapose! hd
  simp [hd]

/-- Induced map on Novikov series from a map of abelian groups. -/
def map (f : A →+ B) : NovikovSeries Γ ι A →+ NovikovSeries Γ ι B where
  toFun s := ⟨f ∘ s.val, s.prop.comp⟩
  map_zero' := by
    ext d
    simp
  map_add' s t := by
    ext d
    simp

@[simp]
lemma map_apply (f : A →+ B) (s : NovikovSeries Γ ι A) (d : ι → Γ) :
    (map f s).val d = f (s.val d) :=
  rfl

/-- `map` preserves the identity map. -/
theorem map_id : map (Γ := Γ) (ι := ι) (AddMonoidHom.id A) = AddMonoidHom.id (NovikovSeries Γ ι A) := by
  ext s d
  rfl

/-- `map` is functorial with respect to composition. -/
theorem map_comp (f : A →+ B) (g : B →+ C) :
    map (Γ := Γ) (ι := ι) (g.comp f) = (map g).comp (map f) := by
  ext s d
  rfl

/-- The map on Novikov series preserves injectivity. -/
theorem map_injective (f : A →+ B) (hf : Function.Injective f) :
    Function.Injective (map (Γ := Γ) (ι := ι) f) := by
  intro s t h
  ext d
  apply hf
  rw [← map_apply f s d, h, map_apply]

/-- The map on Novikov series preserves surjectivity. -/
theorem map_surjective (f : A →+ B) (hf : Function.Surjective f) :
    Function.Surjective (map (Γ := Γ) (ι := ι) f) := by
  intro s
  classical
  let g_val := fun d => if s.val d = 0 then 0 else Classical.choose (hf (s.val d))
  have hg : isNovikovSeries g_val := by
    intro t ht C
    refine Set.Finite.subset (s.prop t ht C) ?_
    rintro d ⟨hd, hlt⟩
    refine ⟨?_, hlt⟩
    intro h_s_zero
    apply hd
    simp [g_val, h_s_zero]
  use ⟨g_val, hg⟩
  ext d
  change f (g_val d) = s.val d
  simp only [g_val]
  split_ifs with h
  · rw [h, f.map_zero]
  · exact Classical.choose_spec (hf (s.val d))

/-- The functor `NovikovSeries` preserves exactness. -/
theorem map_exact (f : A →+ B) (g : B →+ C) (h : f.range = g.ker) :
    (map (Γ := Γ) (ι := ι) f).range = (map (Γ := Γ) (ι := ι) g).ker := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    ext d
    simp only [map_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    have h_comp : g.comp f = 0 := by
      ext x
      have : f x ∈ f.range := ⟨x, rfl⟩
      rw [h] at this
      exact this
    rw [← AddMonoidHom.comp_apply, h_comp]
    rfl
  · intro hs
    classical
    have : ∀ d, s.val d ∈ f.range := by
      intro d
      rw [h]
      change g (s.val d) = 0
      have h_val : ((map g) s).val d = 0 := by
        rw [(AddMonoidHom.mem_ker).mp hs]
        rfl
      exact h_val
    let t_val := fun d => if s.val d = 0 then 0 else Classical.choose (this d)
    have ht : isNovikovSeries t_val := by
      intro t_ ht_ C
      refine Set.Finite.subset (s.prop t_ ht_ C) ?_
      rintro d ⟨hd, hlt⟩
      refine ⟨?_, hlt⟩
      intro h_s_zero
      apply hd
      simp [t_val, h_s_zero]
    use ⟨t_val, ht⟩
    ext d
    change f (t_val d) = s.val d
    simp only [t_val]
    split_ifs with h_
    · rw [h_, f.map_zero]
    · exact Classical.choose_spec (this d)

end Novikov
