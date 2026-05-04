
import Novikov.Series.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Exact

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
  intro hgd
  apply hd
  change f (g d) = 0
  rw [hgd, map_zero]

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

lemma map_exact_forward (f : A →+ B) (g : B →+ C) (h : f.range = g.ker) :
    (map (Γ := Γ) (ι := ι) f).range ≤ (map (Γ := Γ) (ι := ι) g).ker := by
  rintro s ⟨t, rfl⟩
  ext d
  simp only [map_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
  have h_comp : g.comp f = 0 := by
    ext x
    have : f x ∈ f.range := ⟨x, rfl⟩
    rw [h] at this
    exact this
  rw [← AddMonoidHom.comp_apply, h_comp]
  rfl

lemma map_exact_backward (f : A →+ B) (g : B →+ C) (h : f.range = g.ker) :
    (map (Γ := Γ) (ι := ι) g).ker ≤ (map (Γ := Γ) (ι := ι) f).range := by
  intro s hs
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

/-- The functor `NovikovSeries` preserves exactness. -/
theorem map_exact (f : A →+ B) (g : B →+ C) (h : f.range = g.ker) :
    (map (Γ := Γ) (ι := ι) f).range = (map (Γ := Γ) (ι := ι) g).ker :=
  le_antisymm (map_exact_forward f g h) (map_exact_backward f g h)

section Linear

variable {R M N P : Type*} [Semiring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

/-- `R`-linear induced map on Novikov series from an `R`-linear map. -/
def lmap (f : M →ₗ[R] N) : NovikovSeries Γ ι M →ₗ[R] NovikovSeries Γ ι N where
  toFun s := ⟨f ∘ s.val, s.prop.comp (f := f.toAddMonoidHom)⟩
  map_add' s t := by
    ext d
    simp
  map_smul' r s := by
    ext d
    change f (r • s.val d) = r • f (s.val d)
    rw [map_smul]

@[simp]
lemma lmap_apply (f : M →ₗ[R] N) (s : NovikovSeries Γ ι M) (d : ι → Γ) :
    (lmap (Γ := Γ) (ι := ι) f s).val d = f (s.val d) :=
  rfl

@[simp]
lemma lmap_toAddMonoidHom (f : M →ₗ[R] N) :
    (lmap (Γ := Γ) (ι := ι) f).toAddMonoidHom = map f.toAddMonoidHom := by
  ext s d
  rfl

theorem lmap_id : lmap (Γ := Γ) (ι := ι) (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  ext s d
  rfl

theorem lmap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    lmap (Γ := Γ) (ι := ι) (g.comp f) = (lmap g).comp (lmap f) := by
  ext s d
  rfl

theorem lmap_injective (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (lmap (Γ := Γ) (ι := ι) f) :=
  map_injective f.toAddMonoidHom hf

theorem lmap_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (lmap (Γ := Γ) (ι := ι) f) :=
  map_surjective f.toAddMonoidHom hf

/-- `lmap` preserves exactness. -/
theorem lmap_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g) :
    Function.Exact (lmap (Γ := Γ) (ι := ι) f) (lmap (Γ := Γ) (ι := ι) g) := by
  have hker : f.toAddMonoidHom.range = g.toAddMonoidHom.ker := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.mem_ker]
      have : g (f x) = 0 := h.apply_apply_eq_zero x
      exact this
    · intro hy
      simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.mem_ker] at hy
      have : ∃ x, f x = y := (h y).mp hy
      obtain ⟨x, hx⟩ := this
      exact ⟨x, hx⟩
  have hrange := map_exact (Γ := Γ) (ι := ι) f.toAddMonoidHom g.toAddMonoidHom hker
  intro s
  constructor
  · intro hs
    have hs' : (map g.toAddMonoidHom) s = 0 := by
      ext d
      have : (lmap (Γ := Γ) (ι := ι) g s).val d = 0 := by rw [hs]; rfl
      simpa using this
    have : s ∈ (map (Γ := Γ) (ι := ι) f.toAddMonoidHom).range := by
      rw [hrange]
      exact (AddMonoidHom.mem_ker).mpr hs'
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by ext d; have := congrArg (·.val d) ht; simpa using this⟩
  · rintro ⟨t, rfl⟩
    ext d
    simp only [lmap_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact h.apply_apply_eq_zero (t.val d)

end Linear

end Novikov
