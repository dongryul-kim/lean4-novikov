import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order

namespace Novikov.Miscellany

open scoped Topology
open TopologicalSpace

variable (A M N : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- The canonical topology on an `A`-module `M` where `A` is a topological ring.
It is the coarsest topology making all `A`-linear maps `M → A` continuous. -/
@[reducible]
def canonicalTopology : TopologicalSpace M :=
  ⨅ (f : M →ₗ[A] A), TopologicalSpace.induced f ‹_›

lemma canonicalTopology_self_eq :
    canonicalTopology A A = ‹TopologicalSpace A› := by
  let tA : TopologicalSpace A := ‹_›
  apply le_antisymm
  · calc
      canonicalTopology A A = ⨅ (f : A →ₗ[A] A), tA.induced f := rfl
      _ ≤ tA.induced (LinearMap.id : A →ₗ[A] A) := iInf_le _ _
      _ = tA := induced_id
  · refine le_iInf ?_
    intro f
    have h_cont : Continuous[tA, tA] (f : A → A) := by
      have h_eq : (f : A → A) = fun x => f 1 * x := by
        ext x
        simpa [smul_eq_mul, mul_comm] using f.map_smul x (1 : A)
      rw [h_eq]
      exact continuous_const_mul (f 1)
    rw [continuous_iff_le_induced] at h_cont
    exact h_cont

lemma canonicalTopology.continuousAdd : @ContinuousAdd M (canonicalTopology A M) _ := by
  letI : TopologicalSpace M := canonicalTopology A M
  have h : Continuous[induced Prod.fst (canonicalTopology A M) ⊓
      induced Prod.snd (canonicalTopology A M), canonicalTopology A M]
      (fun p : M × M => p.1 + p.2) := by
    dsimp [canonicalTopology]
    rw [continuous_iInf_rng]
    intro f
    rw [continuous_induced_rng]
    have hf : Continuous[canonicalTopology A M, ‹TopologicalSpace A›] (f : M → A) := by
      rw [continuous_iff_le_induced]
      dsimp [canonicalTopology]
      exact iInf_le (fun g : M →ₗ[A] A => TopologicalSpace.induced g ‹_›) f
    have h_eq : (f ∘ (fun p : M × M => p.1 + p.2)) = (fun p : M × M => f p.1) + (fun p : M × M => f p.2) := by
      ext p; simp [map_add]
    rw [h_eq]
    have h_fst : Continuous[induced Prod.fst (canonicalTopology A M) ⊓
        induced Prod.snd (canonicalTopology A M), ‹TopologicalSpace A›] (fun p : M × M => f p.1) :=
      hf.comp (continuous_le_dom inf_le_left continuous_induced_dom)
    have h_snd : Continuous[induced Prod.fst (canonicalTopology A M) ⊓
        induced Prod.snd (canonicalTopology A M), ‹TopologicalSpace A›] (fun p : M × M => f p.2) :=
      hf.comp (continuous_le_dom inf_le_right continuous_induced_dom)
    exact h_fst.add h_snd
  refine @ContinuousAdd.mk M (canonicalTopology A M) _ ?_
  simpa using h

lemma canonicalTopology.continuousSMul : @ContinuousSMul A M _ ‹TopologicalSpace A› (canonicalTopology A M) := by
  letI : TopologicalSpace M := canonicalTopology A M
  have h : Continuous[‹TopologicalSpace A›.induced Prod.fst ⊓
      (canonicalTopology A M).induced Prod.snd, canonicalTopology A M]
      (fun p : A × M => p.1 • p.2) := by
    dsimp [canonicalTopology]
    rw [continuous_iInf_rng]
    intro f
    rw [continuous_induced_rng]
    have h_eq : (f ∘ (fun (p : A × M) => p.1 • p.2)) = (fun (p : A × M) => p.1 * f p.2) := by
      ext ⟨a, x⟩; simp [f.map_smul, smul_eq_mul]
    rw [h_eq]
    have h_mul : Continuous[‹TopologicalSpace A›.induced Prod.fst ⊓
        ‹TopologicalSpace A›.induced Prod.snd, ‹TopologicalSpace A›]
        (fun (p : A × A) => p.1 * p.2) := by
      simpa using continuous_mul (M := A)
    have hf : Continuous[canonicalTopology A M, ‹TopologicalSpace A›] (f : M → A) := by
      rw [continuous_iff_le_induced]
      dsimp [canonicalTopology]
      exact iInf_le (fun g : M →ₗ[A] A => TopologicalSpace.induced g ‹_›) f
    have h_prod : Continuous[‹TopologicalSpace A›.induced Prod.fst ⊓
        (canonicalTopology A M).induced Prod.snd,
        ‹TopologicalSpace A›.induced Prod.fst ⊓ ‹TopologicalSpace A›.induced Prod.snd]
        (fun (p : A × M) => (p.1, f p.2) : A × M → A × A) :=
      (continuous_le_dom inf_le_left continuous_induced_dom).prodMk
        (hf.comp (continuous_le_dom inf_le_right continuous_induced_dom))
    have h_eq2 : (fun (p : A × M) => p.1 * f p.2) = (fun (p : A × A) => p.1 * p.2) ∘
        (fun (p : A × M) => (p.1, f p.2)) := by
      ext ⟨a, x⟩; simp
    rw [h_eq2]
    exact h_mul.comp h_prod
  refine @ContinuousSMul.mk A M _ ‹TopologicalSpace A› (canonicalTopology A M) ?_
  simpa using h

lemma canonicalTopology.continuous_linearMap (φ : M →ₗ[A] N) :
    @Continuous M N (canonicalTopology A M) (canonicalTopology A N) φ := by
  unfold canonicalTopology
  rw [continuous_iInf_rng]
  intro f
  rw [continuous_induced_rng]
  have h : (⨅ (g : M →ₗ[A] A), TopologicalSpace.induced g ‹_›) ≤
      TopologicalSpace.induced (f.comp φ) ‹_› :=
    iInf_le (fun g : M →ₗ[A] A => TopologicalSpace.induced g ‹_›) (f.comp φ)
  rw [← continuous_iff_le_induced] at h
  simpa using h

lemma canonicalTopology_prod_eq :
    canonicalTopology A (M × N) =
    @TopologicalSpace.induced (M × N) M Prod.fst (canonicalTopology A M) ⊓
    @TopologicalSpace.induced (M × N) N Prod.snd (canonicalTopology A N) := by
  let tA : TopologicalSpace A := ‹_›
  let tProd := (canonicalTopology A M).induced Prod.fst ⊓ (canonicalTopology A N).induced Prod.snd
  have h_functions : ∀ f : (M × N) →ₗ[A] A, tProd ≤ tA.induced f := by
    intro f
    let f₁ : M →ₗ[A] A := f.comp (LinearMap.inl A M N)
    let f₂ : N →ₗ[A] A := f.comp (LinearMap.inr A M N)
    have h_decomp : (f : M × N → A) = (fun (x : M × N) => f₁ x.1) + (fun (x : M × N) => f₂ x.2) := by
      ext ⟨m, n⟩
      calc
        f (m, n) = f ((m, 0) + (0, n)) := by simp
        _ = f (m, 0) + f (0, n) := by rw [f.map_add]
        _ = f₁ m + f₂ n := by simp [f₁, f₂]
        _ = ((fun (x : M × N) => f₁ x.1) + (fun (x : M × N) => f₂ x.2)) (m, n) := rfl
    letI : TopologicalSpace M := canonicalTopology A M
    letI : TopologicalSpace N := canonicalTopology A N
    letI : TopologicalSpace (M × N) := tProd
    have h₁_cont : Continuous (f₁ : M → A) := by
      rw [continuous_iff_le_induced]
      simpa [canonicalTopology] using iInf_le (fun g : M →ₗ[A] A => tA.induced g) f₁
    have h₂_cont : Continuous (f₂ : N → A) := by
      rw [continuous_iff_le_induced]
      simpa [canonicalTopology] using iInf_le (fun g : N →ₗ[A] A => tA.induced g) f₂
    have h₁ : Continuous (fun (x : M × N) => f₁ x.1) :=
      h₁_cont.comp continuous_fst
    have h₂ : Continuous (fun (x : M × N) => f₂ x.2) :=
      h₂_cont.comp continuous_snd
    rw [h_decomp]
    have h_add_cont : Continuous ((fun (x : M × N) => f₁ x.1) + (fun (x : M × N) => f₂ x.2)) :=
      h₁.add h₂
    rw [continuous_iff_le_induced] at h_add_cont
    simpa using h_add_cont
  have h_prod_le_canon : tProd ≤ canonicalTopology A (M × N) := by
    unfold canonicalTopology
    exact le_iInf h_functions
  have h_canon_le_prod : canonicalTopology A (M × N) ≤ tProd := by
    apply le_inf
    · -- canonical ≤ (canonical M).induced fst
      have h_subs : ∀ g : M →ₗ[A] A, canonicalTopology A (M × N) ≤
          (tA.induced (g : M → A)).induced Prod.fst := by
        intro g
        have h_ind : tA.induced (g.comp (LinearMap.fst A M N)) =
            (tA.induced (g : M → A)).induced Prod.fst := by
          calc
            tA.induced (g.comp (LinearMap.fst A M N)) = tA.induced ((g : M → A) ∘ Prod.fst) := rfl
            _ = (tA.induced (g : M → A)).induced Prod.fst := by rw [induced_compose]
        calc
          canonicalTopology A (M × N) ≤ tA.induced (g.comp (LinearMap.fst A M N)) := by
            unfold canonicalTopology
            exact iInf_le (fun f : (M × N) →ₗ[A] A => tA.induced f)
              (g.comp (LinearMap.fst A M N))
          _ = (tA.induced (g : M → A)).induced Prod.fst := h_ind
      rw [canonicalTopology, show (canonicalTopology A M).induced Prod.fst =
          (⨅ (g : M →ₗ[A] A), tA.induced g).induced Prod.fst from rfl, induced_iInf]
      exact le_iInf h_subs
    · -- canonical ≤ (canonical N).induced snd
      have h_subs : ∀ g : N →ₗ[A] A, canonicalTopology A (M × N) ≤
          (tA.induced (g : N → A)).induced Prod.snd := by
        intro g
        have h_ind : tA.induced (g.comp (LinearMap.snd A M N)) =
            (tA.induced (g : N → A)).induced Prod.snd := by
          calc
            tA.induced (g.comp (LinearMap.snd A M N)) = tA.induced ((g : N → A) ∘ Prod.snd) := rfl
            _ = (tA.induced (g : N → A)).induced Prod.snd := by rw [induced_compose]
        calc
          canonicalTopology A (M × N) ≤ tA.induced (g.comp (LinearMap.snd A M N)) := by
            unfold canonicalTopology
            exact iInf_le (fun f : (M × N) →ₗ[A] A => tA.induced f)
              (g.comp (LinearMap.snd A M N))
          _ = (tA.induced (g : N → A)).induced Prod.snd := h_ind
      rw [canonicalTopology, show (canonicalTopology A N).induced Prod.snd =
          (⨅ (g : N →ₗ[A] A), tA.induced g).induced Prod.snd from rfl, induced_iInf]
      exact le_iInf h_subs
  exact le_antisymm h_canon_le_prod h_prod_le_canon

end Novikov.Miscellany
