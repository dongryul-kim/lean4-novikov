import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Pi

namespace Novikov.Miscellany

open scoped Topology
open TopologicalSpace
open TensorProduct

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

lemma canonicalTopology_pi_eq (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ) :
    canonicalTopology A (Fin n → A) = Pi.topologicalSpace := by
  apply le_antisymm
  · unfold Pi.topologicalSpace
    apply le_iInf; intro i
    exact iInf_le (fun L : (Fin n → A) →ₗ[A] A => TopologicalSpace.induced L ‹_›) (LinearMap.proj i)
  · letI : TopologicalSpace (Fin n → A) := Pi.topologicalSpace
    apply le_iInf; intro L
    rw [← continuous_iff_le_induced]
    have hL : (L : (Fin n → A) → A) = fun x => ∑ i, L (Pi.basisFun A (Fin n) i) * x i := by
      ext x
      have hx : ∑ i, ((Pi.basisFun A (Fin n)).repr x) i • Pi.basisFun A (Fin n) i = x :=
        (Pi.basisFun A (Fin n)).sum_repr x
      have h_repr : ∀ i, ((Pi.basisFun A (Fin n)).repr x) i = x i := fun _ => rfl
      simp_rw [h_repr] at hx
      calc
        L x = L (∑ i, x i • Pi.basisFun A (Fin n) i) := congrArg L hx.symm
        _ = ∑ i, L (x i • Pi.basisFun A (Fin n) i) := map_sum _ _ _
        _ = ∑ i, x i * L (Pi.basisFun A (Fin n) i) := by simp_rw [LinearMap.map_smul, smul_eq_mul]
        _ = ∑ i, L (Pi.basisFun A (Fin n) i) * x i := by simp_rw [mul_comm]
    rw [hL]
    refine continuous_finset_sum (s := Finset.univ) ?_
    intro i hi
    exact Continuous.mul continuous_const (continuous_apply i)

/-- The canonical topology is compatible with `R`-linear isomorphisms: if `φ : F ≃ₗ[R] G`,
then the canonical topology on `F` equals the topology induced by `φ` from the canonical
topology on `G`. -/
lemma canonicalTopology_linearEquiv {R F G : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
    (φ : F ≃ₗ[R] G) :
    canonicalTopology R F =
      TopologicalSpace.induced (φ : F → G) (canonicalTopology R G) := by
  dsimp [canonicalTopology]
  rw [induced_iInf]
  simp_rw [induced_compose]
  let e : (G →ₗ[R] R) → (F →ₗ[R] R) := fun g => g.comp φ.toLinearMap
  have he_equiv : Function.Bijective e := by
    constructor
    · intro g1 g2 h
      apply LinearMap.ext; intro x
      have hx := congrArg (fun (f : F →ₗ[R] R) => f (φ.symm x)) h
      simpa [e, φ.apply_symm_apply] using hx
    · intro f
      refine ⟨f.comp φ.symm.toLinearMap, ?_⟩
      ext x; simp [e]
  have h_eq := (Equiv.ofBijective e he_equiv).iInf_congr
    (f := fun (g : G →ₗ[R] R) => TopologicalSpace.induced (g.comp φ.toLinearMap : F → R) inferInstance)
    (g := fun (f' : F →ₗ[R] R) => TopologicalSpace.induced (f' : F → R) inferInstance)
    (h := fun _ => rfl)
  simpa [e] using h_eq.symm

lemma isClosedEmbedding_baseChange {S R : Type*} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Algebra S R]
    (h_closed : Topology.IsClosedEmbedding (algebraMap S R))
    (M : Type*) [AddCommGroup M] [Module S M] [Module.Finite S M] [Module.Projective S M] :
    @Topology.IsClosedEmbedding M (TensorProduct S R M) (canonicalTopology S M) (canonicalTopology R (TensorProduct S R M)) (TensorProduct.mk S R M (1 : R)) := by
  have ⟨n, π, σ, _, _, h_split⟩ := Module.Finite.exists_comp_eq_id_of_projective S M
  letI tM : TopologicalSpace M := canonicalTopology S M
  letI tM_R : TopologicalSpace (TensorProduct S R M) := canonicalTopology R (TensorProduct S R M)
  letI tFn_S : TopologicalSpace (Fin n → S) := canonicalTopology S (Fin n → S)
  letI tFn_R : TopologicalSpace (Fin n → R) := canonicalTopology R (Fin n → R)
  letI tFn_S_R : TopologicalSpace (TensorProduct S R (Fin n → S)) := canonicalTopology R (TensorProduct S R (Fin n → S))
  haveI : @ContinuousAdd M tM _ := canonicalTopology.continuousAdd S M
  haveI : @ContinuousAdd (TensorProduct S R M) tM_R _ := canonicalTopology.continuousAdd R (TensorProduct S R M)
  haveI : @ContinuousAdd (Fin n → S) tFn_S _ := canonicalTopology.continuousAdd S (Fin n → S)
  haveI : @ContinuousAdd (Fin n → R) tFn_R _ := canonicalTopology.continuousAdd R (Fin n → R)
  haveI : @ContinuousAdd (TensorProduct S R (Fin n → S)) tFn_S_R _ := canonicalTopology.continuousAdd R (TensorProduct S R (Fin n → S))
  let f : M →ₗ[S] TensorProduct S R M := TensorProduct.mk S R M (1 : R)
  let f_free : (Fin n → S) →ₗ[S] TensorProduct S R (Fin n → S) := TensorProduct.mk S R (Fin n → S) (1 : R)
  let g : (Fin n → S) → (Fin n → R) := fun v i => algebraMap S R (v i)
  have h_canon_S : tFn_S = Pi.topologicalSpace := canonicalTopology_pi_eq S n
  have h_canon_R : tFn_R = Pi.topologicalSpace := canonicalTopology_pi_eq R n
  have h_g_closed : @Topology.IsClosedEmbedding _ _ tFn_S tFn_R g := by
    rw [h_canon_S, h_canon_R]
    have h_piMap : g = Pi.map (fun (_ : Fin n) => (algebraMap S R : S → R)) := by ext v i; rfl
    rw [h_piMap]
    exact Topology.IsClosedEmbedding.piMap (fun _ => h_closed)
  let F_equiv : TensorProduct S R (Fin n → S) ≃ₗ[R] (Fin n → R) :=
    (Algebra.TensorProduct.piScalarRight S R R (Fin n)).toLinearEquiv
  let hF_equiv : Homeomorph (TensorProduct S R (Fin n → S)) (Fin n → R) := {
    toEquiv := F_equiv.toEquiv,
    continuous_toFun := @canonicalTopology.continuous_linearMap R (TensorProduct S R (Fin n → S)) (Fin n → R) _ _ _ _ _ _ _ F_equiv,
    continuous_invFun := @canonicalTopology.continuous_linearMap R (Fin n → R) (TensorProduct S R (Fin n → S)) _ _ _ _ _ _ _ F_equiv.symm
  }
  have h_f_free_closed : @Topology.IsClosedEmbedding _ _ tFn_S tFn_S_R f_free := by
    have h_eq : f_free = (F_equiv.symm : (Fin n → R) →ₗ[R] TensorProduct S R (Fin n → S)) ∘ g := by
      ext v
      apply F_equiv.injective
      calc
        F_equiv (f_free v) = F_equiv (1 ⊗ₜ[S] v) := rfl
        _ = g v := by
          ext i
          simp [F_equiv, Algebra.TensorProduct.piScalarRight_tmul_apply, g, Algebra.smul_def]
        _ = F_equiv (F_equiv.symm (g v)) := by simp
    rw [h_eq]
    exact hF_equiv.symm.isClosedEmbedding.comp h_g_closed
  let σR : TensorProduct S R M →ₗ[R] TensorProduct S R (Fin n → S) := σ.baseChange R
  let πR : TensorProduct S R (Fin n → S) →ₗ[R] TensorProduct S R M := π.baseChange R
  have h_comm : (σR.restrictScalars S).comp f = f_free.comp σ := by
    apply LinearMap.ext; intro x
    change σR (1 ⊗ₜ x) = 1 ⊗ₜ (σ x)
    rw [LinearMap.baseChange_tmul]
  have ht_R_inv : πR.comp σR = LinearMap.id := by
    apply LinearMap.ext; intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro r m
      change πR (σR (r ⊗ₜ m)) = r ⊗ₜ m
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
      rw [← LinearMap.comp_apply, h_split, LinearMap.id_apply]
    · intro y z hy hz
      rw [map_add, hy, hz, map_add, LinearMap.id_apply, LinearMap.id_apply]
  have h_tM_emb : @Topology.IsEmbedding M (Fin n → S) tM tFn_S σ := by
    have h_cont_t : @Continuous M (Fin n → S) tM tFn_S σ :=
      @canonicalTopology.continuous_linearMap S M (Fin n → S) _ _ _ _ _ _ _ σ
    have h_cont_p : @Continuous (Fin n → S) M tFn_S tM π :=
      @canonicalTopology.continuous_linearMap S (Fin n → S) M _ _ _ _ _ _ _ π
    have h_leftInv : Function.LeftInverse (π : (Fin n → S) → M) (σ : M → Fin n → S) := by
      intro x; simpa using LinearMap.congr_fun h_split x
    exact h_leftInv.isEmbedding h_cont_p h_cont_t
  have h_tR_inducing : Topology.IsInducing σR := by
    -- t_R has a continuous left inverse p_R, so it's an embedding, hence inducing
    have h_cont : @Continuous (TensorProduct S R M) (TensorProduct S R (Fin n → S)) tM_R tFn_S_R σR :=
      @canonicalTopology.continuous_linearMap R (TensorProduct S R M) (TensorProduct S R (Fin n → S)) _ _ _ _ _ _ _ σR
    have h_cont_p : @Continuous (TensorProduct S R (Fin n → S)) (TensorProduct S R M) tFn_S_R tM_R πR :=
      @canonicalTopology.continuous_linearMap R (TensorProduct S R (Fin n → S)) (TensorProduct S R M) _ _ _ _ _ _ _ πR
    have h_leftInv : Function.LeftInverse (πR : TensorProduct S R (Fin n → S) → TensorProduct S R M)
        (σR : TensorProduct S R M → TensorProduct S R (Fin n → S)) := by
      intro x
      simpa using LinearMap.congr_fun ht_R_inv x
    exact (h_leftInv.isEmbedding h_cont_p h_cont).isInducing
  have h_eq_fun : σR ∘ f = f_free ∘ σ := by
    have := congrArg (fun (φ : M →ₗ[S] TensorProduct S R (Fin n → S)) => (φ : M → TensorProduct S R (Fin n → S))) h_comm
    simpa [LinearMap.coe_comp] using this
  have h_f_emb : @Topology.IsEmbedding M (TensorProduct S R M) tM tM_R f := by
    apply Topology.IsEmbedding.mk
    · -- IsInducing f: we need tM = induced f tM_R
      apply Topology.IsInducing.mk
      have h_ind_eq := (Topology.isInducing_iff (f_free ∘ σ)).mp
        (h_f_free_closed.isEmbedding.comp h_tM_emb).isInducing
      have h_tR_ind_eq := (Topology.isInducing_iff σR).mp h_tR_inducing
      calc
        tM = TopologicalSpace.induced (f_free ∘ σ) tFn_S_R := h_ind_eq
        _ = TopologicalSpace.induced (σR ∘ f) tFn_S_R := by rw [h_eq_fun]
        _ = TopologicalSpace.induced f (TopologicalSpace.induced σR tFn_S_R) := by rw [induced_compose]
        _ = TopologicalSpace.induced f tM_R := by rw [h_tR_ind_eq]
    · -- Injective f
      intro u v h
      have h1 : (σR ∘ f) u = (σR ∘ f) v := by simp [h]
      rw [h_eq_fun] at h1
      exact (h_f_free_closed.isEmbedding.comp h_tM_emb).injective h1
  have h_f_closedRange : IsClosed (Set.range f) := by
    have hS_closed : IsClosed (Set.range f_free : Set (TensorProduct S R (Fin n → S))) :=
      h_f_free_closed.isClosed_range
    have h_eq : Set.range f = σR ⁻¹' (Set.range f_free) := by
      ext x
      constructor
      · rintro ⟨m, hm⟩
        rw [← hm]
        refine ⟨σ m, ?_⟩
        calc
          σR (f m) = σR (1 ⊗ₜ[S] m) := rfl
          _ = 1 ⊗ₜ[S] (σ m) := by rw [LinearMap.baseChange_tmul]
          _ = f_free (σ m) := rfl
      · intro h
        rcases h with ⟨v, hv⟩
        use π v
        have hv' : σR x = 1 ⊗ₜ[S] v := by
          simpa [f_free] using hv.symm
        calc
          f (π v) = 1 ⊗ₜ[S] (π v) := rfl
          _ = πR (1 ⊗ₜ[S] v) := by rw [LinearMap.baseChange_tmul]
          _ = πR (σR x) := by rw [← hv']
          _ = x := by simpa using LinearMap.congr_fun ht_R_inv x
    rw [h_eq]
    exact IsClosed.preimage
      (@canonicalTopology.continuous_linearMap R (TensorProduct S R M) (TensorProduct S R (Fin n → S)) _ _ _ _ _ _ _ σR)
      hS_closed
  exact Topology.IsClosedEmbedding.mk h_f_emb h_f_closedRange

end Novikov.Miscellany
