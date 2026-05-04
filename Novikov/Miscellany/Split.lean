import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Cardinality

namespace Novikov.Miscellany

variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]

/-- If `B` is an `A`-algebra with an `A`-linear splitting `σ`, and `B ⊗[A] M` is a finite
projective `B`-module, then `M` is a finite projective `A`-module.

**Proof of finiteness**: Induct on tensor product elements to extract a finite `Finset M`
whose `A`-span contains the image of `(σ ⊗ id) ∘ (A ⊗ M ≅ M)` applied to every element
of the form `b · x`.  Then apply to the finite set of `B`-generators of `B ⊗[A] M`.

**Proof of projectivity**: Use the lifting criterion.  Given a surjection `ε : P → Q`
and `φ : M → Q`, extend to `B` via `baseChange B`, lift through the `B`-projectivity
of `B ⊗[A] M`, and descend back to `A` using the retraction `(σ ⊗ id)` and the map
`m ↦ 1 ⊗ m`.  Naturality `ε ∘ (σ ⊗ id) = (σ ⊗ id) ∘ (id ⊗ ε)` gives the result. -/
lemma finite_projective_of_split_baseChange {B : Type*} [CommRing B] [Algebra A B]
    (σ : B →ₗ[A] A) (hσ : σ.comp (Algebra.linearMap A B) = LinearMap.id)
    [Module.Finite B (TensorProduct A B M)] [Module.Projective B (TensorProduct A B M)] :
    Module.Finite A M ∧ Module.Projective A M := by
  classical
  -- The retraction map q : B ⊗[A] M → M given by (σ ⊗ id) followed by the natural iso
  let q : TensorProduct A B M →ₗ[A] M :=
    (TensorProduct.lid A M).toLinearMap ∘ₗ
      (TensorProduct.map σ (LinearMap.id : M →ₗ[A] M))
  have hσ_one : σ (1 : B) = 1 := by
    simpa using congr_fun (congr_arg DFunLike.coe hσ) (1 : A)
  -- Lemma: for any tensor x, there's a finite S such that q(b·x) ∈ A-span(S) for all b
  have h_exists_span (x : TensorProduct A B M) :
      ∃ (S : Finset M), ∀ (b : B), q (b • x) ∈ Submodule.span A (S : Set M) := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · exact ⟨∅, fun _ => by simp [q]⟩
    · intro b0 m
      refine ⟨{m}, fun b => ?_⟩
      have hq : q (b • (b0 ⊗ₜ[A] m)) = σ (b * b0) • m := by
        simp [q, TensorProduct.smul_tmul']
      rw [hq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · intro x y ⟨Sx, hx⟩ ⟨Sy, hy⟩
      refine ⟨Sx ∪ Sy, fun b => ?_⟩
      have hq : q (b • (x + y)) = q (b • x) + q (b • y) := by simp [q, smul_add]
      rw [hq]
      apply Submodule.add_mem
      · exact Submodule.span_mono (by simp) (hx b)
      · exact Submodule.span_mono (by simp) (hy b)
  -- Get a finite B-linear presentation of B⊗M
  obtain ⟨n, π, hπ_surj⟩ := Module.Finite.exists_fin' B (TensorProduct A B M)
  let ei (i : Fin n) : Fin n → B := Pi.single i (1 : B)
  have h_each (i : Fin n) :
      ∃ (S : Finset M), ∀ (b : B), q (b • π (ei i)) ∈
        Submodule.span A (S : Set M) :=
    h_exists_span _
  choose S hS using h_each
  let S_total : Finset M := Finset.biUnion Finset.univ S
  have hS_total_sub (i : Fin n) : (S i : Set M) ⊆ (S_total : Set M) := fun m hm =>
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hm⟩
  have h_basis_eq (v : Fin n → B) : v = ∑ i, (v i) • ei i := by
    ext j; simp [ei, Pi.single_apply, Finset.sum_apply]
  have h_all (x : TensorProduct A B M) : q x ∈ Submodule.span A (S_total : Set M) := by
    obtain ⟨v, hv⟩ := hπ_surj x
    rw [← hv]
    have h_pi : π v = ∑ i, (v i) • π (ei i) :=
      calc
        π v = π (∑ i, (v i) • ei i) := congrArg π (h_basis_eq v)
        _ = ∑ i, π ((v i) • ei i) := map_sum _ _ _
        _ = ∑ i, (v i) • π (ei i) := by simp
    rw [h_pi, map_sum]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.span_mono (hS_total_sub i) (hS i (v i))
  refine ⟨?_, ?_⟩
  · -- Module.Finite A M
    refine ⟨S_total, ?_⟩
    rw [eq_top_iff]
    intro m _
    have hm : q ((1 : B) ⊗ₜ[A] m) = m := by simp [q, hσ_one]
    have hmem := h_all ((1 : B) ⊗ₜ[A] m)
    rw [hm] at hmem
    exact hmem
  · -- Module.Projective A M
    refine Module.Projective.of_lifting_property'' ?_
    intro ε' hε_surj
    let ε_B : (TensorProduct A B (M →₀ A)) →ₗ[B] (TensorProduct A B M) := ε'.baseChange B
    have hε_B_surj : Function.Surjective ε_B :=
      LinearMap.lTensor_surjective B hε_surj
    let φ_B : (TensorProduct A B M) →ₗ[B] (TensorProduct A B M) :=
      (LinearMap.id : M →ₗ[A] M).baseChange B
    obtain ⟨ψ_B, hψ_B⟩ :=
      Module.projective_lifting_property ε_B φ_B hε_B_surj
    -- maps for the retraction and inclusion
    let j : M →ₗ[A] (TensorProduct A B M) := TensorProduct.mk A B M (1 : B)
    let qP : (TensorProduct A B (M →₀ A)) →ₗ[A] (M →₀ A) :=
      (TensorProduct.lid A (M →₀ A)).toLinearMap ∘ₗ
        (TensorProduct.map σ (LinearMap.id : (M →₀ A) →ₗ[A] (M →₀ A)))
    let qM : (TensorProduct A B M) →ₗ[A] M := q
    -- naturality: ε' ∘ (σ⊗id) = (σ⊗id) ∘ (id⊗ε')
    have h_naturality : ε' ∘ₗ qP = qM ∘ₗ ε_B.restrictScalars A := by
      apply TensorProduct.ext'
      intro b f; simp [qP, qM, ε_B, ε'.baseChange_tmul, q]
    have h_final : ε' ∘ₗ (qP ∘ₗ ψ_B.restrictScalars A ∘ₗ j) = LinearMap.id := by
      calc
        ε' ∘ₗ (qP ∘ₗ ψ_B.restrictScalars A ∘ₗ j)
            = ((ε' ∘ₗ qP) ∘ₗ ψ_B.restrictScalars A) ∘ₗ j := by
          simp [LinearMap.comp_assoc]
        _ = ((qM ∘ₗ ε_B.restrictScalars A) ∘ₗ ψ_B.restrictScalars A) ∘ₗ j := by rw [h_naturality]
        _ = (qM ∘ₗ (ε_B ∘ₗ ψ_B).restrictScalars A) ∘ₗ j := by
          simp [LinearMap.comp_assoc]
        _ = (qM ∘ₗ φ_B.restrictScalars A) ∘ₗ j := by rw [hψ_B]
        _ = LinearMap.id := by
          ext m; simp [qM, φ_B, j, hσ_one, q]
    exact ⟨qP ∘ₗ ψ_B.restrictScalars A ∘ₗ j, h_final⟩

end Novikov.Miscellany
