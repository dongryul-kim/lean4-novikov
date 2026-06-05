import Novikov.Descent.Product.Trivialization

/-!
# Fiber-trivialization compatibility for product descent

This file isolates the expensive conversion from linear-map descent compatibility
to its pointwise form.  Downstream support estimates can reuse the resulting
opaque theorem without rechecking that conversion.
-/

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract

namespace Novikov.Descent

noncomputable section

universe u

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)] [∀ i, IsAlgClosed (K i)]

attribute [local irreducible]
  fiberTrivializationLinearEquiv
  LinearMap.baseChange
  LinearMap.comp

/-- Pointwise form of compatibility between the fiber trivialization and the
fiber descent isomorphisms. -/
lemma fiberTrivializationLinearEquiv_commute_φ_apply
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i))
    (i : I) (x : π₁s (realC (K i)) (fiberDescentDatum K M i).M) :
    (fiberConstDescentDatum K M i).φ
      ((letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ :=
        (realC (K i)).π₁.toAlgebra;
        LinearMap.baseChange (realC (K i)).R₂
          (fiberTrivializationLinearEquiv K M i).toLinearMap) x) =
    (letI : Algebra (realC (K i)).R₁ (realC (K i)).R₂ :=
      (realC (K i)).π₂.toAlgebra;
      LinearMap.baseChange (realC (K i)).R₂
        (fiberTrivializationLinearEquiv K M i).toLinearMap)
      ((fiberDescentDatum K M i).φ x) := by
  have h := LinearMap.congr_fun (fiberTrivializationLinearEquiv_commute_φ K M i) x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using h

end

end Novikov.Descent
