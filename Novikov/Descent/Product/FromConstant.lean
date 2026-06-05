import Novikov.Descent.Product.ToConstant
import Novikov.Descent.Product.Dual

open CategoryTheory TensorProduct Novikov.Miscellany Novikov.Descent.Abstract
open scoped BigOperators

namespace Novikov.Descent

noncomputable section

universe u

variable {I : Type u} (K : I → Type u) [∀ i, Field (K i)] [∀ i, IsAlgClosed (K i)]

/-- The finite projective module that will source the duality-produced map back
to `M`: it is the ordinary dual of the product constant module attached to
`M.dual`. -/
noncomputable def fromConstantModule
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    FiniteProjectiveModule (∀ i, K i) :=
  FiniteProjectiveModule.dual (∀ i, K i) (productConstModule K M.dual)

/-- Source-module identification using the canonical fiber-dual comparison. -/
noncomputable def fromConstantModuleIsoProductConstModuleCompatible
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    fromConstantModule K M ≅ productConstModule K M :=
  (FiniteProjectiveModule.dualIso (∀ i, K i)
      (productConstModuleDualFiberIsoOf K M (fiberDescentDatumDualIso K M))).symm.trans
    (productConstModuleFiberDualsDualIsoProduct K M)

/-- The source-module identification after applying constant descent. -/
noncomputable def fromConstantSourceIsoProductConstModuleCompatible
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (fromConstantModule K M) ≅
      (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (productConstModule K M) :=
  (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).mapIso
    (fromConstantModuleIsoProductConstModuleCompatible K M)

/-- The forward comparison applied to the dual descent datum. -/
noncomputable def toDualConstant
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    M.dual ⟶ (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
      (productConstModule K M.dual) :=
  toConstant K M.dual

/-- Dualizing `toDualConstant` gives a map from a constant object to the double
dual of `M`.  The source is rewritten using `constantDescentDatum_dual`. -/
private noncomputable def fromDualConstantToDoubleDual
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (fromConstantModule K M) ⟶ M.dual.dual :=
  (productConstDescentDatumDualIso K M.dual).hom ≫ (toDualConstant K M).dual

/-- The duality-produced morphism from the constant object `fromConstantModule K M`
back to `M`. -/
noncomputable def fromConstantFromDual
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (fromConstantModule K M) ⟶ M :=
  fromDualConstantToDoubleDual K M ≫ (DescentDatum.doubleDualIso M).inv

/-- The underlying linear map of the duality-produced morphism back to `M`. -/
noncomputable def fromDualConstantLinearMap
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    (((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (fromConstantModule K M)).M) →ₗ[(realC (∀ i, K i)).R₁] M.M :=
  (fromConstantFromDual K M).toLinearMap

/-- The reverse comparison map with the intended constant source. -/
noncomputable def fromConstant
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)) :
    (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) (∀ i, K i)).obj
        (productConstModule K M) ⟶ M :=
  (fromConstantSourceIsoProductConstModuleCompatible K M).inv ≫ fromConstantFromDual K M

end

end Novikov.Descent
