
import Novikov.Series.Basic
import Novikov.Series.Algebra
import Novikov.Series.Finite
import Novikov.Series.Multiplication
import Mathlib.Algebra.Module.BigOperators

namespace Novikov

variable (Γ : AddSubmonoid ℝ)
variable {ι A : Type*} [Fintype ι] [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]

/-- Scalar multiplication as a bi-additive map. -/
def smulAddHom : A →+ M →+ M :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun m => a • m) (smul_add a)) 
    (fun x y => AddMonoidHom.ext fun z => add_smul x y z)

/-- Scalar multiplication of a Novikov series by a Novikov series on M. -/
noncomputable def novikovSeriesSMul (f : NovikovSeries Γ ι A) (m : NovikovSeries Γ ι M) :
    NovikovSeries Γ ι M :=
  novikovSeriesMul f m smulAddHom

noncomputable instance : SMul (NovikovSeries Γ ι A) (NovikovSeries Γ ι M) where
  smul := novikovSeriesSMul Γ

@[simp]
lemma novikovSMul_val (f : NovikovSeries Γ ι A) (m : NovikovSeries Γ ι M) (d : ι → Γ) :
    (f • m) d = novikovSeriesMulFun f m smulAddHom d := rfl

noncomputable instance moduleNovikovSeries : Module (NovikovSeries Γ ι A) (NovikovSeries Γ ι M) where
  smul_add f m1 m2 := by
    exact novikovSeriesMul_right_distrib f m1 m2 smulAddHom
  add_smul f1 f2 m := by
    exact novikovSeriesMul_left_distrib f1 f2 m smulAddHom
  mul_smul f1 f2 m := by
    exact novikovSeriesMul_assoc f1 f2 m AddMonoidHom.mul smulAddHom smulAddHom smulAddHom mul_smul
  one_smul m := by
    refine Subtype.ext (funext (fun d => ?_))
    simp only [show (1 : NovikovSeries Γ ι A) = novikovOne from rfl, novikovSMul_val, novikovSeriesMulFun, novikovOne_val, ne_eq, ite_eq_right_iff, Classical.not_imp]
    rw [Finset.sum_eq_single (0, d)]
    · simp only [↓reduceIte, smulAddHom, AddMonoidHom.mk'_apply, one_smul]
    · intro p hp hne
      have hsum : p.1 + p.2 = d := by
        have h' := hp
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h'
        simp_all only [not_false_eq_true, and_true, Set.Finite.mem_toFinset, Set.mem_setOf_eq, zero_add, and_self, ne_eq, add_eq_right]
      by_cases hp1 : p.1 = 0
      · have hp2 : p.2 = d := by
          funext i
          have h_i := congr_fun hsum i
          simp only [hp1, Pi.add_apply, Pi.zero_apply, zero_add] at h_i
          exact h_i
        have : p = (0, d) := Prod.ext hp1 hp2
        contradiction
      · simp only [hp1, ↓reduceIte, smulAddHom, AddMonoidHom.mk'_apply, zero_smul]
    · intro h
      by_cases hm : m d = 0
      · simp only [↓reduceIte, smulAddHom, AddMonoidHom.mk'_apply, hm, smul_zero]
      · exfalso
        apply h
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, zero_add, true_and, hm, not_false_eq_true, and_true]
        intro h1
        have h0 : m d = 0 := by
          rw [← one_smul A (m d), h1, zero_smul]
        exact hm h0
  zero_smul m := by
    exact novikovSeriesMul_zero_mul (A := A) m smulAddHom
  smul_zero f := by
    exact novikovSeriesMul_mul_zero (B := M) f smulAddHom

end Novikov
