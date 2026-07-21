import Novikov.Series.Ring
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps

namespace Novikov

variable {ι A B : Type*} [Fintype ι] [CommRing A] [CommRing B]
variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S}

/-- A surjective coefficient ring map induces a surjective map on Novikov
series rings. -/
theorem mapRingHom_surjective (q : A →+* B) (hq : Function.Surjective q) :
    Function.Surjective (mapRingHom (Γ := Γ) (ι := ι) q) :=
  map_surjective q.toAddMonoidHom hq

/-- A coefficient ring map with square-zero kernel induces a Novikov series
ring map with square-zero kernel. -/
theorem mapRingHom_ker_sq (q : A →+* B)
    (hq_sq : RingHom.ker q ^ 2 = ⊥) :
    RingHom.ker (mapRingHom (Γ := Γ) (ι := ι) q) ^ 2 = ⊥ := by
  apply bot_unique
  rw [pow_two, Ideal.mul_le]
  intro x hx y hy
  change x * y = 0
  ext d
  rw [novikovMul_val]
  unfold novikovMulFun
  apply Finset.sum_eq_zero
  intro p _
  have hx_coeff : x p.1 ∈ RingHom.ker q := by
    change q (x p.1) = 0
    have h := congrArg (fun z : NovikovSeries Γ ι B => z p.1) hx
    simpa only [mapRingHom_apply, ZeroMemClass.coe_zero, Pi.zero_apply] using h
  have hy_coeff : y p.2 ∈ RingHom.ker q := by
    change q (y p.2) = 0
    have h := congrArg (fun z : NovikovSeries Γ ι B => z p.2) hy
    simpa only [mapRingHom_apply, ZeroMemClass.coe_zero, Pi.zero_apply] using h
  have hK : RingHom.ker q * RingHom.ker q = ⊥ := by
    simpa only [pow_two] using hq_sq
  have hprod : x p.1 * y p.2 ∈ RingHom.ker q * RingHom.ker q :=
    Ideal.mul_mem_mul hx_coeff hy_coeff
  rw [hK] at hprod
  simpa using hprod

end Novikov
