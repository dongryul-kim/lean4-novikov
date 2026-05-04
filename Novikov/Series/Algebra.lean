import Novikov.Series.Basic
import Novikov.Series.Finite
import Novikov.Series.Ring

namespace Novikov

variable {ι A : Type*} [Fintype ι] [CommRing A]
variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ] {Γ : S}

/-- The canonical ring homomorphism `A → NovikovSeriesMultivar Γ ι A` sending `a`
to the series with `a` at the zero exponent and `0` elsewhere. -/
noncomputable def algebraMapNovikov :
    A →+* NovikovSeries Γ ι A where
  toFun a := ⟨fun d => if d = (0 : ι → Γ) then a else 0, isNovikov_monomial a 0⟩
  map_one' := by
    rfl
  map_mul' := by
    intros x y
    ext d
    rw [novikovMul_val]
    unfold novikovMulFun
    dsimp
    by_cases hd : d = 0
    · subst hd
      simp only [ite_true]
      rw [Finset.sum_eq_single ((0 : ι → Γ), (0 : ι → Γ))]
      · simp
      · intro b hb hne
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hb
        simp only [Prod.ext_iff, ne_eq] at hne
        simp_all only [ite_eq_right_iff, Classical.not_imp, and_self, not_true_eq_false]
      · intro h
        simp_all only [ite_eq_right_iff, Classical.not_imp, Set.Finite.mem_toFinset, Set.mem_setOf_eq, add_zero,
          true_and, not_and, not_not, ↓reduceIte]
        by_cases hx : x = 0
        · subst hx
          simp_all only [not_true_eq_false, IsEmpty.forall_iff, zero_mul]
        · simp_all only [not_false_eq_true, forall_const, mul_zero]
    · simp only [hd, ite_false]
      rw [Finset.sum_eq_zero]
      intro p hp
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
      by_cases hp : p.1 = 0
      · simp_all only [zero_add, ↓reduceIte, ite_eq_right_iff, Classical.not_imp, mul_zero]
      · simp_all only [↓reduceIte, not_true_eq_false, ite_eq_right_iff, Classical.not_imp, false_and, and_false]
  map_zero' := by
    ext d
    dsimp
    split_ifs <;> rfl
  map_add' := by
    intros x y
    ext d
    dsimp
    split_ifs <;> simp

/-- Novikov series form an `A`-algebra. -/
noncomputable instance novikovAlgebra :
    Algebra A (NovikovSeries Γ ι A) where
  smul r f := ⟨r • f.val, isNovikovSeries_smul r f.prop⟩
  smul_def' r f := by
    ext d
    have h_lhs : (r • f).val d = r * f.val d := rfl
    rw [h_lhs]
    rw [novikovMul_val]
    unfold novikovMulFun
    rw [Finset.sum_eq_single ((0 : ι → Γ), d)]
    · dsimp [algebraMapNovikov]
      simp
    · rintro ⟨b1, b2⟩ hb hne
      rw [mem_finite_convolution_support] at hb
      rcases hb with ⟨hsum, hb1, hb2⟩
      dsimp [algebraMapNovikov] at hb1
      split_ifs at hb1 with h0
      · subst h0
        simp only [zero_add] at hsum
        subst hsum
        exact (hne rfl).elim
      · contradiction
    · intro h
      rw [mem_finite_convolution_support] at h
      dsimp [algebraMapNovikov] at h
      simp only [zero_add, ↓reduceIte, true_and, not_and, not_not] at h
      by_cases hr : r = 0
      · subst hr; simp
      · by_cases hfd : f.val d = 0
        · rw [hfd]; simp
        · exfalso; simp_all only [not_false_eq_true, mul_zero, imp_false, not_true_eq_false]
  commutes' r f := novikovMul_mul_comm _ _
  algebraMap := algebraMapNovikov

end Novikov

