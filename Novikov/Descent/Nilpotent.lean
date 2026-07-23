import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Novikov.Descent.SquareZeroDeformation

/-!
# Nilpotent deformation of real Novikov descent data

This file promotes the square-zero deformation theorem to arbitrary nilpotent
coefficient ideals. The proof uses `Ideal.IsNilpotent.induction_on` and factors
surjective coefficient maps through intermediate quotient rings.
-/

namespace Novikov.Descent

open Abstract CategoryTheory Novikov.Miscellany

universe u

private theorem novikovDescent_of_surjective_of_isNilpotent_ker
    (A B : Type u) [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    (hK : IsNilpotent (RingHom.ker q))
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (hM : ∃ Q : FiniteProjectiveModule.{u, u} B,
      Nonempty
        ((vectToNovikovDescent.{0, u, u}
            (⊤ : AddSubgroup ℝ) B).obj Q ≅
          M.baseChange (realCCoeffHom q))) :
    ∃ P : FiniteProjectiveModule.{u, u} A,
      Nonempty
        ((vectToNovikovDescent.{0, u, u}
          (⊤ : AddSubgroup ℝ) A).obj P ≅ M) := by
  let P : ∀ {R : Type u} [CommRing R], Ideal R → Prop :=
    fun {R} _ K =>
      ∀ (S : Type u) [CommRing S]
        (f : R →+* S), Function.Surjective f → RingHom.ker f = K →
        ∀ N : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) R,
          (∃ Q : FiniteProjectiveModule.{u, u} S,
            Nonempty
              ((vectToNovikovDescent.{0, u, u}
                  (⊤ : AddSubgroup ℝ) S).obj Q ≅
                N.baseChange (realCCoeffHom f))) →
          ∃ Q : FiniteProjectiveModule.{u, u} R,
            Nonempty
              ((vectToNovikovDescent.{0, u, u}
                (⊤ : AddSubgroup ℝ) R).obj Q ≅ N)
  have hP : P (RingHom.ker q) := by
    apply Ideal.IsNilpotent.induction_on (I := RingHom.ker q) hK
    · intro R _ K hK S _ f hf hker N hN
      apply novikovDescent_squareZero_of_surjective R S f hf
      · rw [hker]
        exact hK
      · exact hN
    · intro R _ I J hIJ hPI hPJI S _ f hf hker N hN
      have hIf : I ≤ RingHom.ker f := by
        rw [hker]
        exact hIJ
      let fI : R ⧸ I →+* S := Ideal.Quotient.lift I f hIf
      have hfI : Function.Surjective fI := by
        intro s
        obtain ⟨r, rfl⟩ := hf s
        exact ⟨Ideal.Quotient.mk I r, rfl⟩
      have hkerI : RingHom.ker fI = J.map (Ideal.Quotient.mk I) := by
        rw [show fI = Ideal.Quotient.lift I f hIf from rfl,
          Ideal.ker_quotient_lift, hker]
      let NI := N.baseChange (realCCoeffHom (Ideal.Quotient.mk I))
      have hcomp : fI.comp (Ideal.Quotient.mk I) = f := by
        ext r
        rfl
      have eComp :
          NI.baseChange (realCCoeffHom fI) ≅
            N.baseChange (realCCoeffHom f) := by
        rw [← hcomp]
        exact novikovDescent_baseChangeCompIso
          (Ideal.Quotient.mk I) fI N
      have hNI : ∃ Q : FiniteProjectiveModule.{u, u} S,
          Nonempty
            ((vectToNovikovDescent.{0, u, u}
                (⊤ : AddSubgroup ℝ) S).obj Q ≅
              NI.baseChange (realCCoeffHom fI)) := by
        obtain ⟨Q, ⟨e⟩⟩ := hN
        exact ⟨Q, ⟨e ≪≫ eComp.symm⟩⟩
      obtain ⟨QI, ⟨eI⟩⟩ := hPJI S fI hfI hkerI NI hNI
      exact hPI (R ⧸ I) (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective Ideal.mk_ker N ⟨QI, ⟨eI⟩⟩
  exact hP B q hq rfl M hM

/-- Real Novikov descent data that become constant modulo a nilpotent ideal
are already constant. -/
theorem novikovDescent_nilpotent
    (A : Type u) [CommRing A]
    (I : Ideal A) (hI : IsNilpotent I)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A)
    (hM : ∃ Q : FiniteProjectiveModule.{u, u} (A ⧸ I),
      Nonempty
        ((vectToNovikovDescent.{0, u, u}
            (⊤ : AddSubgroup ℝ) (A ⧸ I)).obj Q ≅
          M.baseChange
            (realCCoeffHom (Ideal.Quotient.mk I)))) :
    ∃ P : FiniteProjectiveModule.{u, u} A,
      Nonempty
        ((vectToNovikovDescent.{0, u, u}
          (⊤ : AddSubgroup ℝ) A).obj P ≅ M) := by
  apply novikovDescent_of_surjective_of_isNilpotent_ker
    A (A ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  · simpa only [Ideal.mk_ker] using hI
  · exact hM

end Novikov.Descent
