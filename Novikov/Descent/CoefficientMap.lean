import Novikov.Descent.Abstract.BaseChange
import Novikov.Descent.Isocrystal
import Novikov.Series.Product

/-!
# Coefficient maps on real Novikov descent rings

A homomorphism of coefficient rings induces a homomorphism between the real
Novikov cosimplicial rings by applying it coefficientwise in every degree.
-/

open Novikov.Descent.Abstract

namespace Novikov.Descent

universe u v

/-- The coefficientwise homomorphism between real Novikov cosimplicial rings
induced by a homomorphism of coefficient rings. -/
noncomputable def realCCoeffHom {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) :
    CosimplicialRingHom (realC A) (realC B) where
  f₁ := Novikov.mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) f
  f₂ := Novikov.mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) f
  f₃ := Novikov.mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 3) f
  comm_π₁ := by
    ext x
    simpa [realC] using Novikov.mapRingHom_substitute
      (Γ := (⊤ : AddSubgroup ℝ)) f (fun _ : Unit => (0 : Fin 2)) x
  comm_π₂ := by
    ext x
    simpa [realC] using Novikov.mapRingHom_substitute
      (Γ := (⊤ : AddSubgroup ℝ)) f (fun _ : Unit => (1 : Fin 2)) x
  comm_π₁₂ := by
    ext x
    simpa [realC] using Novikov.mapRingHom_substitute
      (Γ := (⊤ : AddSubgroup ℝ)) f Fin.castSucc x
  comm_π₁₃ := by
    ext x
    simpa [realC] using Novikov.mapRingHom_substitute
      (Γ := (⊤ : AddSubgroup ℝ)) f (Fin.succAbove 1) x
  comm_π₂₃ := by
    ext x
    simpa [realC] using Novikov.mapRingHom_substitute
      (Γ := (⊤ : AddSubgroup ℝ)) f Fin.succ x

@[simp]
lemma realCCoeffHom_f₁ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (realCCoeffHom f).f₁ =
      Novikov.mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Unit) f := rfl

@[simp]
lemma realCCoeffHom_f₂ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (realCCoeffHom f).f₂ =
      Novikov.mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 2) f := rfl

@[simp]
lemma realCCoeffHom_f₃ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (realCCoeffHom f).f₃ =
      Novikov.mapRingHom (Γ := (⊤ : AddSubgroup ℝ)) (ι := Fin 3) f := rfl

end Novikov.Descent
