import Novikov.Descent.Abstract.ConstantBaseChange
import Novikov.Descent.Isocrystal
import Novikov.Series.Product

/-!
# Coefficient maps on real Novikov descent rings

A homomorphism of coefficient rings induces a homomorphism between the real
Novikov cosimplicial rings by applying it coefficientwise in every degree.
-/

namespace Novikov

variable {S : Type*} [SetLike S ℝ] [AddSubmonoidClass S ℝ]
variable {Γ : S} {ι A B : Type*} [Fintype ι] [CommRing A] [CommRing B]

/-- Coefficientwise maps on Novikov rings commute with constant coefficients. -/
lemma mapRingHom_comp_algebraMapNovikov (q : A →+* B) :
    (mapRingHom (Γ := Γ) (ι := ι) q).comp algebraMapNovikov =
      algebraMapNovikov.comp q := by
  ext a d
  simp only [RingHom.coe_comp, Function.comp_apply, mapRingHom_apply]
  by_cases hd : d = 0
  · subst d
    simp [algebraMapNovikov]
  · simp [algebraMapNovikov, hd]

/-- Applying two coefficient maps successively agrees with applying their
composite. -/
lemma mapRingHom_comp {C : Type*} [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    mapRingHom (Γ := Γ) (ι := ι) (g.comp f) =
      (mapRingHom (Γ := Γ) (ι := ι) g).comp
        (mapRingHom (Γ := Γ) (ι := ι) f) := by
  ext x d
  rfl

end Novikov

open Novikov.Descent.Abstract

namespace Novikov.Descent

open Novikov.Miscellany

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

/-- The coefficientwise morphism of extended real Novikov cosimplicial rings. -/
noncomputable def realExtendedCoeffHom {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) :
    ExtendedCosimplicialRingHom
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) A)
      (novikovExtendedCosimplicialRing (⊤ : AddSubgroup ℝ) B) where
  toCosimplicialRingHom := realCCoeffHom f
  f₀ := f
  comm_π₀ := Novikov.mapRingHom_comp_algebraMapNovikov f

@[simp]
lemma realExtendedCoeffHom_f₀ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (realExtendedCoeffHom f).f₀ = f := rfl

@[simp]
lemma realExtendedCoeffHom_toCosimplicialRingHom {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (realExtendedCoeffHom f).toCosimplicialRingHom = realCCoeffHom f := rfl

@[simp]
lemma realExtendedCoeffHom_f₁ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (realExtendedCoeffHom f).f₁ = (realCCoeffHom f).f₁ := rfl

@[simp]
lemma realExtendedCoeffHom_f₂ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (realExtendedCoeffHom f).f₂ = (realCCoeffHom f).f₂ := rfl

@[simp]
lemma realExtendedCoeffHom_f₃ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (realExtendedCoeffHom f).f₃ = (realCCoeffHom f).f₃ := rfl

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

/-- Cosimplicial coefficient maps preserve composition. -/
lemma realCCoeffHom_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    realCCoeffHom (g.comp f) =
      (realCCoeffHom g).comp (realCCoeffHom f) := by
  apply CosimplicialRingHom.ext <;>
    simp only [realCCoeffHom_f₁, realCCoeffHom_f₂,
      realCCoeffHom_f₃, CosimplicialRingHom.comp_f₁,
      CosimplicialRingHom.comp_f₂, CosimplicialRingHom.comp_f₃]
  · exact Novikov.mapRingHom_comp f g
  · exact Novikov.mapRingHom_comp f g
  · exact Novikov.mapRingHom_comp f g

/-- Iterated coefficient base change of real Novikov descent data agrees with
base change along the composite coefficient map. -/
noncomputable def novikovDescent_baseChangeCompIso
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (M : NovikovDescentDatum.{0, u, u} (⊤ : AddSubgroup ℝ) A) :
    (M.baseChange (realCCoeffHom f)).baseChange (realCCoeffHom g) ≅
      M.baseChange (realCCoeffHom (g.comp f)) := by
  rw [realCCoeffHom_comp f g]
  exact M.baseChangeCompIso (realCCoeffHom f) (realCCoeffHom g)

/-- Constant real Novikov descent commutes with coefficient base change. -/
noncomputable def vectToNovikovDescent_baseChangeIso
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (P : FiniteProjectiveModule.{u, u} A) :
    ((vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) A).obj P).baseChange
        (realCCoeffHom f) ≅
      (vectToNovikovDescent.{0, u, u} (⊤ : AddSubgroup ℝ) B).obj
        (P.baseChange f) := by
  exact constantDescentDatum_baseChangeIso (realExtendedCoeffHom f) P

end Novikov.Descent
