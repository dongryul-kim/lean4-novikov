# Lean 4 formalization of Novikov descent

This repository formalizes the main results of
[Descending finite projective modules from a Novikov ring](https://arxiv.org/abs/2402.17852)
in Lean 4 and [mathlib](https://github.com/leanprover-community/mathlib4).

## Main result

Fix a commutative ring `A` and an additive submonoid `Γ ⊆ ℝ`.

### Novikov series

For a finite set of variables `ι`, a multivariable Novikov series with
coefficients in `A` is a coefficient function

```text
f : (ι → Γ) → A
```

satisfying the Novikov finiteness condition: for every positive weight vector
`s : ι → ℝ` and every cutoff `C : ℝ`, the set

```text
{d ∈ support(f) | ∑ i, s i * d i < C}
```

is finite. The resulting type is `Novikov.NovikovSeries Γ ι A` in Lean.
Addition is coefficientwise and multiplication is convolution. For one, two,
and three variables we write the resulting rings as

```text
R₁ = A((t^Γ))
R₂ = A((t^Γ, u^Γ))
R₃ = A((t^Γ, u^Γ, v^Γ)).
```

Substitution of variables defines two face maps `π₁, π₂ : R₁ → R₂`, placing
the one variable in the first or second coordinate, and three face maps
`π₁₂, π₁₃, π₂₃ : R₂ → R₃`, selecting the indicated pair of coordinates.
These maps satisfy the truncated semi-cosimplicial identities and are bundled
as `Novikov.Descent.novikovCosimplicialRing Γ A`.

### Descent data and constant objects

A Novikov descent datum is:

- a finite projective `R₁`-module `M`;
- an `R₂`-linear isomorphism

  ```text
  φ : R₂ ⊗[R₁, π₁] M ≃ₗ[R₂] R₂ ⊗[R₁, π₂] M;
  ```

- the cocycle identity
  `π₂₃* φ ∘ π₁₂* φ = π₁₃* φ` after base change to `R₃`.

A morphism of descent data is an `R₁`-linear map whose two pullbacks commute
with `φ`. Thus the Lean category is the abbreviation

```lean
NovikovDescentDatum Γ A :=
  DescentDatum (novikovCosimplicialRing Γ A)
```

`FiniteProjectiveModule A` is the source category: its objects are finite
projective `A`-modules and its morphisms are `A`-linear maps.

For a finite projective `A`-module `P`, its constant descent datum has
underlying module `R₁ ⊗[A] P`. Both pullbacks are canonically identified with
`R₂ ⊗[A] P`, which supplies the descent isomorphism. This construction is the
functor

```lean
vectToNovikovDescent Γ A :
  FiniteProjectiveModule A ⥤ NovikovDescentDatum Γ A
```

### The theorem

The main result is Theorem 1.1 of the paper, restated and proved there as
Theorem 4.9. It states that this functor is fully faithful and essentially
surjective. Concretely:

- every Novikov descent datum `M` is isomorphic to the constant datum of some
  finite projective `A`-module `P`;
- every morphism between constant data comes from a unique `A`-linear map
  between the corresponding finite projective modules.

The central Lean theorem has the following signature:

```lean
namespace Novikov.Descent

universe u v

variable {S : Type v} [SetLike S ℝ] [AddSubmonoidClass S ℝ]

theorem vectToNovikovDescent_isEquivalence
    (Γ : S) (A : Type u) [CommRing A] :
    (vectToNovikovDescent.{v, u, u} Γ A).IsEquivalence

end Novikov.Descent
```

The `SetLike` and `AddSubmonoidClass` assumptions make the theorem uniform in
the representation of the exponent set. In particular, it applies to
`Γ : AddSubmonoid ℝ`, as well as to additive subgroups such as the full real
exponent group `(⊤ : AddSubgroup ℝ)`.

It is also packaged as the categorical equivalence

```lean
vectToNovikovDescent_equivalence Γ A :
  FiniteProjectiveModule A ≌ NovikovDescentDatum Γ A
```

Both declarations are in
[`Novikov/Descent/Exponent.lean`](Novikov/Descent/Exponent.lean).

## Proof outline

The formal proof follows the paper rather than invoking a general faithfully
flat descent theorem.

1. **Novikov series and descent data.** The development constructs
   multivariable Novikov rings, substitution maps, the truncated cosimplicial
   ring, and its category of finite-projective descent data. The constant
   descent functor is proved fully faithful.
2. **Real exponents.** For `Γ = ℝ`, a descent datum gives a Novikov
   isocrystal. Constancy is first proved over algebraically closed fields, then
   products of such fields, reduced rings, and finally arbitrary commutative
   rings via nilpotent deformation.
3. **Arbitrary exponents.** Extension by zero embeds `Γ`-exponent series into
   real-exponent series. A real trivialization is shown to have support in
   `Γ`, so it restricts to an injective map into a constant object. Repeating
   the construction for the dual produces a right inverse, hence an
   isomorphism. This argument only uses injectivity reflected through finite
   projective modules; it does not assume the exponent-extension map is
   faithfully flat.

## Repository layout

- [`Novikov/Series/`](Novikov/Series/) — Novikov series, multiplication,
  substitution, modules, Frobenius, topology, and exponent extension.
- [`Novikov/Isocrystal/`](Novikov/Isocrystal/) — Novikov isocrystals and their
  constancy criteria.
- [`Novikov/Descent/Abstract/`](Novikov/Descent/Abstract/) — abstract
  cosimplicial rings, descent data, base change, constants, and duality.
- [`Novikov/Descent/`](Novikov/Descent/) — Novikov descent and the reductions
  from algebraically closed fields to arbitrary rings.
- [`Novikov/Descent/Exponent/`](Novikov/Descent/Exponent/) — support
  restriction and the duality argument for arbitrary exponent monoids.
- [`Novikov.lean`](Novikov.lean) — root import for the formalization.
- [`blueprint/`](blueprint/) — the mathematical blueprint and its dependency
  graph.

## Documentation

- [Blueprint website](https://dongryul-kim.github.io/lean4-novikov/blueprint/)
- [Blueprint PDF](https://dongryul-kim.github.io/lean4-novikov/blueprint.pdf)
- [Lean API documentation](https://dongryul-kim.github.io/lean4-novikov/docs/)
- [Original paper](https://arxiv.org/abs/2402.17852)

The blueprint records the mathematical statements, proof sketches, and links
to their corresponding Lean declarations.  Its lint requires such a link on
every completed node and verifies that the labeled dependency graph is a
connected acyclic graph rooted at the main theorem.

## Building

The project pins Lean in [`lean-toolchain`](lean-toolchain) and its dependencies
in `lake-manifest.json`. With [elan](https://github.com/leanprover/elan)
installed, run:

```bash
lake build
```

To use mathlib's precompiled cache before building, run:

```bash
lake exe cache get
lake build
```

With [leanblueprint](https://github.com/PatrickMassot/leanblueprint) installed,
lint and build the PDF and web blueprint with:

```bash
python3 blueprint/lint.py
leanblueprint all
```

## Acknowledgements

The formalization was developed with substantial assistance from several AI
models, under human guidance and review.
