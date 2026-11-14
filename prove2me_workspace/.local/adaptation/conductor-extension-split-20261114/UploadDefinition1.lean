/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation; see SOURCE_LEDGER.md.
-/
import Definitions.Def_FermatBelyiConductorExtensionFinitePlaces

set_option autoImplicit false
open NumberField IsDedekindDomain Module
open scoped Classical IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

open ConductorExtensionSource

/-- Exact source Conductor.lean:104, restricted to the actual inclusion φ(x)-field ⊆ x-field.
The left term is normalized by the image-field degree; all right terms by the full point-field
 degree. No field, algebra, height, or correction term is supplied by a model law. -/
def BelyiActualFieldLocalConductorComparison : Prop :=
  ∀ {N : ℕ} (M : Model N) (hRF : ResiduesFinite M) (φ : M.K)
    (x : QbarPoint M.K) (hgood : GoodValue M x φ),
    letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
    letI : Algebra (Tripod.fieldOf (belyiImage M φ x).1) x.fieldOf :=
      (IntermediateField.inclusion (belyiImage_field_le M φ x hgood)).toRingHom.toAlgebra
    ∀ u : FinitePlace (Tripod.fieldOf (belyiImage M φ x).1),
      Real.log (placeNorm u) / finrank ℚ (Tripod.fieldOf (belyiImage M φ x).1) ≤
        (∑ w ∈ placesOver x.fieldOf u, Real.log (placeNorm w) / finrank ℚ x.fieldOf) +
          diffContrib x.fieldOf u.maximalIdeal.asIdeal

/-- Exact source NumberField.lean:228/256, for the same actual inclusion.
The support finiteness is explicit: `finsum` alone does not justify a finite-subsum bound.
This child has no conductor inequality or finite element sets hidden in its statement. -/
def BelyiActualFieldDifferentAccounting : Prop :=
  ∀ {N : ℕ} (M : Model N) (hRF : ResiduesFinite M) (φ : M.K)
    (x : QbarPoint M.K) (hgood : GoodValue M x φ),
    letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
    letI : Algebra (Tripod.fieldOf (belyiImage M φ x).1) x.fieldOf :=
      (IntermediateField.inclusion (belyiImage_field_le M φ x hgood)).toRingHom.toAlgebra
    (Function.support fun 𝔭 : HeightOneSpectrum
      (𝓞 (Tripod.fieldOf (belyiImage M φ x).1)) =>
        diffContrib x.fieldOf 𝔭.asIdeal).Finite ∧
    Real.log (Ideal.absNorm
      (differentIdeal (𝓞 (Tripod.fieldOf (belyiImage M φ x).1)) (𝓞 x.fieldOf))) /
        finrank ℚ x.fieldOf =
      ∑ᶠ 𝔭 : HeightOneSpectrum (𝓞 (Tripod.fieldOf (belyiImage M φ x).1)),
        diffContrib x.fieldOf 𝔭.asIdeal

end AbcAdaptation.Tripod.Fermat.Proper
