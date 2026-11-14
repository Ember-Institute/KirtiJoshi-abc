import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalCuspPolarLinearEquivalence
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_polarPresentationHeightSum_of_principalRelation
/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors

Independent adaptation of Genl/Curves/BelyiDescent.lean:215 at
ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf. Both exact mathematical
child inputs below remain separate open theorem obligations.
-/
import Definitions.Def_FermatBelyiComparisons

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The good-open value has precisely the existing tripod height.
This identity uses the actual minimal field of φ(x); it adds no error term. -/
theorem functionHeight_eq_htCan_belyiImage {N : ℕ}
    (M : Model N) (φ : M.K) (x : QbarPoint M.K) (hgood : GoodValue M x φ) :
    functionHeight M φ x = Tripod.htCan (belyiImage M φ x) := by
  obtain ⟨hφ, h0, h1⟩ := hgood
  rw [functionHeight_of_regular M φ x hφ, belyiImage_eq M φ x hφ h0 h1]
  rfl

/-- The original comparison follows from the actual divisor coefficient
relation and the general height comparison for every explicit presentation. -/
theorem belyiHeightRelation_of_children
    (hGeometry : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
      (hRF : ResiduesFinite M) (φ : M.K) (hφ : IsBelyi M hDVR φ)
      (hfin : (cusps M hDVR φ).Finite) (K : CanonicalDivisorData M hDVR),
      ∃ r : M.K, r ≠ 0 ∧ ∀ P : Place M.K,
        K.D P + cuspDivisor M hDVR φ hfin P =
          poleMultiplicity M hDVR φ P + ord M hDVR P r)
    (hPolarHeights : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
      (hRF : ResiduesFinite M) (D E : Divisor M)
      (RD : PolarPresentation M hDVR D) (RE : PolarPresentation M hDVR E)
      (f r : M.K) (hr : r ≠ 0)
      (hrel : ∀ P : Place M.K,
        D P + E P = poleMultiplicity M hDVR f P + ord M hDVR P r),
      ∃ C : ℝ, ∀ x : QbarPoint M.K,
        |divHeight RD x + divHeight RE x - functionHeight M f x| ≤ C) :
    BelyiHeightRelation := by
  intro N M hDVR hRF A φ hφ hfin B
  obtain ⟨r, hr, hrel⟩ := hGeometry M hDVR hRF φ hφ hfin B.canonical
  obtain ⟨C, hC⟩ := hPolarHeights M hDVR hRF
    B.canonical.D (cuspDivisor M hDVR φ hfin)
    B.canonicalPresentation B.cuspPresentation φ r hr hrel
  refine ⟨C, ?_⟩
  intro p hgood
  rw [← functionHeight_eq_htCan_belyiImage M φ (affineLift M A p) hgood]
  exact hC (affineLift M A p)

end AbcAdaptation.Tripod.Fermat.Proper

theorem solution : AbcAdaptation.Tripod.Fermat.Proper.BelyiHeightRelation :=
  AbcAdaptation.Tripod.Fermat.Proper.belyiHeightRelation_of_children
    AbcAdaptation.Tripod.Fermat.Proper.canonicalCuspPolarLinearEquivalence
    AbcAdaptation.Tripod.Fermat.Proper.polarPresentationHeightSum_of_principalRelation
