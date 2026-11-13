/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors
-/
import Definitions.Def_FermatLocalBelyiComposition
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The actual canonical divisor has the Fermat canonical degree. The
infinity and adjunction data are concrete inputs to this identity. -/
def CanonicalDegreeIdentity : Prop :=
  ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M), 3 < N →
    ResiduesFinite M → ∀ (K : CanonicalDivisorData M hDVR)
      (H : InfinityDivisorData M hDVR),
      PlaneAdjunctionData M hDVR K H →
      divisorDegree M K.D = planeCanonicalDegree N

/-- Explicit identification of the true canonical divisor height with the
existing fixed projective Fermat height. No identity is presumed by a name. -/
def CanonicalHeightIdentification : Prop :=
  ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M), 3 < N →
    ResiduesFinite M → ∀ (A : AffineIdentification M)
      (K : CanonicalDivisorData M hDVR) (H : InfinityDivisorData M hDVR),
      PlaneAdjunctionData M hDVR K H →
      ∀ RK : PolarPresentation M hDVR K.D,
      ∃ C : ℝ, ∀ p : Fermat.Pt N,
        |divHeight RK (affineLift M A p) - Fermat.canonicalHeight p| ≤ C

/-- The actual Belyi canonical+cusp height relation on the good open part. -/
def BelyiHeightRelation : Prop :=
  ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M), ResiduesFinite M →
    ∀ (A : AffineIdentification M) (φ : M.K), IsBelyi M hDVR φ →
      ∀ (hfin : (cusps M hDVR φ).Finite)
        (B : ArithmeticDivisorChoices M hDVR φ hfin),
      ∃ C : ℝ, ∀ p : Fermat.Pt N, GoodValue M (affineLift M A p) φ →
        |divHeight B.canonicalPresentation (affineLift M A p) +
            divHeight B.cuspPresentation (affineLift M A p) -
            Tripod.htCan (belyiImage M φ (affineLift M A p))| ≤ C

/-- The genuine strict degree comparison of heights on a curve. Both
functions are computed from exact polar presentations of actual divisors. -/
def DivisorDegreeHeightComparison : Prop :=
  ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M), ResiduesFinite M →
    ∀ (D E : Divisor M) (RD : PolarPresentation M hDVR D)
      (RE : PolarPresentation M hDVR E) (q : ℝ),
      0 < divisorDegree M D →
      (divisorDegree M E : ℝ) < q * divisorDegree M D →
      ∃ C : ℝ, ∀ x : QbarPoint M.K, divHeight RE x ≤ q * divHeight RD x + C

/-- Normalized discriminant/conductor tower inequality for the actual
point fields and actual affine generators; image field degrees can differ. -/
def BelyiDifferentConductorComparison : Prop :=
  ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M),
    ∀ (A : AffineIdentification M) (φ : M.K), IsBelyi M hDVR φ →
      ∀ (hfin : (cusps M hDVR φ).Finite)
        (G : CuspGenerators M hDVR φ hfin),
      ∃ C : ℝ, ∀ p : Fermat.Pt N, GoodValue M (affineLift M A p) φ →
        Tripod.logDiff (belyiImage M φ (affineLift M A p)) +
          Tripod.logCond (belyiImage M φ (affineLift M A p)) ≤
        Fermat.logDiff p + logCondOf M hRF G.G (affineLift M A p) + C

/-- The actual cusp conductor is bounded by a height of its effective
reduced divisor, uniformly in points on that affine model. -/
def CuspConductorHeightComparison : Prop :=
  ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M),
    ∀ (A : AffineIdentification M) (φ : M.K), IsBelyi M hDVR φ →
      ∀ (hfin : (cusps M hDVR φ).Finite)
        (G : CuspGenerators M hDVR φ hfin)
        (RE : PolarPresentation M hDVR (cuspDivisor M hDVR φ hfin)),
      ∃ C : ℝ, ∀ p : Fermat.Pt N, GoodValue M (affineLift M A p) φ →
        logCondOf M hRF G.G (affineLift M A p) ≤
          divHeight RE (affineLift M A p) + C

end AbcAdaptation.Tripod.Fermat.Proper
