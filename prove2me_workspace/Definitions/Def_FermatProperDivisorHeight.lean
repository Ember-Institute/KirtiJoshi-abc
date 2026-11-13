/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent adaptation of Heights/Curve/{TupleHeight,DivisorHeight,Conductor}.lean
at 721496ca4c158e511d25d8ccf6bfe8503eda73c1. Choices of rational functions and
generators are explicit data. Their existence is not imported into Definitions.
-/
import Definitions.Def_FermatProperCarrier

set_option autoImplicit false

open NumberField
open scoped Classical IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

/-- The multiplicity of the polar divisor, including the source convention
that the zero function has zero polar divisor. -/
noncomputable def poleMultiplicity (M : Model N) (hDVR : PlacesDiscrete M)
    (f : M.K) (P : Place M.K) : ℤ :=
  max 0 (-ord M hDVR P f)

/-- An exact presentation of a genuine divisor by two rational functions.
The pointwise equality fixes every coefficient on the proper model.
The existence of this data is Riemann's theorem, a separate open child. -/
structure PolarPresentation (M : Model N) (hDVR : PlacesDiscrete M)
    (D : Divisor M) where
  f : M.K
  g : M.K
  divisor_eq : ∀ P : Place M.K,
    D P = poleMultiplicity M hDVR f P - poleMultiplicity M hDVR g P

/-- The actual absolute logarithmic height of a rational function at a
proper point. A pole maps to [0:1], whose height is zero. At a regular point
the value is measured in its actual minimal number field ℚ(f(x)).
This is the source's `tupleHeight ![1,f]`, with field normalization made explicit. -/
noncomputable def functionHeight (M : Model N) (f : M.K)
    (x : QbarPoint M.K) : ℝ :=
  if hf : f ∈ x.P.1 then
    Height.logHeight₁ (AbcAdaptation.Tripod.gen (x.eval f hf)) /
      AbcAdaptation.Tripod.deg (x.eval f hf)
  else 0

theorem functionHeight_of_regular (M : Model N) (f : M.K)
    (x : QbarPoint M.K) (hf : f ∈ x.P.1) :
    functionHeight M f x =
      Height.logHeight₁ (AbcAdaptation.Tripod.gen (x.eval f hf)) /
        AbcAdaptation.Tripod.deg (x.eval f hf) := by
  simp only [functionHeight, dif_pos hf]

theorem functionHeight_of_pole (M : Model N) (f : M.K)
    (x : QbarPoint M.K) (hf : f ∉ x.P.1) : functionHeight M f x = 0 := by
  simp only [functionHeight, dif_neg hf]

/-- The regular value zero also has height zero. The pole branch does not
confuse a zero value with a pole of the rational function. -/
theorem functionHeight_of_eval_zero (M : Model N) (f : M.K)
    (x : QbarPoint M.K) (hf : f ∈ x.P.1) (h0 : x.eval f hf = 0) :
    functionHeight M f x = 0 := by
  rw [functionHeight_of_regular M f x hf, h0]
  have hg : AbcAdaptation.Tripod.gen (0 : Qbar) = 0 := by
    apply Subtype.ext
    exact AbcAdaptation.Tripod.coe_gen 0
  rw [hg, Height.logHeight₁_zero, zero_div]

/-- A Weil divisor height from an explicitly chosen polar presentation.
No function on the point carrier is supplied by the caller. -/
noncomputable def divHeight {M : Model N} {hDVR : PlacesDiscrete M}
    {D : Divisor M} (R : PolarPresentation M hDVR D)
    (x : QbarPoint M.K) : ℝ :=
  functionHeight M R.f x - functionHeight M R.g x

/-- The height of the actual reduced cusp divisor, for a concrete Riemann
presentation of that divisor. -/
noncomputable def cuspHeight {M : Model N} {hDVR : PlacesDiscrete M}
    {φ : M.K} {hfin : (cusps M hDVR φ).Finite}
    (R : PolarPresentation M hDVR (cuspDivisor M hDVR φ hfin))
    (x : QbarPoint M.K) : ℝ :=
  divHeight R x

/-- The arithmetic degree ratio is tied to an actual canonical divisor.
At a regular point, ord(du)=e_u-1; at a pole it is -e_u-1.
These are the coefficients proved in pinned Belyi/CurveField/Canonical.lean.
Finiteness of this exact coefficient function is a separate open child.
In particular, D cannot be an arbitrarily selected divisor of the right degree. -/
structure CanonicalDivisorData (M : Model N) (hDVR : PlacesDiscrete M) where
  D : Divisor M
  coefficient : ∀ P : Place M.K,
    D P = if M.u ∈ P.1 then ramIdx M hDVR M.u P - 1
      else -ramIdx M hDVR M.u P - 1

/-- The projective hyperplane [W=0] in the fixed Fermat presentation.
Its multiplicity is the largest pole order of the coordinates U/W,V/W.
No affine point, including no point at infinity, has been removed here. -/
structure InfinityDivisorData (M : Model N) (hDVR : PlacesDiscrete M) where
  H : Divisor M
  coefficient : ∀ P : Place M.K,
    H P = max (poleMultiplicity M hDVR M.u P)
      (poleMultiplicity M hDVR M.v P)

/-- Concrete adjunction data. It says div(du) is linearly equivalent to
(N-3)H through the divisor of this actual nonzero rational function r.
It does not assume a height comparison or the desired canonical estimate. -/
structure PlaneAdjunctionData (M : Model N) (hDVR : PlacesDiscrete M)
    (K : CanonicalDivisorData M hDVR) (H : InfinityDivisorData M hDVR) where
  r : M.K
  r_ne_zero : r ≠ 0
  coefficient : ∀ P : Place M.K,
    K.D P = ((N : ℤ) - 3) * H.H P + ord M hDVR P r

/-- The coordinate ring of the complement of supp D. Its elements are
precisely rational functions regular at every place outside supp D. -/
def coordRing (M : Model N) (D : Divisor M) : Subalgebra ℚ M.K where
  carrier := {f | ∀ P : Place M.K, D P = 0 → f ∈ P.1}
  algebraMap_mem' q P _ := by simpa using P.2.2 q
  zero_mem' P _ := P.1.zero_mem
  one_mem' P _ := P.1.one_mem
  add_mem' hf hg P hP := P.1.add_mem _ _ (hf P hP) (hg P hP)
  mul_mem' hf hg P hP := P.1.mul_mem _ _ (hf P hP) (hg P hP)

/-- A genuine finite affine model of the complement of the Belyi cusps,
with the three tripod functions included among its concrete generators.
The equality is equality of actual subalgebras, not just a regularity label. -/
structure CuspGenerators (M : Model N) (hDVR : PlacesDiscrete M)
    (φ : M.K) (hfin : (cusps M hDVR φ).Finite) where
  G : Finset M.K
  generate : Algebra.adjoin ℚ (G : Set M.K) =
    coordRing M (cuspDivisor M hDVR φ hfin)
  phi_mem : φ ∈ G
  inv_phi_mem : φ⁻¹ ∈ G
  inv_one_sub_phi_mem : (1 - φ)⁻¹ ∈ G

/-- The point field is the image of its residue field; finiteness is
transported from the separately exposed residue-finiteness theorem.
This proof does not introduce a new existence assumption or global instance. -/
theorem pointField_finiteDimensional (M : Model N) (hRF : ResiduesFinite M)
    (x : QbarPoint M.K) : FiniteDimensional ℚ x.fieldOf := by
  letI : FiniteDimensional ℚ x.P.ResidueField := hRF x.P
  exact x.σ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional

/-- The value of an actual regular rational function in the full point field. -/
noncomputable def evalInPointField {M : Model N} (x : QbarPoint M.K)
    (f : M.K) (hf : f ∈ x.P.1) : x.fieldOf :=
  ⟨x.eval f hf, x.eval_mem_fieldOf f hf⟩

/-- The normalized log-conductor of the affine arithmetic model specified
by G. A finite prime contributes exactly once if some generator has norm >1.
The denominator is the degree of the full point field, not ℚ(φ(x)).
As in the pinned source, the total extension at a point outside the affine
model is zero; all comparison theorems restrict to points where G is regular. -/
noncomputable def logCondOf (M : Model N) (hRF : ResiduesFinite M)
    (G : Finset M.K) (x : QbarPoint M.K) : ℝ := by
  letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
  exact if hG : ∀ g ∈ G, g ∈ x.P.1 then
    (∑ᶠ w : FinitePlace x.fieldOf,
      if ∃ (g : M.K) (hg : g ∈ G), 1 < w (evalInPointField x g (hG g hg))
      then Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) else 0) / x.degree
  else 0

/-- The normalized discriminant of the same actual point field used by
logCondOf. AffineIdentification.field_eq transfers it to the fixed Fermat
logDiff after proving equality of the degrees. -/
noncomputable def pointLogDiff (M : Model N) (hRF : ResiduesFinite M)
    (x : QbarPoint M.K) : ℝ := by
  letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
  exact Real.log |(NumberField.discr x.fieldOf : ℝ)| / x.degree

/-- A finite package of concrete choices needed by the next arithmetic
steps. It contains rational functions, divisors with fixed coefficients,
and generators of an actual coordinate ring. It contains no height function
or estimate. Every existence assertion is supplied as a separate child. -/
structure ArithmeticDivisorChoices (M : Model N) (hDVR : PlacesDiscrete M)
    (φ : M.K) (hfin : (cusps M hDVR φ).Finite) where
  canonical : CanonicalDivisorData M hDVR
  infinity : InfinityDivisorData M hDVR
  adjunction : PlaneAdjunctionData M hDVR canonical infinity
  canonicalPresentation : PolarPresentation M hDVR canonical.D
  cuspPresentation : PolarPresentation M hDVR (cuspDivisor M hDVR φ hfin)
  generators : CuspGenerators M hDVR φ hfin

end AbcAdaptation.Tripod.Fermat.Proper
