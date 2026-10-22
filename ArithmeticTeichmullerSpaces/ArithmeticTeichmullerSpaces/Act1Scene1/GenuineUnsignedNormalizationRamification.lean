/-
original-path: `refer/iut/Iut/Anabelian/Genuine/Homs.lean`
original-author: Christian Merten <lana@merten.dev> (Git author)
original-file-authors: The iut contributors
original-coauthor: Claude Opus 5.5 (1M context) <noreply@anthropic.com> (Git trailer)
original-commit: `b51b94cad5c729f753ed0790b5fb95d9d65aaff1`
additional-source: `refer/iut/Iut/Anabelian/Genuine/Cover.lean`, effLevel_smul_Mbar,
commit `7b3756ff3fde46bbd4daa89076fd4bc9c4e60baf` (same author and license).
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the source copyright and Apache-2.0 license before
copying. No NOTICE file occurs in the reference tree. Retain the notice below.
modifications: use the proved local prime-inertia theorem and the actual
normalization fields. Build the finite Galois closure of the full division
field. Prove unramifiedness above the level-one unsigned field.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineUnsignedNormalizationFields

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Genuine/Homs.lean, ramificationIdx_geom_eq_one.
fidelity: the actual unsigned normalization over the actual level-one unsigned
normalization has ramification index one at every closed point. The proof uses
an actual finite Galois closure, actual prime inertia and the proved comparison.
boundary: Scene1/Derived. Orbicurve comparison, the global cartesian square,
core and the full geometric producer remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped Classical IntermediateField.algebraAdjoinAdjoin Pointwise
attribute [local instance 2000] Classical.propDecidable
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

attribute [local instance] finite_divisionNormalClosure galois_divisionNormalClosure
  primeNormalizationSeparable primeNormalizationCoeffComm
  primeNormalizationDedekind primeNormalizationFraction
  FunctionFieldNormalization.galoisNormalizationCoeffComm FunctionFieldNormalization.fieldRingAction

/-- The actual unsigned normalization has no ramification over the actual base curve. -/
theorem unsignedNormalization_ramificationIdx_one (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (w : Ideal (coverCoordinateRing E ell M false)) (hw : w.IsMaximal) :
    (letI := FunctionFieldNormalization.ringMapAlgebra (normalization_base_unsigned_le E ell M)
     w.ramificationIdx (coverCoordinateRing E 1 ⊥ false)) = 1 := by
  have : w.IsMaximal := hw
  let F := normalizationField E 1 ⊥ false
  let L := normalizationField E ell M false
  let N := divisionNormalClosure E ell
  have hFL : F ≤ L := normalization_base_unsigned_le E ell M
  have hLN : L ≤ N := normalization_unsigned_le_divisionNormalClosure E ell M
  obtain ⟨u, hu, hul⟩ : ∃ u : Ideal (FunctionFieldNormalization.coordRing (xG E) N),
      u.IsMaximal ∧ u.comap (FunctionFieldNormalization.ringMap hLN) = w :=
    FunctionFieldNormalization.normalization_exists_maximal_over hLN w hw
  have : u.IsMaximal := hu
  have hr : (letI := FunctionFieldNormalization.ringMapAlgebra hFL
      (u.comap (FunctionFieldNormalization.ringMap hLN)).ramificationIdx
        (FunctionFieldNormalization.coordRing (xG E) F)) = 1 := by
    apply (FunctionFieldNormalization.ramificationIdx_eq_one_iff
      (transcendental_xG E) hFL hLN u).mpr
    rintro τ ⟨hτI, hτF⟩ x hx
    have hyF : yG E ∈ F := normalization_yG_mem_unsigned E 1 ⊥
    have hyN : yG E ∈ N := hLN (hFL hyF)
    have hτy : τ ⟨yG E, hyN⟩ = ⟨yG E, hyN⟩ := hτF ⟨yG E, hyN⟩ hyF
    let p : IsDedekindDomain.HeightOneSpectrum
        (FunctionFieldNormalization.coordRing (xG E) N) :=
      ⟨u, hu.isPrime, normalization_maximal_ne_bot E N u hu⟩
    exact normalizationPrime_inertia_fixes_unsignedField E N ell
      (normalizationFull_le_divisionNormalClosure E ell) hyN p τ hτI hτy M x hx
  rw [hul] at hr
  exact hr

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
