/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalQRootNorm

/-!
source-id: JT-SCENE1-CANONICAL-QROOT-NORM-ACCOUNTING
source: Joshi III `cor:cor312` local q-factor normalization and the actual
q-root source; the preceding `CanonicalQRootNorm` local identity.
fidelity: lifts the proved pointwise paper-normalized root identity to the
finite actual q-root source carrier. The relative ramification factor remains
explicit, so this is not an `L'` representative sum or a paper theta-volume.
boundary: Scene1/Derived. Paper representative multiplicity, unweighted
paper sums, and the theta-volume identity remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.CanonicalQRootNorm

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open NumberField
open scoped BigOperators

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data D.F O p}
variable (hTate : T.scene1.data.link.tate = iutInitialThetaTateParameterData D)
variable (hCompat : QNormTateCompatibility T.scene1.data.link)

/-- The finite actual q-root source has an exact relative-ramification weighted
paper-normalized logarithmic accounting identity. -/
theorem sum_negLog_paperRootNorm_eq_relRamWeightedPaperFactorSum
    (hEll : T.ell = D.prime.ℓ) :
    (∑ v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset,
      -Real.log (paperRootNorm D v)) =
      ∑ v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset,
        (relRamIdx v.1 (baseIndex D p hTate hCompat v).1 : ℝ) *
          (-Real.log (Corollary312PaperNormalizedSourceQFactor p T
            (baseIndex D p hTate hCompat v))) := by
  classical
  apply Finset.sum_congr rfl
  intro v hv
  exact negLog_paperRootNorm_eq_paperFactor_log_mul
    D p hTate hCompat hEll v

end
end JoshiTeich.Act1Scene1.CanonicalQRootNorm
