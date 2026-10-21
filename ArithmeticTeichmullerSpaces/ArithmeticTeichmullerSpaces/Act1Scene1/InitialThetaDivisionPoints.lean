import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.DivisionPoints
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaFunctionField

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Pi1.lean`, compatible division points.
fidelity: constructs every positive-level generic division point on the same
seed's curve over its torsion field. The coherent system is obtained from the
proved scalar-multiplication theorem, with no divisibility/source law parameter.
boundary: Scene1/Derived. Covering/core/theta-root realization remains open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical

universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The coherent division point at level `n` for the seed's actual generic point. -/
def functionFieldDivisionPoint (n : ℕ) :
    (S.prime.EK⁄S.functionFieldClosure).toAffine.Point :=
  Genuine.divSys S.prime.EK n

@[simp] theorem functionFieldDivisionPoint_one :
    S.functionFieldDivisionPoint 1 = S.functionFieldGenericPoint :=
  Genuine.divSys_one S.prime.EK

theorem functionFieldDivisionPoint_compatible (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    n • S.functionFieldDivisionPoint (n * m) = S.functionFieldDivisionPoint m :=
  Genuine.mul_nsmul_divSys S.prime.EK n m hn hm

/-- These are actual preimages of this same generic point under `[n]`. -/
theorem nsmul_functionFieldDivisionPoint (n : ℕ) (hn : 0 < n) :
    n • S.functionFieldDivisionPoint n = S.functionFieldGenericPoint :=
  Genuine.nsmul_divSys S.prime.EK n hn

theorem functionFieldDivisionPoint_ne_torsion (n : ℕ) (hn : 0 < n) (R : ↥S.prime.TK) :
    S.functionFieldDivisionPoint n ≠ S.functionFieldTorsionMap R :=
  Genuine.divSys_ne_base S.prime.EK n hn R

theorem functionFieldDivisionPoint_ne_zero (n : ℕ) (hn : 0 < n) :
    S.functionFieldDivisionPoint n ≠ 0 :=
  Genuine.divSys_ne_zero S.prime.EK n hn

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
