import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetTateLogEigenHom
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRationalTatePeriod
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRationalTateSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPrincipalRationalLift

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-TATE-LOG-EIGEN-HOM-RANGE
source: Joshi II `se:ff-rings`, `eq:tate-module-of-lubin-tate`, and
`pr:teichmuller-lift-A/B`.
fidelity: identifies each value of the transported integral Tate-log eigen
hom with the Frechet rational Tate period map at the pure tensor `1 ⊗ₜ t`.
Consequently the integral Tate-log image lies in the Frechet Tate line.
boundary: Scene1/Derived; this actual completion inclusion does not identify
paper `B`, define rho norms, or provide H1e/BK, holomorphoid, or paper volume
identities.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetTateLogEigenHomRange

open JoshiTeich.Prologue
open InitialThetaWittAdditiveTatePeriod InitialThetaWittFrechetTateKernel
open InitialThetaWittFrechetTateLogEigenHom
open InitialThetaWittTateLogarithm
open InitialThetaWittFrechetPrincipalRationalLift
open InitialThetaWittRationalTatePeriod InitialThetaWittRationalTateSource
open scoped TensorProduct Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Tate := InitialThetaWittFrechetTateLogProducer.Tate D w

theorem frechetTateLogEigenHom_eq_frechetEigenPeriodMap_tmul
    (t : Additive (Tate D w)) :
    frechetTateLogEigenHom D w t =
      frechetEigenPeriodMap D w (1 ⊗ₜ t) := by
  apply frechetToActualEigen_injective D w
  rw [frechetToActualEigen_frechetTateLogEigenHom,
    frechetToActualEigen_frechetEigenPeriodMap]
  apply Subtype.ext
  change tateLogHom D w t = periodMap D w (1 ⊗ₜ t)
  rw [periodMap_tmul]
  change tateLog D w t.toMul = _
  simp only [one_smul]

theorem frechetTateLogEigenHom_mem_tateLine (t : Additive (Tate D w)) :
    frechetTateLogEigenHom D w t ∈ frechetTateLine D w := by
  rw [frechetTateLogEigenHom_eq_frechetEigenPeriodMap_tmul D w t]
  exact ⟨1 ⊗ₜ t, rfl⟩

theorem frechetTateLogEigenHom_range_le_tateLine :
    Set.range (frechetTateLogEigenHom D w) ⊆
      (frechetTateLine D w : Set (InitialThetaWittFrechetTateKernel.frechetFrobeniusPrime D w)) := by
  rintro _ ⟨t, rfl⟩
  exact frechetTateLogEigenHom_mem_tateLine D w t

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetTateLogEigenHomRange
