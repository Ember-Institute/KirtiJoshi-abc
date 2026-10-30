import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLogarithmMultiplication
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLogarithmSeries
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialSeries
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithmBounded
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAdditiveTatePeriod

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-TATE-LOG-PRODUCER
source: Joshi II `se:ff-rings`, `eq:tate-module-of-lubin-tate` and
`pr:teichmuller-lift-A/B`, the all-radius logarithmic domain of the
multiplicative Tate tower.
fidelity: packages the proved actual all-radius condition
`InDomain x := ∀ρ, ‖x‖ρ < 1` as a Frechet-domain carrier. The formal-group
product `x ⊙ y = x + y + x*y` stays in this domain, its convergent
logarithms add, and actual Tate coordinates provide domain elements whose
logs have the proved HasSum and `φ=p` properties. The existing uniform
radius bounds are exposed as a family for this producer.
boundary: Scene1/Derived; this is an actual completion producer for the
Tate-log convergence domain. It does not identify the carrier with paper
`B`, supply a paper rho norm, or prove H¹ₑ/BK or global holomorphoid laws.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetTateLogProducer

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittTateLogarithm
open InitialThetaWittAdditiveTatePeriod InitialThetaWittLogarithmMultiplication
open InitialThetaWittLogarithmSeries InitialThetaWittExponentialSeries
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Carrier := InitialThetaWittAllRadiusCompletion.Carrier D w
abbrev Tate := InitialThetaWittTateLogarithm.Tate D w

def Domain := {x : Carrier D w // InDomain D w x}

instance domainInhabited : Inhabited (Domain D w) :=
  ⟨⟨0, by intro ρ; simpa only [map_zero, norm_zero] using zero_lt_one⟩⟩

def domainProduct (x y : Domain D w) : Domain D w :=
  ⟨x.1 + y.1 + x.1 * y.1,
    inDomain_mul_coordinate D w x.1 y.1 x.2 y.2⟩

theorem domainProduct_value (x y : Domain D w) :
    (domainProduct D w x y).1 = x.1 + y.1 + x.1 * y.1 := rfl

def logOnDomain (x : Domain D w) : Carrier D w := logOneAdd D w x.1

theorem logOnDomain_hasSum (x : Domain D w) :
    HasSum (logTerm D w x.1) (logOnDomain D w x) :=
  hasSum_logOneAdd D w x.1 x.2

theorem logOnDomain_domainProduct (x y : Domain D w) :
    logOnDomain D w (domainProduct D w x y) =
      logOnDomain D w x + logOnDomain D w y := by
  change logOneAdd D w (x.1 + y.1 + x.1 * y.1) = _
  exact logOneAdd_mul_coordinate D w x.1 y.1 x.2 y.2

def tateInput (t : Tate D w) : Domain D w :=
  ⟨coordinate D w t, by
    intro ρ
    exact coordinate_lt_one D w t ρ⟩

theorem tateInput_value (t : Tate D w) :
    (tateInput D w t).1 = coordinate D w t := rfl

theorem tateInput_hasSum (t : Tate D w) :
    HasSum (logTerm D w (tateInput D w t).1)
      (logOnDomain D w (tateInput D w t)) :=
  logOnDomain_hasSum D w (tateInput D w t)

theorem tateInput_log_eq_tateLog (t : Tate D w) :
    logOnDomain D w (tateInput D w t) = tateLog D w t := by
  change logOneAdd D w (coordinate D w t) = tateLog D w t
  rfl

theorem tateInput_log_mem_frobeniusPrime (t : Tate D w) :
    logOnDomain D w (tateInput D w t) ∈ frobeniusPrimeSubmodule D w := by
  rw [tateInput_log_eq_tateLog]
  exact tateLog_mem_frobeniusPrime D w t

theorem exists_uniform_tateLog_bound_all :
    ∀ ρ : InitialThetaWittRhoCompletion.Radius, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : Tate D w,
        ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ
          (logOnDomain D w (tateInput D w t))‖ ≤ C := by
  intro ρ
  simpa only [tateInput_log_eq_tateLog] using
    (InitialThetaWittTateLogarithmBounded.exists_uniform_tateLog_bound D w ρ)

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetTateLogProducer
