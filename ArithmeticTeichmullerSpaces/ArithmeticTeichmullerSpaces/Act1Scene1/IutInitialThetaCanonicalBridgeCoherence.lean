import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullGeometricFontaine

/-!
source-id: JT-SCENE1-INITIAL-THETA-CANONICAL-BRIDGE-COHERENCE
source: Joshi I \`def:geom-base-points\`, \`lem:perfectoid\`, and the actual
canonical geometric Fontaine bridge already constructed from one
\`InitialThetaData\` and supported Tate place.
fidelity: packages the local bridge's place identity, supportedness,
coefficient-map injectivity, theta surjectivity, and residue-Frobenius
surjectivity into one auditable coherence proposition.
boundary: Scene1/Derived; this remains a local bridge result. It does not
construct global holomorphoid marking, cross-place collation, H¹ₑ/BK data,
or paper theta-volume identities.
-/

namespace JoshiTeich.Act1Scene1.CanonicalActualHull.BridgeCoherence

open JoshiTeich.Prologue
open NumberField
open scoped Topology
universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (theta : ThetaPilotData D.F)
variable (route : PositivePacket D → theta.index)
variable (thetaBase : theta.index)
variable (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase)
variable (periodMap : ∀ i, theta.period i = theta.liftedLog i)
variable (normalization : letI := theta.indexFintype
  cost D = ∑ i, theta.period i)
variable (theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i))

local instance coherencePrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance coherencePrimeNorm :
    Fact (0 < ‖(Arithmetic.residueChar w.1 :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 :
        InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w
local instance coherencePrimeNonunit :
    Fact (¬ IsUnit (Arithmetic.residueChar w.1 :
      LocalGeometricFontaine.integerRing
        (InitialThetaCanonicalGeometricFontaine.coefficientField D w))) :=
  LocalGeometricFontaine.primeNonunitFact
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w)
    (Arithmetic.residueChar w.1)

abbrev CanonicalInput
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F)
    (route : PositivePacket D → theta.index)
    (thetaBase : theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (w : (iutInitialThetaTateParameterData D).places) :=
  CanonicalActualHull.AnalyticInput (O := LocalGeometricFontaine.integerRing
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (Arithmetic.residueChar w.1) D theta route thetaBase heightData ramification

structure Data (X : CanonicalInput D theta route thetaBase heightData ramification w) : Prop where
  place_eq : X.placeData.place = w.1
  place_supported : X.placeData.place ∈
    (CanonicalActualHull.link D theta route thetaBase heightData ramification).places
  coefficientMap_injective : Function.Injective X.bridge.coefficientMap
  theta_surjective : Function.Surjective X.placeData.data.theta
  frobenius_surjective : Function.Surjective (frobenius
    (ModP (LocalGeometricFontaine.integerRing
      (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
      (Arithmetic.residueChar w.1)) (Arithmetic.residueChar w.1))

theorem ofCanonicalGeometricFontaine :
    Data D theta route thetaBase heightData ramification w
      (CanonicalActualHull.AnalyticInput.ofCanonicalGeometricFontaine D theta route
        thetaBase heightData ramification w thetaScaling periodMap normalization theta_log_shell) := by
  letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  refine
    { place_eq := ?_
      place_supported := ?_
      coefficientMap_injective := ?_
      theta_surjective := ?_
      frobenius_surjective := ?_ }
  · exact CanonicalActualHull.AnalyticInput.ofCanonicalGeometricFontaine_place_eq D theta
      route thetaBase heightData ramification w thetaScaling periodMap normalization theta_log_shell
  · exact CanonicalActualHull.AnalyticInput.ofCanonicalGeometricFontaine_place_supported D theta
      route thetaBase heightData ramification w thetaScaling periodMap normalization theta_log_shell
  · change Function.Injective (InitialThetaCanonicalGeometricFontaine.coefficientMap D w)
    exact InitialThetaCanonicalGeometricFontaine.coefficientMap_injective D w
  · change Function.Surjective (InitialThetaCanonicalGeometricFontaine.placeData D w).data.theta
    exact InitialThetaCanonicalGeometricFontaine.theta_surjective D w
  · change Function.Surjective (frobenius
      (ModP (LocalGeometricFontaine.integerRing
        (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
        (Arithmetic.residueChar w.1)) (Arithmetic.residueChar w.1))
    exact InitialThetaCanonicalGeometricFontaine.frobenius_surjective D w

end
end JoshiTeich.Act1Scene1.CanonicalActualHull.BridgeCoherence
