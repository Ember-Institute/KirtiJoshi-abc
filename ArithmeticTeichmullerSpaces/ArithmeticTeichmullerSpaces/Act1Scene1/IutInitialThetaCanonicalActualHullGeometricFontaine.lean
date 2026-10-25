import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullData
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalGeometricFontaine

namespace JoshiTeich.Act1Scene1.CanonicalActualHull

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

local instance selectedPrime
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaTateParameterData D).places) :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

local instance selectedPrimeNorm
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaTateParameterData D).places) :
    Fact (0 < ‖(Arithmetic.residueChar w.1 :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 :
        InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

local instance selectedPrimeNonunit
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaTateParameterData D).places) :
    Fact (¬ IsUnit (Arithmetic.residueChar w.1 :
      LocalGeometricFontaine.integerRing
        (InitialThetaCanonicalGeometricFontaine.coefficientField D w))) :=
  LocalGeometricFontaine.primeNonunitFact
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w)
    (Arithmetic.residueChar w.1)

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-GEOMETRIC-FONTAINE
source: the actual supported Tate place, the geometric Fontaine completion,
and the ordinary-log actual-hull cost producer.
fidelity: specializes CanonicalActualHull.AnalyticInput so its local
perfectoid place, coefficient map, and bridge laws come from the same actual
InitialThetaData. Theta scaling, period, normalization, and theta-log laws
remain explicit analytic inputs.
boundary: Scene1/Derived. This does not construct the global holomorphoid,
H1_e/BK comparison, or paper theta-volume identity.
-/

namespace AnalyticInput

local instance selectedPrime
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaTateParameterData D).places) :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

local instance selectedPrimeNorm
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaTateParameterData D).places) :
    Fact (0 < ‖(Arithmetic.residueChar w.1 :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 :
        InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

local instance selectedPrimeNonunit
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaTateParameterData D).places) :
    Fact (¬ IsUnit (Arithmetic.residueChar w.1 :
      LocalGeometricFontaine.integerRing
        (InitialThetaCanonicalGeometricFontaine.coefficientField D w))) :=
  LocalGeometricFontaine.primeNonunitFact
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w)
    (Arithmetic.residueChar w.1)

noncomputable def ofCanonicalGeometricFontaine
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F)
    (route : PositivePacket D → theta.index)
    (thetaBase : theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (w : (iutInitialThetaTateParameterData D).places)
    (thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase)
    (periodMap : ∀ i, theta.period i = theta.liftedLog i)
    (normalization : letI := theta.indexFintype
      cost D = ∑ i, theta.period i)
    (theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i)) :
    AnalyticInput (O := LocalGeometricFontaine.integerRing
      (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
      (Arithmetic.residueChar w.1) D theta route thetaBase heightData ramification := by
  letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  refine
    { placeData := InitialThetaCanonicalGeometricFontaine.placeData D w
      bridge := InitialThetaCanonicalGeometricFontaine.bridgeData D w theta thetaBase
        (packetHull D theta route) heightData ramification (cost D) (length D)
      thetaScaling := thetaScaling
      periodMap := periodMap
      normalization := normalization
      perfectoidBridge := InitialThetaCanonicalGeometricFontaine.bridgeData_laws D w
        theta thetaBase (packetHull D theta route) heightData ramification
        (cost D) (length D)
      theta_log_shell := theta_log_shell }

theorem ofCanonicalGeometricFontaine_place_eq
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F)
    (route : PositivePacket D → theta.index)
    (thetaBase : theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (w : (iutInitialThetaTateParameterData D).places)
    (thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase)
    (periodMap : ∀ i, theta.period i = theta.liftedLog i)
    (normalization : letI := theta.indexFintype
      cost D = ∑ i, theta.period i)
    (theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i)) :
    let X := ofCanonicalGeometricFontaine D theta route thetaBase heightData ramification
      w thetaScaling periodMap normalization theta_log_shell
    (X.placeData).place = w.1 := by
  letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rfl

theorem ofCanonicalGeometricFontaine_bridge_coefficientMap
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F)
    (route : PositivePacket D → theta.index)
    (thetaBase : theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (w : (iutInitialThetaTateParameterData D).places)
    (thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase)
    (periodMap : ∀ i, theta.period i = theta.liftedLog i)
    (normalization : letI := theta.indexFintype
      cost D = ∑ i, theta.period i)
    (theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i))
    (a : 𝓞 D.F) :
    let X := ofCanonicalGeometricFontaine D theta route thetaBase heightData ramification
      w thetaScaling periodMap normalization theta_log_shell
    ((X.bridge.coefficientMap a :
      LocalGeometricFontaine.integerRing
        (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) :
        InitialThetaCanonicalGeometricFontaine.coefficientField D w) =
      InitialThetaCanonicalGeometricFontaine.completionEmbedding D w
        (FinitePlace.embedding w.1.maximalIdeal (a : D.F)) := by
  letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact InitialThetaCanonicalGeometricFontaine.bridgeData_coefficientMap D w theta thetaBase
    (packetHull D theta route) heightData ramification (cost D) (length D) a

theorem ofCanonicalGeometricFontaine_place_supported
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F)
    (route : PositivePacket D → theta.index)
    (thetaBase : theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (w : (iutInitialThetaTateParameterData D).places)
    (thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase)
    (periodMap : ∀ i, theta.period i = theta.liftedLog i)
    (normalization : letI := theta.indexFintype
      cost D = ∑ i, theta.period i)
    (theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i)) :
    let X := ofCanonicalGeometricFontaine D theta route thetaBase heightData ramification
      w thetaScaling periodMap normalization theta_log_shell
    (X.placeData).place ∈
      (link D theta route thetaBase heightData ramification).places := by
  letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (ofCanonicalGeometricFontaine D theta route thetaBase heightData ramification
    w thetaScaling periodMap normalization theta_log_shell).perfectoidBridge.place_supported

end AnalyticInput

theorem corollary312_ofCanonicalGeometricFontaine
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F)
    (route : PositivePacket D → theta.index)
    (thetaBase : theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (w : (iutInitialThetaTateParameterData D).places)
    (thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase)
    (periodMap : ∀ i, theta.period i = theta.liftedLog i)
    (normalization : letI := theta.indexFintype
      cost D = ∑ i, theta.period i)
    (theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i)) :
    Corollary312 (Arithmetic.residueChar w.1)
      (data (O := LocalGeometricFontaine.integerRing
        (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
        (Arithmetic.residueChar w.1) D theta route thetaBase heightData ramification
        (AnalyticInput.ofCanonicalGeometricFontaine D theta route thetaBase heightData
          ramification w thetaScaling periodMap normalization theta_log_shell)) := by
  exact corollary312 (p := Arithmetic.residueChar w.1) (D := D) (theta := theta)
    (route := route) (thetaBase := thetaBase) (heightData := heightData)
    (ramification := ramification)
    (X := AnalyticInput.ofCanonicalGeometricFontaine D theta route thetaBase heightData
      ramification w thetaScaling periodMap normalization theta_log_shell)

end
end JoshiTeich.Act1Scene1.CanonicalActualHull
