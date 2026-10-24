import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullData
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalGeometricFontaine

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-GEOMETRIC-FONTAINE
source: the actual supported Tate place, the geometric Fontaine completion,
and the ordinary-log actual-hull cost producer.
fidelity: specializes `CanonicalActualHull.AnalyticInput` so its local
perfectoid place, coefficient map, and bridge laws come from the same actual
`InitialThetaData`; theta scaling, period, normalization, and theta-log laws
remain explicit analytic inputs.
boundary: Scene1/Derived. This does not construct the global holomorphoid,
H¹ₑ/BK comparison, or paper theta-volume identity.
-/

namespace JoshiTeich.Act1Scene1.CanonicalActualHull

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (n : ℕ)
variable (σ : iutInitialThetaVBadModuliFinset D → Fin n →
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)
variable (theta : ThetaPilotData D.F)
variable (route : ActualHullCostTransfer.PositivePacket D n σ hσ
  (VBadThetaLogCollation.collation D n σ hσ) → theta.index)
variable (thetaBase : theta.index) (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F)

noncomputable def AnalyticInput.ofCanonicalGeometricFontaine
    (w : (iutInitialThetaTateParameterData D).places)
    (thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase)
    (periodMap : ∀ i, theta.period i = theta.liftedLog i)
    (normalization : letI := theta.indexFintype
      ActualHullCostTransfer.cost D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ) = ∑ i, theta.period i)
    (theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i)) :
    AnalyticInput (O := LocalGeometricFontaine.integerRing
      (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
      (Arithmetic.residueChar w.1) D theta route thetaBase heightData ramification := by
  letI : Fact (Arithmetic.residueChar w.1).Prime :=
    ⟨Arithmetic.residueChar_prime w.1⟩
  letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  refine
    { placeData := InitialThetaCanonicalGeometricFontaine.placeData D w
      bridge := InitialThetaCanonicalGeometricFontaine.bridgeData D w theta thetaBase
        (packetHull D n σ hσ (VBadThetaLogCollation.collation D n σ hσ) theta route)
        heightData ramification
        (ActualHullCostTransfer.cost D n σ hσ
          (VBadThetaLogCollation.collation D n σ hσ)) n
      thetaScaling := thetaScaling
      periodMap := periodMap
      normalization := normalization
      perfectoidBridge := ?_
      theta_log_shell := theta_log_shell }
  exact InitialThetaCanonicalGeometricFontaine.bridgeData_laws D w theta thetaBase
    (packetHull D n σ hσ (VBadThetaLogCollation.collation D n σ hσ) theta route)
    heightData ramification
    (ActualHullCostTransfer.cost D n σ hσ
      (VBadThetaLogCollation.collation D n σ hσ)) n

theorem AnalyticInput.ofCanonicalGeometricFontaine_place_eq
    (w : (iutInitialThetaTateParameterData D).places)
    (thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase)
    (periodMap : ∀ i, theta.period i = theta.liftedLog i)
    (normalization : letI := theta.indexFintype
      ActualHullCostTransfer.cost D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ) = ∑ i, theta.period i)
    (theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i)) :
    let X := AnalyticInput.ofCanonicalGeometricFontaine D n σ hσ theta route thetaBase
      heightData ramification w thetaScaling periodMap normalization theta_log_shell
    (X.placeData).place = w.1 := by
  letI : Fact (Arithmetic.residueChar w.1).Prime :=
    ⟨Arithmetic.residueChar_prime w.1⟩
  letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rfl

theorem corollary312_ofCanonicalGeometricFontaine
    (w : (iutInitialThetaTateParameterData D).places)
    (thetaScaling : Theta.ThetaPilotScalingLaws theta thetaBase)
    (periodMap : ∀ i, theta.period i = theta.liftedLog i)
    (normalization : letI := theta.indexFintype
      ActualHullCostTransfer.cost D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ) = ∑ i, theta.period i)
    (theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i)) :
    Corollary312 (Arithmetic.residueChar w.1)
      (data (O := LocalGeometricFontaine.integerRing
        (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
        (Arithmetic.residueChar w.1) D theta route thetaBase heightData ramification
        (AnalyticInput.ofCanonicalGeometricFontaine D n σ hσ theta route thetaBase
          heightData ramification w thetaScaling periodMap normalization theta_log_shell)) := by
  letI : Fact (Arithmetic.residueChar w.1).Prime :=
    ⟨Arithmetic.residueChar_prime w.1⟩
  letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact corollary312 (p := Arithmetic.residueChar w.1) (D := D) (theta := theta)
    (route := route) (thetaBase := thetaBase) (heightData := heightData)
    (ramification := ramification)
    (X := AnalyticInput.ofCanonicalGeometricFontaine D n σ hσ theta route thetaBase
      heightData ramification w thetaScaling periodMap normalization theta_log_shell)

end
end JoshiTeich.Act1Scene1.CanonicalActualHull
