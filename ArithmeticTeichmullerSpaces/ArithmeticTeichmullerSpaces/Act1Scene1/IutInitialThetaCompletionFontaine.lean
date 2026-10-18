import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAdicFontaine
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLinkSource

/-!
source-id: JT-SCENE1-INITIAL-THETA-COMPLETION-FONTAINE
source: actual InitialThetaData Tate support and its canonical completion
embedding; Prologue PerfectoidPlaceData and PerfectoidBridgeLaws.
fidelity: uses every supported actual base-field place and its completion
integer ring to supply the existing algebraic bridge fields and laws.
The prime, coefficient map, ring and place are actual producers. Remaining
theta/period input and the holomorphoid perfectoid/untilt identity stay open.
Original consumer proofs; no reference source code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaCompletionFontaine

open JoshiTeich.Prologue NumberField
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def placeData : PerfectoidPlaceData D.F (LocalCompletion.integerRing w.1)
    (Arithmetic.residueChar w.1) := LocalCompletion.completionPlaceData w.1

theorem placeData_place : (placeData D w).place = w.1 := rfl

theorem placeData_laws : PerfectoidPlaceLaws (Arithmetic.residueChar w.1) (placeData D w) :=
  LocalCompletion.completionPlaceData_laws w.1

variable (theta : ThetaPilotData D.F) (thetaBase : theta.index)
variable (packetHull : PacketHullData theta.index) (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F) (logVolume : ℝ) (processionLength : ℕ)

/-- Same link, same actual supported place, and its actual completion integer ring. -/
def bridgeData : PerfectoidBridgeData
    (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull heightData
      ramification logVolume processionLength) (Arithmetic.residueChar w.1) (placeData D w) :=
  LocalCompletion.completionBridgeData w.1 _

theorem bridgeData_laws : PerfectoidBridgeLaws
    (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull heightData
      ramification logVolume processionLength) (Arithmetic.residueChar w.1) (placeData D w)
        (bridgeData D w theta thetaBase packetHull heightData ramification logVolume processionLength) :=
  LocalCompletion.completionBridgeData_laws w.1 _ w.2

theorem bridgeData_coefficientMap (a : 𝓞 D.F) :
    ((bridgeData D w theta thetaBase packetHull heightData ramification logVolume processionLength).coefficientMap a :
      LocalCompletion.completionAt D.F w.1) = FinitePlace.embedding w.1.maximalIdeal (a : D.F) := rfl

theorem bridgeData_coefficientMap_injective : Function.Injective
    (bridgeData D w theta thetaBase packetHull heightData ramification logVolume processionLength).coefficientMap :=
  LocalCompletion.integerCoefficientMap_injective w.1

end
end JoshiTeich.Act1Scene1.InitialThetaCompletionFontaine
