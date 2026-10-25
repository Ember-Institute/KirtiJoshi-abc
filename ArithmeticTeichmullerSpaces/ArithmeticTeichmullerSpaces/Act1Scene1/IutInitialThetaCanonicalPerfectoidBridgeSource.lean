/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalGeometricFontaine

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-CANONICAL-PERFECTOID-BRIDGE-SOURCE
source: the actual supported finite-place completion, canonical geometric
Fontaine coefficient field, and bridge laws in
`IutInitialThetaCanonicalGeometricFontaine.lean`.
fidelity: packages the local perfectoid place, coefficient map, bridge laws,
place support, theta surjectivity, and Frobenius surjectivity produced from
the same `InitialThetaData` and supported Tate place.
boundary: Scene1/Derived; this is a local actual perfectoid bridge source. It
does not produce the global holomorphoid, cross-place marking, H¹ₑ/BK
comparison, or paper theta-volume identity.
-/

namespace InitialThetaCanonicalPerfectoidBridgeSource

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (theta : ThetaPilotData D.F) (thetaBase : theta.index)
variable (packetHull : PacketHullData theta.index)
variable (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F)
variable (logVolume : ℝ) (processionLength : ℕ)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance selectedPrimeNorm :
    Fact (0 < ‖(Arithmetic.residueChar w.1 :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 :
        InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

abbrev CoefficientField := InitialThetaCanonicalGeometricFontaine.coefficientField D w
abbrev IntegerRing := LocalGeometricFontaine.integerRing (CoefficientField D w)
abbrev Link := AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
  heightData ramification logVolume processionLength
abbrev PlaceData := PerfectoidPlaceData D.F (IntegerRing D w)
  (Arithmetic.residueChar w.1)
structure Data : Type (u + 1) where
  placeData : PlaceData D w
  bridgeData : PerfectoidBridgeData
    (Link D theta thetaBase packetHull heightData ramification logVolume processionLength)
    (Arithmetic.residueChar w.1) placeData
  coefficientMap : 𝓞 D.F →+* IntegerRing D w
  bridgeLaws : PerfectoidBridgeLaws
    (Link D theta thetaBase packetHull heightData ramification logVolume processionLength)
    (Arithmetic.residueChar w.1) placeData bridgeData
  coefficientMap_injective : Function.Injective coefficientMap
  place_eq : placeData.place = w.1
  theta_surjective : Function.Surjective placeData.data.theta
  frobenius_surjective : Function.Surjective (frobenius
    (ModP (IntegerRing D w) (Arithmetic.residueChar w.1))
    (Arithmetic.residueChar w.1))

noncomputable def canonical : Data D w theta thetaBase packetHull heightData ramification
    logVolume processionLength where
  placeData := InitialThetaCanonicalGeometricFontaine.placeData D w
  bridgeData := InitialThetaCanonicalGeometricFontaine.bridgeData D w theta thetaBase
    packetHull heightData ramification logVolume processionLength
  coefficientMap := InitialThetaCanonicalGeometricFontaine.coefficientMap D w
  bridgeLaws := InitialThetaCanonicalGeometricFontaine.bridgeData_laws D w theta thetaBase
    packetHull heightData ramification logVolume processionLength
  coefficientMap_injective := InitialThetaCanonicalGeometricFontaine.coefficientMap_injective D w
  place_eq := InitialThetaCanonicalGeometricFontaine.placeData_place D w
  theta_surjective := InitialThetaCanonicalGeometricFontaine.theta_surjective D w
  frobenius_surjective := InitialThetaCanonicalGeometricFontaine.frobenius_surjective D w

theorem canonical_place_eq :
    ((canonical D w theta thetaBase packetHull heightData ramification logVolume processionLength).placeData).place = w.1 :=
  (canonical D w theta thetaBase packetHull heightData ramification logVolume processionLength).place_eq

theorem canonical_bridge_place_supported :
    w.1 ∈ (Link D theta thetaBase packetHull heightData ramification logVolume processionLength).places :=
  (canonical D w theta thetaBase packetHull heightData ramification logVolume processionLength).bridgeLaws.place_supported

theorem canonical_coefficientMap_injective :
    Function.Injective
      (canonical D w theta thetaBase packetHull heightData ramification logVolume processionLength).coefficientMap :=
  (canonical D w theta thetaBase packetHull heightData ramification logVolume processionLength).coefficientMap_injective

theorem canonical_theta_surjective :
    Function.Surjective
      (canonical D w theta thetaBase packetHull heightData ramification logVolume processionLength).placeData.data.theta :=
  (canonical D w theta thetaBase packetHull heightData ramification logVolume processionLength).theta_surjective

theorem canonical_frobenius_surjective_for
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ) :
    Function.Surjective (frobenius
      (ModP (IntegerRing D w) (Arithmetic.residueChar w.1))
      (Arithmetic.residueChar w.1)) :=
  (canonical D w theta thetaBase packetHull heightData ramification logVolume processionLength).frobenius_surjective

end InitialThetaCanonicalPerfectoidBridgeSource

end
end JoshiTeich.Act1Scene1
