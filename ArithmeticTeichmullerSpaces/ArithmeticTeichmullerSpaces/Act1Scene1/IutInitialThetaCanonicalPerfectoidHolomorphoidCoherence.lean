import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalPerfectoidBridgeSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLocalHolomorphoidSource

/-!
source-id: JT-SCENE1-CANONICAL-PERFECTOID-HOLOMORPHOID-COHERENCE
source: Joshi I, Definition 3.1(e)--(f), Definition 2.5; the canonical local
Fontaine theta and sharp maps from the same InitialThetaData supported place.
fidelity: identifies the theta map in the actual local perfectoid bridge with
the theta map in the local holomorphoid source and transports its
Teichmuller/sharp identity. This does not supply a global holomorphoid marking.
boundary: Scene1/Derived; original proof.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

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

theorem canonicalPerfectoid_theta_eq_localHolomorphoid_theta
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaTateParameterData D).places)
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ) :
    InitialThetaLocalHolomorphoidSource.theta D w =
      (InitialThetaCanonicalPerfectoidBridgeSource.canonical D w theta thetaBase
        packetHull heightData ramification logVolume processionLength).placeData.data.theta := by
  rfl

theorem canonicalPerfectoid_theta_teichmuller_eq_sharp
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaTateParameterData D).places)
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ)
    (x : InitialThetaTiltField.Source D w) :
    (((InitialThetaCanonicalPerfectoidBridgeSource.canonical D w theta thetaBase
      packetHull heightData ramification logVolume processionLength).placeData.data.theta
        (WittVector.teichmuller (Arithmetic.residueChar w.1) x) :
          InitialThetaCanonicalPerfectoidBridgeSource.IntegerRing D w) :
            InitialThetaCanonicalPerfectoidBridgeSource.CoefficientField D w) =
      InitialThetaLocalHolomorphoidSource.sharp D w
        (InitialThetaTiltField.inclusion D w x) := by
  rw [← canonicalPerfectoid_theta_eq_localHolomorphoid_theta D w theta thetaBase
    packetHull heightData ramification logVolume processionLength]
  exact InitialThetaLocalHolomorphoidSource.canonical_theta_teichmuller D w x

end
end JoshiTeich.Act1Scene1
