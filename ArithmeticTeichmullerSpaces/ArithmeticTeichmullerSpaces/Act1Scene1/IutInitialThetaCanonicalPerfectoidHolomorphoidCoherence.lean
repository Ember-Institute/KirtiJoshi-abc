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

/-!
The bridge and local holomorphoid descriptions also agree on the induced
nonarchimedean size.  This is the quantitative form of the Teichmuller/sharp
compatibility used by later local period and log-shell consumers.
-/
theorem canonicalPerfectoid_theta_teichmuller_nnnorm_eq_tiltValuation
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaTateParameterData D).places)
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ)
    (x : InitialThetaTiltField.Source D w) :
    ‖(((InitialThetaCanonicalPerfectoidBridgeSource.canonical D w theta thetaBase
      packetHull heightData ramification logVolume processionLength).placeData.data.theta
        (WittVector.teichmuller (Arithmetic.residueChar w.1) x) :
          InitialThetaCanonicalPerfectoidBridgeSource.IntegerRing D w) :
            InitialThetaCanonicalPerfectoidBridgeSource.CoefficientField D w)‖₊ =
      InitialThetaTiltField.valuation D w (InitialThetaTiltField.inclusion D w x) := by
  rw [canonicalPerfectoid_theta_teichmuller_eq_sharp D w theta thetaBase packetHull
    heightData ramification logVolume processionLength x]
  exact InitialThetaLocalHolomorphoidSource.canonical_sharp_norm D w
    (InitialThetaTiltField.inclusion D w x)

/-!
The coefficient map in the canonical bridge is isometric on the completion
image.  This records the norm compatibility needed when a local holomorphoid
consumer changes between integral coefficients and the completed coefficient
field.
-/
theorem canonicalPerfectoid_coefficientMap_norm_eq_completionEmbedding_norm
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaTateParameterData D).places)
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ)
    (a : 𝓞 D.F) :
    ‖(((InitialThetaCanonicalPerfectoidBridgeSource.canonical D w theta thetaBase
      packetHull heightData ramification logVolume processionLength).coefficientMap a :
        InitialThetaCanonicalPerfectoidBridgeSource.IntegerRing D w) :
          InitialThetaCanonicalPerfectoidBridgeSource.CoefficientField D w)‖ =
      ‖InitialThetaCanonicalGeometricFontaine.completionEmbedding D w
        (FinitePlace.embedding w.1.maximalIdeal (a : D.F))‖ := by
  rw [(InitialThetaCanonicalPerfectoidBridgeSource.canonical D w theta thetaBase packetHull
    heightData ramification logVolume processionLength).coefficientMap_eq_bridge]
  rw [InitialThetaCanonicalPerfectoidBridgeSource.Data.bridge_coefficientMap_coe]

/-!
Global integers therefore map into the closed unit ball of the same completed
coefficient field.  The bound is transferred from the finite-place integral
norm, rather than imposed as an independent bridge law.
-/
theorem canonicalPerfectoid_coefficientMap_norm_le_one
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaTateParameterData D).places)
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ)
    (a : 𝓞 D.F) :
    ‖(((InitialThetaCanonicalPerfectoidBridgeSource.canonical D w theta thetaBase
      packetHull heightData ramification logVolume processionLength).coefficientMap a :
        InitialThetaCanonicalPerfectoidBridgeSource.IntegerRing D w) :
          InitialThetaCanonicalPerfectoidBridgeSource.CoefficientField D w)‖ ≤ 1 := by
  rw [canonicalPerfectoid_coefficientMap_norm_eq_completionEmbedding_norm D w theta thetaBase
    packetHull heightData ramification logVolume processionLength a]
  rw [InitialThetaCanonicalGeometricFontaine.completionEmbedding_norm]
  exact FinitePlace.norm_le_one D.F w.1.maximalIdeal a

end
end JoshiTeich.Act1Scene1
