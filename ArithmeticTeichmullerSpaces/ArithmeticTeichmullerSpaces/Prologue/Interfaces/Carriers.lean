import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import ArithmeticTeichmullerSpaces.Prologue.Arithmetic.Basic
import ArithmeticTeichmullerSpaces.Prologue.Theta.Tate

namespace JoshiTeich.Prologue

universe uK

/-!
The Prologue data layer.  These structures contain data that downstream
consumers may compute with.  Mathematical relations are kept in `Contracts`.

The finite-place type is mathlib's `NumberField.FinitePlace`, so a place is an
actual absolute value attached to a height-one prime of the ring of integers.
-/

structure ThetaPilotData (K : Type uK) [Field K] where
  index : Type uK
  indexFintype : Fintype index
  value : index → K
  norm : index → ℝ
  scalingIndex : index → ℕ
  frobenius : index → index
  period : index → ℝ
  liftedLog : index → ℝ

structure PacketHullData (Pilot : Type uK) where
  packet : Type uK
  packetFintype : Fintype packet
  packetToPilot : packet → Pilot
  packetWeight : packet → ℝ
  hull : Type uK
  hullFintype : Fintype hull
  hullToPacket : hull → packet
  hullWeight : hull → ℝ

structure AdelicThetaLinkData (K : Type uK) [Field K] [NumberField K] where
  places : Finset (NumberField.FinitePlace K)
  qParameter : K
  tate : Theta.TateParameterData K
  theta : ThetaPilotData K
  thetaBase : theta.index
  packetHull : PacketHullData theta.index
  heightData : Arithmetic.HeightData K
  ramification : Arithmetic.RamificationProfile K
  logVolume : ℝ
  processionLength : ℕ

namespace AdelicThetaLinkData

variable {K : Type*} [Field K] [NumberField K]

def qNorm (D : AdelicThetaLinkData K)
    (w : NumberField.FinitePlace K) : ℝ :=
  w D.qParameter

def height (D : AdelicThetaLinkData K) : K → ℝ :=
  D.heightData.value

def placeNorm (D : AdelicThetaLinkData K)
    (w : NumberField.FinitePlace K) : ℝ :=
  D.qNorm w

def thetaIndices (D : AdelicThetaLinkData K) : Finset D.theta.index := by
  letI := D.theta.indexFintype
  exact Finset.univ

def packetIndices (D : AdelicThetaLinkData K) : Finset D.packetHull.packet := by
  letI := D.packetHull.packetFintype
  exact Finset.univ

def hullIndices (D : AdelicThetaLinkData K) : Finset D.packetHull.hull := by
  letI := D.packetHull.hullFintype
  exact Finset.univ

end AdelicThetaLinkData

end JoshiTeich.Prologue
