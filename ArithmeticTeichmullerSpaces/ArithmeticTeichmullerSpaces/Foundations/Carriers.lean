import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Basic.Real.Basic

namespace JoshiTeich

/-!
The data layer for Act1. These structures contain the objects that later
contracts must be able to inspect. Mathematical properties are kept in
`AST₀` and in the contract structures, rather than hidden in existential
propositions.
-/

structure PlaceData (K : Type*) where
  label : ℕ
  residueDegree : ℕ
  valuation : K → ℤ

structure UntiltData (K : Type*) where
  carrier : Type*
  map : K → carrier
  frobenius : carrier → carrier

structure ThetaData (K : Type*) where
  qParameter : K
  thetaValue : ℕ → K
  thetaPilot : Finset ℕ

structure PacketData (K : Type*) where
  packetIndex : Finset ℕ
  coordinate : ℕ → K
  hullRegion : Finset ℕ
  logVolume : ℝ

structure ASTData where
  K : Type*
  fieldStructure : Field K
  ossPlaces : Finset ℕ
  place : ℕ → PlaceData K
  untilt : UntiltData K
  theta : ThetaData K
  packet : PacketData K
  height : K → ℝ
  norm : K → ℝ
  qNorm : ℕ → ℝ
  ell : ℕ
  ellStar : ℕ

end JoshiTeich
