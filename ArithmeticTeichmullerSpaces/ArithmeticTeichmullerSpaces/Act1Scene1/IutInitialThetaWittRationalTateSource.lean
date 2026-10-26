import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithmLinear
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RATIONAL-TATE-SOURCE
source: Joshi II `eq:tate-module-of-lubin-tate` and the actual
T_y tensor Q_p term of the sequence following `pr:teichmuller-lift-A`.
fidelity: forms Q_p tensor over Z_p with the original Tate inverse
limit. Base change of its proved integral basis identifies this actual
tensor product with Q_p. Transfers the standard norm to this new source
and proves the corresponding isometric equivalence and dimension one.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this defines only the rational Tate source.
Its period map and kernel comparisons are separate consumers. The
existing period-ring topology is unchanged. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRationalTateSource

open JoshiTeich.Prologue InitialThetaWittTateLogarithm
open scoped TensorProduct Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev RationalTate := Padic (Arithmetic.residueChar w.1) ⊗[
  PadicInt (Arithmetic.residueChar w.1)] Additive (Tate D w)

def integralBasis : PadicInt (Arithmetic.residueChar w.1) ≃ₗ[
    PadicInt (Arithmetic.residueChar w.1)] Additive (Tate D w) :=
  (LocalKummer.TateBasis.equiv (p := Arithmetic.residueChar w.1)
    (Ω := InitialThetaCanonicalGeometricFontaine.coefficientField D w)).toLinearEquiv

def coefficientEquiv : RationalTate D w ≃ₗ[Padic (Arithmetic.residueChar w.1)]
    Padic (Arithmetic.residueChar w.1) :=
  (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (Padic (Arithmetic.residueChar w.1)) (Padic (Arithmetic.residueChar w.1)))
    (integralBasis D w).symm).trans
      (TensorProduct.AlgebraTensorModule.rid (PadicInt (Arithmetic.residueChar w.1))
        (Padic (Arithmetic.residueChar w.1)) (Padic (Arithmetic.residueChar w.1)))

theorem coefficientEquiv_tmul (a : Padic (Arithmetic.residueChar w.1)) (t : Additive (Tate D w)) :
    coefficientEquiv D w (a ⊗ₜ t) = a * ((integralBasis D w).symm t : Padic (Arithmetic.residueChar w.1)) := by
  simp only [coefficientEquiv, LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, TensorProduct.AlgebraTensorModule.rid_tmul]
  change ((integralBasis D w).symm t : Padic (Arithmetic.residueChar w.1)) * a = _
  exact mul_comm _ _

instance rationalTateNormedAddCommGroup : NormedAddCommGroup (RationalTate D w) :=
  NormedAddCommGroup.induced _ (Padic (Arithmetic.residueChar w.1))
    (coefficientEquiv D w).toLinearMap (coefficientEquiv D w).injective

instance rationalTateNormedSpace : NormedSpace (Padic (Arithmetic.residueChar w.1)) (RationalTate D w) :=
  NormedSpace.induced _ _ (Padic (Arithmetic.residueChar w.1)) (coefficientEquiv D w).toLinearMap

def coefficientIsometryEquiv : RationalTate D w ≃ₗᵢ[Padic (Arithmetic.residueChar w.1)]
    Padic (Arithmetic.residueChar w.1) where
  __ := coefficientEquiv D w
  norm_map' _ := rfl

instance rationalTateFiniteDimensional : FiniteDimensional (Padic (Arithmetic.residueChar w.1))
    (RationalTate D w) :=
  FiniteDimensional.of_injective (coefficientEquiv D w).toLinearMap (coefficientEquiv D w).injective

theorem rationalTate_finrank : Module.finrank (Padic (Arithmetic.residueChar w.1)) (RationalTate D w) = 1 :=
  (coefficientEquiv D w).finrank_eq.trans (Module.finrank_self _)

end
end JoshiTeich.Act1Scene1.InitialThetaWittRationalTateSource
