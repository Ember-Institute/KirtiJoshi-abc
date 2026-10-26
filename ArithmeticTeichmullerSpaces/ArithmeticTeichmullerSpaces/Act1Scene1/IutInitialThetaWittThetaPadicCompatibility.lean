import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaQuotientTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionPadicAlgebra

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-THETA-PADIC-COMPATIBILITY
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, the
Q_p-linear evaluation from the period algebra to its original untilt.
fidelity: constructs the untilt scalar map through the original local
number-field completion and its original geometric embedding. Density
of rational numbers and proved continuity identify this independent map
with evaluation of the existing period scalars. The same evaluation is
therefore a continuous Q_p-linear algebra map for the original actions.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the original untilt norm is retained. No
isometric Q_p scalar norm, arbitrary untilt or period/BK identity is
assumed. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittThetaPadicCompatibility

open JoshiTeich.Prologue InitialThetaWittThetaBound InitialThetaWittThetaEvaluation
open InitialThetaWittAllRadiusPadicScalars
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def untiltPadicMap : Padic (Arithmetic.residueChar w.1) →+* Untilt D w :=
  (InitialThetaCanonicalGeometricFontaine.completionEmbedding D w).comp
    (LocalCompletion.padicEmb (w := w.1) (p := Arithmetic.residueChar w.1) rfl)

theorem untiltPadicMap_continuous : Continuous (untiltPadicMap D w) :=
  (InitialThetaCanonicalGeometricFontaine.completionEmbedding_isometry D w).continuous.comp
    (LocalCompletion.continuous_padicEmb rfl)

theorem untiltPadicMap_injective : Function.Injective (untiltPadicMap D w) :=
  (untiltPadicMap D w).injective

theorem untiltPadicMap_rational (q : ℚ) :
    untiltPadicMap D w (algebraMap ℚ (Padic (Arithmetic.residueChar w.1)) q) =
      algebraMap ℚ (Untilt D w) q :=
  RingHom.map_rat_algebraMap (untiltPadicMap D w) q

theorem evaluation_commonPadicMap (a : Padic (Arithmetic.residueChar w.1)) :
    evaluation D w (commonPadicMap D w a) = untiltPadicMap D w a := by
  have h := (Padic.denseRange_ratCast (Arithmetic.residueChar w.1)).equalizer
    ((evaluation_continuous D w).comp (InitialThetaWittPadicScalarContinuity.commonPadicMap_continuous D w))
    (untiltPadicMap_continuous D w) (by
      funext q
      change evaluation D w (commonPadicMap D w (algebraMap ℚ (Padic (Arithmetic.residueChar w.1)) q)) =
        untiltPadicMap D w (algebraMap ℚ (Padic (Arithmetic.residueChar w.1)) q)
      rw [commonPadicMap_rational, untiltPadicMap_rational]
      exact RingHom.map_rat_algebraMap (evaluation D w) q)
  exact congrFun h a

instance untiltPadicAlgebra : Algebra (Padic (Arithmetic.residueChar w.1)) (Untilt D w) :=
  (untiltPadicMap D w).toAlgebra

instance untiltContinuousSMul : ContinuousSMul (Padic (Arithmetic.residueChar w.1)) (Untilt D w) :=
  continuousSMul_of_algebraMap _ _ (untiltPadicMap_continuous D w)

def evaluationAlgHom : InitialThetaWittAllRadiusCompletion.Carrier D w →ₐ[
    Padic (Arithmetic.residueChar w.1)] Untilt D w where
  __ := evaluation D w
  commutes' := evaluation_commonPadicMap D w

theorem evaluation_smul (a : Padic (Arithmetic.residueChar w.1))
    (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    evaluation D w (a • x) = a • evaluation D w x := map_smul (evaluationAlgHom D w) a x

def evaluationContinuousLinear : InitialThetaWittAllRadiusCompletion.Carrier D w →L[
    Padic (Arithmetic.residueChar w.1)] Untilt D w where
  __ := (evaluationAlgHom D w).toLinearMap
  cont := evaluation_continuous D w

theorem evaluationContinuousLinear_apply (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    evaluationContinuousLinear D w x = evaluation D w x := rfl

theorem evaluationContinuousLinear_surjective : Function.Surjective (evaluationContinuousLinear D w) :=
  InitialThetaWittThetaSurjective.evaluation_surjective D w

end
end JoshiTeich.Act1Scene1.InitialThetaWittThetaPadicCompatibility
