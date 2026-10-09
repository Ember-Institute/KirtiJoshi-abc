import ArithmeticTeichmullerSpaces.Act1Scene1.Corollary312
import ArithmeticTeichmullerSpaces.Act1Scene1.IutQSourceContract

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped NumberField

universe u

/-!
source-id: IUT-COR312-FIELD-ORIENTATION
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/Basic.lean`,
`refer/iut/Iut/Concrete/ThetaRegion.lean`, and
`refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean`.
fidelity: audits that a base-field q-pilot and torsion-field q-root source have
the same carrier and local parameter as the Scene1 link. The source contracts
and their arithmetic order laws are defined in `IutQSourceContract`.
boundary: Scene1/Derived
-/

structure IutFieldOrientationAudit
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    {F : Type u} [Field F] [NumberField F] [Algebra F K]
    (B : IutBaseQPilotSource F T.ell)
    (R : IutTorsionQRootSource F K T.ell B) where
  /-- The target Scene1 carrier is the torsion-field carrier. -/
  torsionCarrier_eq_link : R.badFinset = T.scene1.data.link.places
  /-- The target's local Tate parameter is the image of the base completion value. -/
  linkParameter_completion_eq : ∀ v : R.badFinset,
    R.completionMap v (B.tateParameter (R.basePlace v)) =
      T.scene1.data.link.tate.parameter v.1

namespace IutFieldOrientationAudit

variable {K : Type u} [Field K] [NumberField K]
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}
variable {F : Type u} [Field F] [NumberField F] [Algebra F K]
variable {B : IutBaseQPilotSource F T.ell}
variable {R : IutTorsionQRootSource F K T.ell B}

lemma target_carrier_eq_torsion
    (A : IutFieldOrientationAudit p T B R) :
    R.badFinset = T.scene1.data.link.places :=
  A.torsionCarrier_eq_link

lemma qroot_pow_eq_link_completion
    (_A : IutFieldOrientationAudit p T B R) (v : R.badFinset) :
    R.qroot v ^ (2 * T.ell) =
      R.completionMap v (B.tateParameter (R.basePlace v)) := by
  exact R.qroot_pow_eq v

lemma qroot_pow_eq_target_completion
    (A : IutFieldOrientationAudit p T B R) (v : R.badFinset) :
    R.qroot v ^ (2 * T.ell) =
      T.scene1.data.link.tate.parameter v.1 := by
  calc
    R.qroot v ^ (2 * T.ell) =
        R.completionMap v (B.tateParameter (R.basePlace v)) :=
      R.qroot_pow_eq v
    _ = T.scene1.data.link.tate.parameter v.1 :=
      A.linkParameter_completion_eq v

lemma base_weight_is_arithmetic
    (w : NumberField.FinitePlace F) :
    B.weight w = Arithmetic.qPilotWeight w :=
  B.weight_eq_qPilotWeight w

end IutFieldOrientationAudit

end JoshiTeich.Act1Scene1
