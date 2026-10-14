import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Semilinear
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRationalCohomology

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-COEFFICIENT-CHANGE
source: the integral/rational H1 comparison needed in Joshi III (3214--3236).
fidelity: maps standard integral H1 to standard rational H1, and proves
agreement with the previous explicit Kummer quotient construction. Nonzero
integral torsion is killed, so injectivity is not asserted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.Rational
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]

def integralCoefficient : padicTateTopRep (K := K) (Ω := Ω) p →SL[PadicInt.Coe.ringHom (p := p)]
    topRep (K := K) (Ω := Ω) p where
  toFun x := ULift.up (coefficientMap p x)
  map_add' x y := by apply ULift.ext; exact map_add (coefficientMap p) x y
  map_smul' r x := by apply ULift.ext; exact coefficientMap_smul p r x
  cont := continuous_uliftUp.comp (continuous_coefficientMap p)

theorem integralCoefficient_equivariant (σ : Ω ≃ₐ[K] Ω)
    (x : padicTateTopRep (K := K) (Ω := Ω) p) :
    integralCoefficient p ((padicTateTopRep p).ρ σ x) =
      (topRep p).ρ σ (integralCoefficient p x) := by
  apply ULift.ext
  exact coefficientMap_equivariant p σ x

def standardMap : continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p) →SL[PadicInt.Coe.ringHom (p := p)]
    continuousCohomology 1 (topRep (K := K) (Ω := Ω) p) :=
  ContinuousH1Semilinear.map _ _ (integralCoefficient p) (integralCoefficient_equivariant p)

theorem standardMap_classOfCocycle (f : continuousCocycles (K := K) (Ω := Ω) p) :
    standardMap p (padicClassOfCocycle p f) = classOfCocycle p f :=
  ContinuousH1Semilinear.map_classOf _ _ (integralCoefficient p)
    (integralCoefficient_equivariant p) (padicAdditiveCocycle p f) (padicAdditiveCocycle_law p f)

theorem standardMap_toPadicH1 (c : continuousH1 (K := K) (Ω := Ω) p) :
    standardMap p (toPadicH1 p c) = toH1 p c := by
  induction c using Quotient.inductionOn with
  | h f => exact standardMap_classOfCocycle p f

theorem standardMap_eq_zero_of_torsion (r : ℤ_[p]) (hr : r ≠ 0)
    (x : continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p)) (hx : r • x = 0) :
    standardMap p x = 0 := by
  have h := congrArg (standardMap (K := K) (Ω := Ω) p) hx
  rw [map_smulₛₗ, map_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (PadicInt.coe_ne_zero.mpr hr)

theorem standardMap_not_injective_of_torsion (r : ℤ_[p]) (hr : r ≠ 0)
    (x : continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p))
    (hx : x ≠ 0) (ht : r • x = 0) : ¬ Function.Injective (standardMap (K := K) (Ω := Ω) p) := by
  intro hinj
  apply hx
  apply hinj
  rw [standardMap_eq_zero_of_torsion p r hr x ht, map_zero]

end
end JoshiTeich.Act1Scene1.LocalKummer.Rational
