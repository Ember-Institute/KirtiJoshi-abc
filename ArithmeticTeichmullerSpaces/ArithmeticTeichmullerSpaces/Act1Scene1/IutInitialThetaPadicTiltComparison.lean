import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAlgebraicPadicNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTiltField
import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-TILT-COMPARISON
source: Joshi II `se:ff-rings`, with fixed F=C_p^flat, and the actual
completed-algebraic-closure comparison proved in Scene1.
fidelity: constructs the comparison from the coefficient field of the same
InitialThetaData supported place to standard C_p, retaining the exact
local-degree power of its original norm. The integer, mod-p, pretilt and
fraction-field comparisons consume this constructed comparison.
boundary: Scene1/Derived; this is a local coefficient comparison, without
paper period-ring or global holomorphoid identities. Original proofs; no
reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicTiltComparison

open JoshiTeich.Prologue
open InitialThetaCanonicalGeometricFontaine
noncomputable section

private theorem ofNormedField_norm_eq_raw
    (B : Type*) [NormedField B] [CompleteSpace B] [IsUltrametricDist B] [CharZero B]
    (h₁ h₂ : ∃ x : B, 1 < ‖x‖) :
    letI : NontriviallyNormedField B :=
      { (inferInstance : NormedField B) with non_trivial := h₂ }
    ∀ x : (CompletedAlgebraicClosure.ofNormedField B h₁).Carrier,
      (letI := (CompletedAlgebraicClosure.ofNormedField B h₁).normedField
       ‖x‖) =
        @norm (CompletedAlgebraicClosure.Field B)
          (UniformSpace.Completion.instNorm (CompletedAlgebraicClosure.Algebraic B)) x := by
  exact fun x => rfl

universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

local instance rawNontrivialNorm :
    NontriviallyNormedField (LocalCompletion.completionAt D.F w.1) :=
  LocalCompletion.completionNontrivialNorm w.1
local instance rawComplete : CompleteSpace (LocalCompletion.completionAt D.F w.1) :=
  LocalCompletion.completionComplete w.1
local instance rawUltrametric : IsUltrametricDist (LocalCompletion.completionAt D.F w.1) :=
  LocalCompletion.completionUltrametric w.1
local instance rawCharZero : CharZero (LocalCompletion.completionAt D.F w.1) :=
  LocalCompletion.completionCharZero w.1

private abbrev RawCompleted := CompletedAlgebraicClosure.Field (LocalCompletion.completionAt D.F w.1)

abbrev Standard := PadicComplex (Arithmetic.residueChar w.1)

def coefficientEquiv : coefficientField D w ≃+* Standard D w :=
  LocalCompletion.completedPadicEquiv w.1

theorem coefficientEquiv_apply (x : coefficientField D w) :
    coefficientEquiv D w x = LocalCompletion.completedPadicEquiv w.1 x := rfl

private def completedRawNorm (x : coefficientField D w) : ℝ :=
  @norm _ (UniformSpace.Completion.instNorm (LocalCompletion.AlgebraicCompletion w.1)) x

private theorem coefficient_norm_eq_raw (x : coefficientField D w) :
    ‖x‖ = completedRawNorm D w x :=
  ofNormedField_norm_eq_raw (LocalCompletion.completionAt D.F w.1)
    (LocalCompletion.completionNontrivialNorm w.1).non_trivial
    (LocalCompletion.completionNontrivialNorm w.1).non_trivial x

theorem coefficientEquiv_norm_pow (x : coefficientField D w) :
    ‖coefficientEquiv D w x‖ ^ Arithmetic.localDeg w.1 = ‖x‖ := by
  calc
    ‖coefficientEquiv D w x‖ ^ Arithmetic.localDeg w.1 =
        ‖LocalCompletion.completedPadicEquiv w.1 (show RawCompleted D w from x)‖ ^
          Arithmetic.localDeg w.1 :=
      congrArg (fun y : Standard D w => ‖y‖ ^ Arithmetic.localDeg w.1) (coefficientEquiv_apply D w x)
    _ = completedRawNorm D w x := LocalCompletion.completedPadicEquiv_norm_pow w.1 x
    _ = ‖x‖ := (coefficient_norm_eq_raw D w x).symm

theorem standard_prime_norm :
    0 < ‖(Arithmetic.residueChar w.1 : Standard D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : Standard D w)‖ < 1 := by
  have h := coefficientEquiv_norm_pow D w
    (Arithmetic.residueChar w.1 : coefficientField D w)
  rw [map_natCast] at h
  constructor
  · exact norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  · apply (pow_lt_one_iff_of_nonneg (norm_nonneg _) (Arithmetic.localDeg_pos w.1).ne').mp
    exact h.trans_lt (primeNormFact D w).out.2

local instance sourcePrimeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ < 1) := primeNormFact D w

local instance standardPrimeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : Standard D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : Standard D w)‖ < 1) := ⟨standard_prime_norm D w⟩

def integerEquiv : LocalGeometricFontaine.integerRing (coefficientField D w) ≃+*
    LocalGeometricFontaine.integerRing (Standard D w) :=
  GeometricTiltComparison.integerEquiv (coefficientEquiv D w) (Arithmetic.localDeg w.1)
    (Arithmetic.localDeg_pos w.1) (coefficientEquiv_norm_pow D w)

theorem integerEquiv_apply (x : LocalGeometricFontaine.integerRing (coefficientField D w)) :
    (integerEquiv D w x : Standard D w) = coefficientEquiv D w x := rfl

def modPEquiv : ModP (LocalGeometricFontaine.integerRing (coefficientField D w))
    (Arithmetic.residueChar w.1) ≃+*
      ModP (LocalGeometricFontaine.integerRing (Standard D w)) (Arithmetic.residueChar w.1) :=
  GeometricTiltComparison.modPEquiv (coefficientEquiv D w) (Arithmetic.localDeg w.1)
    (Arithmetic.localDeg_pos w.1) (coefficientEquiv_norm_pow D w) (Arithmetic.residueChar w.1)

def sourceEquiv : InitialThetaTiltField.Source D w ≃+*
    GeometricTiltField.Source (Standard D w) (Arithmetic.residueChar w.1) :=
  GeometricTiltComparison.preTiltEquiv (coefficientEquiv D w) (Arithmetic.localDeg w.1)
    (Arithmetic.localDeg_pos w.1) (coefficientEquiv_norm_pow D w) (Arithmetic.residueChar w.1)

theorem sourceEquiv_coeff (x : InitialThetaTiltField.Source D w) (n : ℕ) :
    PreTilt.coeff n (sourceEquiv D w x) = modPEquiv D w (PreTilt.coeff n x) := rfl

theorem sourceEquiv_valuation_pow (x : InitialThetaTiltField.Source D w) :
    GeometricTiltField.sourceValuation (Standard D w) (Arithmetic.residueChar w.1)
        (sourceEquiv D w x) ^ Arithmetic.localDeg w.1 =
      InitialThetaTiltField.sourceValuation D w x :=
  GeometricTiltComparison.sourceValuation_pow (coefficientEquiv D w) (Arithmetic.localDeg w.1)
    (Arithmetic.localDeg_pos w.1) (coefficientEquiv_norm_pow D w) (Arithmetic.residueChar w.1) x

abbrev StandardTilt := GeometricTiltField.FractionField (Standard D w) (Arithmetic.residueChar w.1)

def tiltEquiv : InitialThetaTiltField.Carrier D w ≃+* StandardTilt D w :=
  GeometricTiltComparison.fractionEquiv (coefficientEquiv D w) (Arithmetic.localDeg w.1)
    (Arithmetic.localDeg_pos w.1) (coefficientEquiv_norm_pow D w) (Arithmetic.residueChar w.1)

theorem tiltEquiv_inclusion (x : InitialThetaTiltField.Source D w) :
    tiltEquiv D w (InitialThetaTiltField.inclusion D w x) =
      algebraMap (GeometricTiltField.Source (Standard D w) (Arithmetic.residueChar w.1))
        (StandardTilt D w) (sourceEquiv D w x) :=
  GeometricTiltComparison.fractionEquiv_inclusion (coefficientEquiv D w) (Arithmetic.localDeg w.1)
    (Arithmetic.localDeg_pos w.1) (coefficientEquiv_norm_pow D w) (Arithmetic.residueChar w.1) x

theorem tiltEquiv_valuation_pow (x : InitialThetaTiltField.Carrier D w) :
    GeometricTiltField.fractionValuation (Standard D w) (Arithmetic.residueChar w.1)
        (tiltEquiv D w x) ^ Arithmetic.localDeg w.1 = InitialThetaTiltField.valuation D w x :=
  GeometricTiltComparison.fractionValuation_pow (coefficientEquiv D w) (Arithmetic.localDeg w.1)
    (Arithmetic.localDeg_pos w.1) (coefficientEquiv_norm_pow D w) (Arithmetic.residueChar w.1) x

theorem tiltEquiv_frobenius (x : InitialThetaTiltField.Carrier D w) :
    tiltEquiv D w
        (frobenius (InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1) x) =
      frobenius (StandardTilt D w) (Arithmetic.residueChar w.1) (tiltEquiv D w x) := by
  simp only [frobenius_def, map_pow]

end
end JoshiTeich.Act1Scene1.InitialThetaPadicTiltComparison
