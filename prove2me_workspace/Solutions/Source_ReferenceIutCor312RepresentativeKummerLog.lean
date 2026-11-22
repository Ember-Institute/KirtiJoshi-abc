import Solutions.Source_ReferenceIutCor312RepresentativeComparisonLog
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAmbientKummerLog
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerLogShell

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1
open scoped BigOperators Valued

universe u v

noncomputable section

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}

local instance representativeKummerPrime {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) :
    Fact (JoshiTeich.Prologue.Arithmetic.residueChar s).Prime :=
  LocalCompletion.selectedPrime s

local instance representativeKummerCharZero {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : CharZero (LocalCompletion.completionAt K s) :=
  LocalCompletion.completionCharZero s

local instance representativeKummerAlgebra {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) :
    Algebra ℚ_[JoshiTeich.Prologue.Arithmetic.residueChar s]
      (LocalCompletion.completionAt K s) :=
  LocalCompletion.padicAlgebra (w := s) rfl

local instance representativeKummerContinuousSMul {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) :
    ContinuousSMul ℚ_[JoshiTeich.Prologue.Arithmetic.residueChar s]
      (LocalCompletion.completionAt K s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s) rfl)

/-- The principal unit `1 + p* · qroot` in the chosen finite completion. -/
def paperQRootPrincipalUnit (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt) :
    LocalPadicLog.principalUnits (k := LocalCompletion.completionAt D.Kt s) := by
  let p := JoshiTeich.Prologue.Arithmetic.residueChar s
  have hp : p.Prime := JoshiTeich.Prologue.Arithmetic.residueChar_prime s
  have hpNorm : ‖(p : LocalCompletion.completionAt D.Kt s)‖ < 1 :=
    LocalCompletion.KummerValuation.prime_norm_lt_one s p rfl
  have hroot : ‖TL.qroot s‖ ≤ 1 :=
    LocalConstruct.norm_le_one_of_ordp_nonneg (TL.ordp_qroot_nonneg s)
  exact ⟨Units.mk0 (LocalPadicLog.paperPrincipalUnit p (TL.qroot s))
    (LocalPadicLog.paperPrincipalUnit_ne_zero hp hpNorm hroot),
    LocalPadicLog.paperPrincipalUnit_norm_sub_one_lt_one hp hpNorm hroot⟩

/-- The principal unit's rational Kummer class in continuous cohomology of the
actual finite completion at `s`. -/
def paperQRootKummerClass (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt) :
    continuousCohomology 1 (LocalKummer.Rational.topRep
      (K := LocalCompletion.completionAt D.Kt s)
      (Ω := AlgebraicClosure (LocalCompletion.completionAt D.Kt s))
      (JoshiTeich.Prologue.Arithmetic.residueChar s)) :=
  (LocalKummer.Rational.kummerHom (K := LocalCompletion.completionAt D.Kt s)
    (Ω := AlgebraicClosure (LocalCompletion.completionAt D.Kt s))
    (JoshiTeich.Prologue.Arithmetic.residueChar s) (TL.paperQRootPrincipalUnit s).1).toAdd

/-- The ordinary ambient Kummer logarithm evaluates this class on its principal unit. -/
theorem ambientLog_paperQRootKummerClass (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt) :
    LocalCompletion.KummerValuation.ambientLog s (JoshiTeich.Prologue.Arithmetic.residueChar s)
        rfl (TL.paperQRootKummerClass s) =
      LocalPadicLog.padicLog (LocalPadicLog.paperPrincipalUnit
        (JoshiTeich.Prologue.Arithmetic.residueChar s) (TL.qroot s)) := by
  let p := JoshiTeich.Prologue.Arithmetic.residueChar s
  let hpNorm := LocalCompletion.KummerValuation.prime_norm_lt_one s p rfl
  let a := Additive.ofMul (TL.paperQRootPrincipalUnit s)
  let c := LocalPadicLog.principalSaturatedClass (k := LocalCompletion.completionAt D.Kt s)
    (Ω := AlgebraicClosure (LocalCompletion.completionAt D.Kt s)) p hpNorm a
  change LocalCompletion.KummerValuation.ambientLog s p rfl c.1 = _
  exact (LocalCompletion.KummerValuation.ambientLog_unit s p rfl c).trans
    (LocalPadicLog.saturatedPadicLog_principalSaturatedClass p hpNorm a)

/-- The ordinary ambient logarithm of the Kummer class divided by `p*`. -/
def paperQRootKummerLog (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt) :
    LocalCompletion.completionAt D.Kt s :=
  let p := JoshiTeich.Prologue.Arithmetic.residueChar s
  (LocalPadicLog.paperScale p : LocalCompletion.completionAt D.Kt s)⁻¹ *
    LocalCompletion.KummerValuation.ambientLog s p rfl (TL.paperQRootKummerClass s)

theorem paperQRootKummerLog_eq_paperNormalizedQRootLog
    (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt) :
    TL.paperQRootKummerLog s = TL.paperNormalizedQRootLog s := by
  unfold paperQRootKummerLog paperNormalizedQRootLog LocalPadicLog.paperNormalizedLog
  dsimp only
  rw [TL.ambientLog_paperQRootKummerClass s]

/-- The finite packet log-volume identity using the normalized ordinary Kummer log at
the representative chosen by P7 at each bad moduli place. -/
theorem log_normalized_sectionKummerLogProduct_eq_sum_finite_packetVol
    (hModuli : @algebraMap ↥(fieldOfModuli D.F D.E) D.Kt _ _ D.algebraModK =
      (algebraMap D.F D.Kt).comp (algebraMap ↥(fieldOfModuli D.F D.E) D.F))
    (TL : ThetaLocalData D (LocalConstruct.concreteLocalTheory (K := D.Kt)))
    (QI : QPilotInputs D) :
    let m := (D.ℓ - 1) / 2
    let M := ↥(fieldOfModuli D.F D.E)
    let R := TL.rhsData
    Real.log (∏ i : Fin m, ∏ w ∈ QI.badModuliFinset.attach,
      ‖completionInPadicComplex (D.localData.sect.sectFin w.1)
        (TL.paperQRootKummerLog (D.localData.sect.sectFin w.1))‖ ^
        ((((i.1 + 1 : ℕ) : ℝ) / (m : ℝ)) ^ 2 * placeWeight M w.1)) =
      (∑ i : Fin m, ∑ p ∈ TL.badChars.attach,
        let q := RationalPlace.finite ⟨p.1, TL.badChars_prime p.1 p.2⟩
        R.vol.packetVol i q ((R.thetaHull i).region q)) / (m : ℝ) ^ 2 :=
  log_normalized_sectionComparisonLogProduct_eq_sum_finite_packetVol hModuli TL QI
    (fun w => TL.paperQRootKummerLog (D.localData.sect.sectFin w.1))
    (fun w => TL.paperQRootKummerLog_eq_paperNormalizedQRootLog (D.localData.sect.sectFin w.1))

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
