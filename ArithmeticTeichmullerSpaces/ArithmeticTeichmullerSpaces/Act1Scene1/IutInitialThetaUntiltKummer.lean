import ArithmeticTeichmullerSpaces.Act1Scene1.EmbeddedAlgebraicClosure
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaClosureLog
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionUntiltTopology

/-!
source-id: JT-SCENE1-INITIAL-THETA-UNTILT-KUMMER
source: Joshi I def:untilt-galois (1470--1498), preferred-closure Kummer
(1588--1632); III actual principal units (3190--3236); II local eta_K pilots.
fidelity: inside the same actual geometric coefficient field used by the
Fontaine/de Rham pilot, constructs the relative algebraic closure of the
original torsion completion. The original principal-unit root tower, Galois
group and rational/saturated classes transport into this concrete subfield.
Their equations and original ordinary-log witnesses are preserved, and the
principal unit is built from the very same de Rham root image.
No whole-untilt Galois action, BK or cross-holomorphoid identity is assumed.
Original proofs; no reference copy; Prologue-R5 unchanged.
-/
namespace JoshiTeich.Act1Scene1.InitialThetaUntiltKummer
open JoshiTeich.Prologue PrincipalUnitKummer InitialThetaCanonicalGeometricFontaine
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (hsw : Ideal.LiesOver s.1.maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal)
local instance residuePrime : Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩
local instance baseCharZero : CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

abbrev localEmbedding : localField D s →+* coefficientField D w :=
  InitialThetaTorsionDeRhamPilot.embedding D w s.1 hsw


/-- The preferred algebraic closure is an actual subfield of the original untilt. -/
abbrev Closure := @EmbeddedAlgebraicClosure.Carrier (localField D s) (coefficientField D w)
  inferInstance inferInstance ((localEmbedding D w s hsw).toAlgebra)

local instance closureAlgebra : Algebra (localField D s) (Closure D w s hsw) := by
  letI := (localEmbedding D w s hsw).toAlgebra
  exact inferInstanceAs (Algebra (localField D s)
    (algebraicClosure (localField D s) (coefficientField D w)))

local instance closureIsAlgClosure : IsAlgClosure (localField D s) (Closure D w s hsw) := by
  let := (localEmbedding D w s hsw).toAlgebra
  exact inferInstance

local instance closureIsAlgClosed : IsAlgClosed (Closure D w s hsw) :=
  (closureIsAlgClosure D w s hsw).isAlgClosed

local instance closureAlgebraic : Algebra.IsAlgebraic (localField D s) (Closure D w s hsw) :=
  (closureIsAlgClosure D w s hsw).isAlgebraic

local instance closureIntegral : Algebra.IsIntegral (localField D s) (Closure D w s hsw) :=
  Algebra.isAlgebraic_iff_isIntegral.mp (closureAlgebraic D w s hsw)

private theorem localEmbedding_eq_algebraMap :
    letI := (localEmbedding D w s hsw).toAlgebra
    (algebraMap (localField D s) (coefficientField D w)) = localEmbedding D w s hsw := rfl

abbrev inclusion : Closure D w s hsw →+* coefficientField D w :=
  @EmbeddedAlgebraicClosure.inclusion (localField D s) (coefficientField D w)
    inferInstance inferInstance ((localEmbedding D w s hsw).toAlgebra)

def closureEquiv : closure D s ≃ₐ[localField D s] Closure D w s hsw :=
  @EmbeddedAlgebraicClosure.equiv (localField D s) (coefficientField D w)
    inferInstance inferInstance ((localEmbedding D w s hsw).toAlgebra) inferInstance

theorem mem_inclusion_range_iff (x : coefficientField D w) :
    letI := ((localEmbedding D w s hsw).toAlgebra)
    x ∈ (inclusion D w s hsw).range ↔ IsAlgebraic (localField D s) x :=
  @EmbeddedAlgebraicClosure.mem_inclusion_range_iff (localField D s) (coefficientField D w)
    inferInstance inferInstance ((localEmbedding D w s hsw).toAlgebra) x

def groupIso : (Closure D w s hsw ≃ₐ[localField D s] Closure D w s hsw) ≃ₜ*
    (closure D s ≃ₐ[localField D s] closure D s) :=
  @EmbeddedAlgebraicClosure.groupIso (localField D s) (coefficientField D w)
    inferInstance inferInstance ((localEmbedding D w s hsw).toAlgebra) inferInstance

def rootTower : LocalKummer.RootTower (Ω := Closure D w s hsw)
    (Arithmetic.residueChar s.1) (PaperLogWitnessHull.principalUnit D s) :=
  LocalKummer.ClosureTransport.mapRootTower (closureEquiv D w s hsw)
    (PrincipalUnitKummer.rootTower D s)

theorem rootTower_power (n : ℕ) :
    inclusion D w s hsw ((rootTower D w s hsw).root n) ^ (Arithmetic.residueChar s.1 ^ n) =
      localEmbedding D w s hsw (PaperLogWitnessHull.principalUnit D s) := by
  rw [← map_pow, (rootTower D w s hsw).root_pow_eq,
    EmbeddedAlgebraicClosure.inclusion_algebraMap, localEmbedding_eq_algebraMap]

theorem principalUnit_eq_rootImage :
    localEmbedding D w s hsw (PaperLogWitnessHull.principalUnit D s) =
      1 + (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : coefficientField D w) *
        InitialThetaTorsionDeRhamPilot.rootImage D w s.1 hsw := by
  classical
  simp only [PaperLogWitnessHull.principalUnit, LocalPadicLog.paperPrincipalUnit,
    map_add, map_one, map_mul, map_natCast]
  apply congrArg (fun z => 1 +
    (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : coefficientField D w) * z)
  change localEmbedding D w s hsw _ = localEmbedding D w s hsw _
  congr 1
  simp only [IutInitialThetaQRootFamily.qrootAt, dite_eq_left s.2]

theorem principalUnit_norm_sub_one_lt_one :
    ‖localEmbedding D w s hsw (PaperLogWitnessHull.principalUnit D s) - 1‖ < 1 := by
  rw [← map_one (localEmbedding D w s hsw), ← map_sub]
  exact (InitialThetaTorsionUntiltTopology.embedding_norm_lt_one_iff D w s.1 hsw _).mpr
    (PaperLogWitnessHull.principalUnit_norm_sub_one_lt_one D s)

theorem principalUnit_eq_theta_pilot :
    localEmbedding D w s hsw (PaperLogWitnessHull.principalUnit D s) =
      1 + (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : coefficientField D w) *
        InitialThetaDeRhamCompletion.theta D w
          (InitialThetaTorsionDeRhamPilot.pilot D w s.1 hsw 1) := by
  rw [principalUnit_eq_rootImage, InitialThetaTorsionDeRhamPilot.theta_pilot]
  simp only [one_pow, pow_one]

def imageClass : LocalPadicLog.principalKummerImage (k := localField D s)
    (Ω := Closure D w s hsw) (Arithmetic.residueChar s.1) :=
  ClosureLog.imageClass D s (Closure D w s hsw)

theorem imageClass_eq_kummer : (imageClass D w s hsw).1 =
    (LocalKummer.Rational.kummerHom (K := localField D s) (Ω := Closure D w s hsw)
      (Arithmetic.residueChar s.1) (actualPrincipalUnit D s).1).toAdd :=
  ClosureLog.imageClass_eq_kummer D s (Closure D w s hsw)

theorem imageClass_eq_rootTower : (imageClass D w s hsw).1 =
    LocalKummer.Rational.toH1 (Arithmetic.residueChar s.1)
      ((rootTower D w s hsw).kummerClass (Arithmetic.residueChar_prime s.1).pos
        (principalUnit_ne_zero D s)) := by
  rw [imageClass_eq_kummer]
  change LocalKummer.Rational.toH1 (Arithmetic.residueChar s.1)
      ((LocalKummer.rootTower (Ω := Closure D w s hsw) (Arithmetic.residueChar s.1)
        (Arithmetic.residueChar_prime s.1).pos (PaperLogWitnessHull.principalUnit D s)).kummerClass
        (Arithmetic.residueChar_prime s.1).pos (principalUnit_ne_zero D s)) = _
  exact congrArg (LocalKummer.Rational.toH1 (Arithmetic.residueChar s.1))
    (LocalKummer.RootTower.kummerClass_eq _ (rootTower D w s hsw)
      (Arithmetic.residueChar_prime s.1).pos (principalUnit_ne_zero D s))

theorem imageClass_log :
    LocalPadicLog.principalImageLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (imageClass D w s hsw) =
        (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : localField D s) *
          PaperLogWitnessHull.value D s :=
  ClosureLog.imageClass_log D s (Closure D w s hsw)

def dividedClass : LocalPadicLog.saturatedKummerImage (k := localField D s)
    (Ω := Closure D w s hsw) (Arithmetic.residueChar s.1) :=
  ClosureLog.dividedClass D s (Closure D w s hsw)

theorem dividedClass_log :
    LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (dividedClass D w s hsw) =
        PaperLogWitnessHull.value D s :=
  ClosureLog.dividedClass_log D s (Closure D w s hsw)

theorem dividedClass_ne_zero : dividedClass D w s hsw ≠ 0 :=
  ClosureLog.dividedClass_ne_zero D s (Closure D w s hsw)

end
end JoshiTeich.Act1Scene1.InitialThetaUntiltKummer
