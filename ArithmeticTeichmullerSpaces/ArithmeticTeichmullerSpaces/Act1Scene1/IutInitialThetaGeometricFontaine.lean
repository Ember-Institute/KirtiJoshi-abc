import ArithmeticTeichmullerSpaces.Act1Scene1.AlgebraicallyClosedFontaine
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCompletionFontaine

/-!
source-id: JT-SCENE1-INITIAL-THETA-GEOMETRIC-FONTAINE
source: Joshi I def:arith-hol-strs and def:untilt-galois;
Arithmetic Holomorphic Structures lem:perfectoid; actual InitialThetaData support.
fidelity: given an actual completion embedding into a complete algebraically
closed ultrametric field, derive the prime bounds, integer-ring completeness,
coefficient map and canonical Fontaine bridge, including theta surjectivity.
The field and its isometric embedding are explicit geometric inputs. This does
not construct a global holomorphoid, its tilt identity or tempered marking.
Original proofs; no reference source code copied; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometricFontaine

open JoshiTeich.Prologue NumberField
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (Ω : Type u) [NormedField Ω]
variable (ι : LocalCompletion.completionAt D.F w.1 →+* Ω) (hι : Isometry ι)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance completionCharZero : CharZero (LocalCompletion.completionAt D.F w.1) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.1.maximalIdeal).injective

include hι in
theorem embedding_norm_eq (x : LocalCompletion.completionAt D.F w.1) : ‖ι x‖ = ‖x‖ := by
  simpa only [map_zero, dist_zero_right] using hι.dist_eq x 0

include hι in
theorem prime_norm_bounds :
    0 < ‖(Arithmetic.residueChar w.1 : Ω)‖ ∧ ‖(Arithmetic.residueChar w.1 : Ω)‖ < 1 := by
  rw [← map_natCast ι, embedding_norm_eq D w Ω ι hι]
  exact ⟨norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero),
    LocalCompletion.integerRing_prime_norm_lt_one w.1⟩

include hι in
theorem primeNormFact :
    Fact (0 < ‖(Arithmetic.residueChar w.1 : Ω)‖ ∧ ‖(Arithmetic.residueChar w.1 : Ω)‖ < 1) :=
  ⟨prime_norm_bounds D w Ω ι hι⟩

variable [IsUltrametricDist Ω]

/-- Actual global integer embedding into the chosen geometric coefficient field. -/
def coefficientMap : 𝓞 D.F →+* LocalGeometricFontaine.integerRing Ω :=
  (ι.comp ((FinitePlace.embedding w.1.maximalIdeal).comp (algebraMap (𝓞 D.F) D.F))).codRestrict
    (LocalGeometricFontaine.integerRing Ω) (fun a => by
      rw [LocalGeometricFontaine.mem_integerRing]
      change ‖ι (FinitePlace.embedding w.1.maximalIdeal (a : D.F))‖ ≤ 1
      rw [embedding_norm_eq D w Ω ι hι]
      exact FinitePlace.norm_le_one D.F w.1.maximalIdeal a)

theorem coefficientMap_coe (a : 𝓞 D.F) :
    (coefficientMap D w Ω ι hι a : Ω) = ι (FinitePlace.embedding w.1.maximalIdeal (a : D.F)) := rfl

theorem coefficientMap_injective : Function.Injective (coefficientMap D w Ω ι hι) := by
  intro a b h
  apply Subtype.ext
  apply (FinitePlace.embedding w.1.maximalIdeal).injective
  apply ι.injective
  exact congrArg (fun x : LocalGeometricFontaine.integerRing Ω => (x : Ω)) h

variable [CompleteSpace Ω]

def placeData :
    letI := primeNormFact D w Ω ι hι
    PerfectoidPlaceData D.F (LocalGeometricFontaine.integerRing Ω) (Arithmetic.residueChar w.1) := by
  letI := primeNormFact D w Ω ι hι
  exact { place := w.1, data := Perfectoid.canonicalPerfectoidData }

theorem placeData_place :
    letI := primeNormFact D w Ω ι hι
    (placeData D w Ω ι hι).place = w.1 := by
  let := primeNormFact D w Ω ι hι
  rfl

theorem placeData_laws :
    letI := primeNormFact D w Ω ι hι
    PerfectoidPlaceLaws (Arithmetic.residueChar w.1) (placeData D w Ω ι hι) := by
  let := primeNormFact D w Ω ι hι
  exact ⟨Perfectoid.canonicalPerfectoidData_laws⟩

section AlgebraicallyClosed
variable [IsAlgClosed Ω]

theorem placeData_theta_surjective :
    letI := primeNormFact D w Ω ι hι
    Function.Surjective (placeData D w Ω ι hι).data.theta := by
  let := primeNormFact D w Ω ι hι
  exact LocalGeometricFontaine.theta_surjective Ω (Arithmetic.residueChar w.1)

include hι in
omit [CompleteSpace Ω] [IsUltrametricDist Ω] in
theorem exists_norm_between_prime :
    ∃ y : Ω, ‖(Arithmetic.residueChar w.1 : Ω)‖ < ‖y‖ ∧ ‖y‖ < 1 :=
  LocalGeometricFontaine.exists_norm_between Ω (Arithmetic.residueChar w.1)
    (prime_norm_bounds D w Ω ι hι).1 (prime_norm_bounds D w Ω ι hι).2

omit [CompleteSpace Ω] in
theorem placeData_frobenius_surjective :
    letI := primeNormFact D w Ω ι hι
    Function.Surjective
      (frobenius (ModP (LocalGeometricFontaine.integerRing Ω) (Arithmetic.residueChar w.1))
        (Arithmetic.residueChar w.1)) := by
  let := primeNormFact D w Ω ι hι
  exact LocalGeometricFontaine.frobenius_modP_surjective Ω (Arithmetic.residueChar w.1)

end AlgebraicallyClosed

variable (theta : ThetaPilotData D.F) (thetaBase : theta.index)
variable (packetHull : PacketHullData theta.index) (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F) (logVolume : ℝ) (processionLength : ℕ)

def bridgeData :
    letI := primeNormFact D w Ω ι hι
    PerfectoidBridgeData
      (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull heightData
        ramification logVolume processionLength) (Arithmetic.residueChar w.1) (placeData D w Ω ι hι) := by
  let := primeNormFact D w Ω ι hι
  exact { coefficientMap := coefficientMap D w Ω ι hι }

theorem bridgeData_laws :
    letI := primeNormFact D w Ω ι hι
    PerfectoidBridgeLaws
      (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull heightData
        ramification logVolume processionLength) (Arithmetic.residueChar w.1) (placeData D w Ω ι hι)
          (bridgeData D w Ω ι hι theta thetaBase packetHull heightData ramification logVolume processionLength) := by
  let := primeNormFact D w Ω ι hι
  exact ⟨w.2, placeData_laws D w Ω ι hι⟩

theorem bridgeData_coefficientMap (a : 𝓞 D.F) :
    letI := primeNormFact D w Ω ι hι
    ((bridgeData D w Ω ι hι theta thetaBase packetHull heightData ramification logVolume
      processionLength).coefficientMap a : Ω) =
        ι (FinitePlace.embedding w.1.maximalIdeal (a : D.F)) := by
  let := primeNormFact D w Ω ι hι
  rfl

end
end JoshiTeich.Act1Scene1.InitialThetaGeometricFontaine
