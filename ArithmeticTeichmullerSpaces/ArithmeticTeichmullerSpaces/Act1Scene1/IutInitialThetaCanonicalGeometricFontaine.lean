import ArithmeticTeichmullerSpaces.Act1Scene1.CompletedAlgebraicClosure
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaGeometricFontaine

/-!
source-id: JT-SCENE1-INITIAL-THETA-CANONICAL-GEOMETRIC-FONTAINE
source: Joshi I de:geom-base-points; Arithmetic Holomorphic Structures
lem:perfectoid and its completed-algebraic-closure example.
fidelity: constructs the local coefficient field and its completion embedding
from the same actual InitialThetaData supported place. All geometric field,
closedness, isometry, prime-bound and Fontaine inputs are proved producers.
A selected tilt identification, Berkovich base point, tempered marking and
paper holomorphoid identity remain separate obligations. Original proofs.
boundary: Scene1/Derived; Prologue-R5 unchanged.
-/

set_option maxHeartbeats 2000000

namespace JoshiTeich.Act1Scene1.InitialThetaCanonicalGeometricFontaine

open JoshiTeich.Prologue NumberField
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance completionCharZero : CharZero (LocalCompletion.completionAt D.F w.1) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.1.maximalIdeal).injective

/-- The carrier and its structures are produced together from this actual completion. -/
def geometricExtension : CompletedAlgebraicClosure.Extension (LocalCompletion.completionAt D.F w.1) :=
  CompletedAlgebraicClosure.ofNormedField _ (by
    refine ⟨(Arithmetic.residueChar w.1 : LocalCompletion.completionAt D.F w.1)⁻¹, ?_⟩
    rw [norm_inv]
    have hp0 : (Arithmetic.residueChar w.1 : LocalCompletion.completionAt D.F w.1) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero
    exact (one_lt_inv₀ (norm_pos_iff.mpr hp0)).mpr
      (LocalCompletion.integerRing_prime_norm_lt_one w.1))

/-- The field projection keeps concrete completion structures behind a stable carrier. -/
def coefficientField := (geometricExtension D w).Carrier

instance coefficientField_normedField : NormedField (coefficientField D w) :=
  (geometricExtension D w).normedField

instance coefficientField_nontriviallyNormedField : NontriviallyNormedField (coefficientField D w) where
  toNormedField := coefficientField_normedField D w
  non_trivial := (geometricExtension D w).nontrivialNorm

instance coefficientField_completeSpace : CompleteSpace (coefficientField D w) :=
  (geometricExtension D w).completeSpace

instance coefficientField_ultrametric : IsUltrametricDist (coefficientField D w) :=
  (geometricExtension D w).ultrametric

instance coefficientField_charZero : CharZero (coefficientField D w) :=
  (geometricExtension D w).charZero

instance coefficientField_isAlgClosed : IsAlgClosed (coefficientField D w) :=
  (geometricExtension D w).isAlgClosed

def completionEmbedding : LocalCompletion.completionAt D.F w.1 →+* coefficientField D w :=
  (geometricExtension D w).embedding

theorem completionEmbedding_isometry : Isometry (completionEmbedding D w) :=
  (geometricExtension D w).embedding_isometry

theorem completionEmbedding_norm (x : LocalCompletion.completionAt D.F w.1) :
    ‖completionEmbedding D w x‖ = ‖x‖ := by
  simpa only [map_zero, dist_zero_right] using (completionEmbedding_isometry D w).dist_eq x 0

theorem primeNormFact : Fact (0 < ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ ∧
    ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ < 1) :=
  InitialThetaGeometricFontaine.primeNormFact D w (coefficientField D w)
    (completionEmbedding D w) (completionEmbedding_isometry D w)

def coefficientMap : 𝓞 D.F →+* LocalGeometricFontaine.integerRing (coefficientField D w) :=
  InitialThetaGeometricFontaine.coefficientMap D w (coefficientField D w)
    (completionEmbedding D w) (completionEmbedding_isometry D w)

theorem coefficientMap_coe (a : 𝓞 D.F) :
    (coefficientMap D w a : coefficientField D w) =
      completionEmbedding D w (FinitePlace.embedding w.1.maximalIdeal (a : D.F)) := rfl

theorem coefficientMap_injective : Function.Injective (coefficientMap D w) :=
  InitialThetaGeometricFontaine.coefficientMap_injective D w (coefficientField D w)
    (completionEmbedding D w) (completionEmbedding_isometry D w)

def placeData :
    letI := primeNormFact D w
    PerfectoidPlaceData D.F (LocalGeometricFontaine.integerRing (coefficientField D w))
      (Arithmetic.residueChar w.1) := by
  letI := primeNormFact D w
  exact InitialThetaGeometricFontaine.placeData D w (coefficientField D w)
    (completionEmbedding D w) (completionEmbedding_isometry D w)

theorem placeData_place :
    letI := primeNormFact D w
    (placeData D w).place = w.1 := by
  let := primeNormFact D w
  rfl

theorem placeData_laws :
    letI := primeNormFact D w
    PerfectoidPlaceLaws (Arithmetic.residueChar w.1) (placeData D w) := by
  let := primeNormFact D w
  exact InitialThetaGeometricFontaine.placeData_laws D w (coefficientField D w)
    (completionEmbedding D w) (completionEmbedding_isometry D w)

theorem theta_surjective :
    letI := primeNormFact D w
    Function.Surjective (placeData D w).data.theta := by
  let := primeNormFact D w
  exact InitialThetaGeometricFontaine.placeData_theta_surjective D w (coefficientField D w)
    (completionEmbedding D w) (completionEmbedding_isometry D w)

theorem frobenius_surjective :
    letI := primeNormFact D w
    Function.Surjective (frobenius
      (ModP (LocalGeometricFontaine.integerRing (coefficientField D w)) (Arithmetic.residueChar w.1))
      (Arithmetic.residueChar w.1)) := by
  let := primeNormFact D w
  exact InitialThetaGeometricFontaine.placeData_frobenius_surjective D w (coefficientField D w)
    (completionEmbedding D w) (completionEmbedding_isometry D w)

variable (theta : ThetaPilotData D.F) (thetaBase : theta.index)
variable (packetHull : PacketHullData theta.index) (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F) (logVolume : ℝ) (processionLength : ℕ)

def bridgeData :
    letI := primeNormFact D w
    PerfectoidBridgeData
      (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull heightData
        ramification logVolume processionLength) (Arithmetic.residueChar w.1) (placeData D w) := by
  let := primeNormFact D w
  exact InitialThetaGeometricFontaine.bridgeData D w (coefficientField D w)
    (completionEmbedding D w) (completionEmbedding_isometry D w)
    theta thetaBase packetHull heightData ramification logVolume processionLength

theorem bridgeData_laws :
    letI := primeNormFact D w
    PerfectoidBridgeLaws
      (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull heightData
        ramification logVolume processionLength) (Arithmetic.residueChar w.1) (placeData D w)
          (bridgeData D w theta thetaBase packetHull heightData ramification logVolume processionLength) := by
  let := primeNormFact D w
  exact InitialThetaGeometricFontaine.bridgeData_laws D w (coefficientField D w)
    (completionEmbedding D w) (completionEmbedding_isometry D w)
    theta thetaBase packetHull heightData ramification logVolume processionLength

theorem bridgeData_coefficientMap (a : 𝓞 D.F) :
    letI := primeNormFact D w
    ((bridgeData D w theta thetaBase packetHull heightData ramification logVolume
      processionLength).coefficientMap a : coefficientField D w) =
        completionEmbedding D w (FinitePlace.embedding w.1.maximalIdeal (a : D.F)) := by
  let := primeNormFact D w
  rfl

end
end JoshiTeich.Act1Scene1.InitialThetaCanonicalGeometricFontaine
