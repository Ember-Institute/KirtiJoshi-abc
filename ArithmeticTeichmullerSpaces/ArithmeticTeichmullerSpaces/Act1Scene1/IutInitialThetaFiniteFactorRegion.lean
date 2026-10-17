import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadQRootFamily
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIndeterminacyRegion

/-!
source-id: JT-SCENE1-INITIAL-THETA-FINITE-FACTOR-REGION
source: `refer/iut/Iut/Concrete/ThetaRegion.lean`,
`ThetaLocalData.scaleElt`, `thetaFinite`, `thetaComponent_eq_integral`
(148--240); Joshi III `th:thetam-construction` supplies the intended
theta-locus consumer, whose identification remains a separate obligation.
fidelity: uses the actual VBad root family of one InitialThetaData and its
completion tensor Packet. Only the distinguished factor is scaled by qroot
to the square power. Compactness, positive finite Haar, integral containment,
and equality with the normalization away from bad characteristics are proved.
Original consumer proofs; no reference source code copied.
boundary: Scene1/Derived; no paper theta/BK/untilt identification.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaFiniteFactorRegion

open JoshiTeich.Prologue
open IutInitialThetaQRootFamily
open scoped Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem qrootAt_norm_le_one (v : NumberField.FinitePlace ↥D.prime.torsionField) :
    ‖qrootAt D v‖ ≤ 1 := by
  unfold qrootAt
  split_ifs with hv
  · exact (iutInitialThetaFullQRoot_norm_lt_one D ⟨v, hv⟩).le
  · simp

theorem vbadQrootAt_norm_le_one (v : NumberField.FinitePlace ↥D.prime.torsionField) :
    ‖vbadQrootAt D v‖ ≤ 1 := by
  unfold vbadQrootAt
  split_ifs
  · exact qrootAt_norm_le_one D v
  · simp

variable {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (P : LocalCompletion.Packet ↥D.prime.torsionField p ι)
local instance factorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  LocalCompletion.padicAlgebra (P.residueChar_eq i)
local instance integralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

/-- All factors except d carry 1. The exponent is j squared. -/
def scalars (d : ι) (j : ℕ) : ∀ i, P.Factor i :=
  Pi.mulSingle d (vbadQrootAt D (P.place d) ^ (j ^ 2))

omit [Fact p.Prime] [Fintype ι] in
theorem scalars_distinguished (d : ι) (j : ℕ) :
    scalars D P d j d = vbadQrootAt D (P.place d) ^ (j ^ 2) := by
  simp [scalars]

omit [Fact p.Prime] [Fintype ι] in
theorem scalars_other (d : ι) (j : ℕ) (i : ι) (hi : i ≠ d) :
    scalars D P d j i = 1 := by
  simp [scalars, hi]

omit [Fact p.Prime] [Fintype ι] in
theorem scalars_ne_zero (d : ι) (j : ℕ) (i : ι) :
    scalars D P d j i ≠ 0 := by
  by_cases hi : i = d
  · subst i
    rw [scalars_distinguished]
    exact pow_ne_zero _ (vbadQrootAt_ne_zero D _)
  · rw [scalars_other D P d j i hi]
    exact one_ne_zero

omit [Fact p.Prime] [Fintype ι] in
theorem scalars_norm_le_one (d : ι) (j : ℕ) (i : ι) :
    ‖scalars D P d j i‖ ≤ 1 := by
  by_cases hi : i = d
  · subst i
    rw [scalars_distinguished, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (vbadQrootAt_norm_le_one D _)
  · rw [scalars_other D P d j i hi]
    simp

def scaleElt (d : ι) (j : ℕ) : P.Tensor := P.pure (scalars D P d j)

omit [Fintype ι] in
theorem scaleElt_eq_singleAlgHom (d : ι) (j : ℕ) :
    scaleElt D P d j =
      PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := fun i => P.Factor i) d
        (vbadQrootAt D (P.place d) ^ (j ^ 2)) := by
  rfl

theorem scaleElt_isUnit (d : ι) (j : ℕ) : IsUnit (scaleElt D P d j) :=
  P.pure_isUnit (scalars D P d j) (scalars_ne_zero D P d j)

/-- The finite factor-automorphism orbit of the actual scaled normalization. -/
def region (d : ι) (j : ℕ) : Set P.Tensor :=
  P.factorOrbitScalarRegion (scalars D P d j) (scalars_ne_zero D P d j)

theorem region_eq_orbit_principalRegion (d : ι) (j : ℕ) :
    region D P d j = P.factorIndeterminacyOrbit (P.principalRegion (scaleElt D P d j)) := by
  unfold region LocalCompletion.Packet.factorOrbitScalarRegion
  rw [P.scalarNormalization_eq_principalRegion]
  rfl

theorem scaleElt_mem_region (d : ι) (j : ℕ) :
    scaleElt D P d j ∈ region D P d j :=
  P.pure_mem_factorOrbitScalarRegion (scalars D P d j) (scalars_ne_zero D P d j)

theorem region_isCompact (d : ι) (j : ℕ) : IsCompact (region D P d j) :=
  P.factorOrbitScalarRegion_isCompact (scalars D P d j) (scalars_ne_zero D P d j)

theorem region_haar_pos_lt_top (d : ι) (j : ℕ) :
    0 < P.normalizationHaar (region D P d j) ∧
      P.normalizationHaar (region D P d j) < ⊤ :=
  P.factorOrbitScalarRegion_haar_pos_lt_top (scalars D P d j) (scalars_ne_zero D P d j)

theorem region_subset_normalization (d : ι) (j : ℕ) :
    region D P d j ⊆ P.normalization :=
  P.factorOrbitScalarRegion_subset_normalization (scalars D P d j)
    (scalars_ne_zero D P d j) (scalars_norm_le_one D P d j)

omit [Fact p.Prime] [Fintype ι] in
theorem scalars_eq_one_of_not_bad (d : ι) (j : ℕ) (hp : p ∉ badChars D) :
    scalars D P d j = 1 := by
  have hroot : vbadQrootAt D (P.place d) = 1 :=
    vbadQrootAt_eq_one_of_residueChar_not_mem_badChars D _
      (by rw [P.residueChar_eq]; exact hp)
  simp [scalars, hroot]

omit [Fintype ι] in
theorem scaleElt_eq_one_of_not_bad (d : ι) (j : ℕ) (hp : p ∉ badChars D) :
    scaleElt D P d j = 1 := by
  unfold scaleElt
  rw [scalars_eq_one_of_not_bad D P d j hp]
  rfl

theorem region_eq_normalization_of_not_bad (d : ι) (j : ℕ) (hp : p ∉ badChars D) :
    region D P d j = (P.normalization : Set P.Tensor) := by
  rw [region_eq_orbit_principalRegion, scaleElt_eq_one_of_not_bad D P d j hp]
  have hone : P.principalRegion 1 = (P.normalization : Set P.Tensor) := by
    simp [LocalCompletion.Packet.principalRegion]
  rw [hone, P.factorIndeterminacyOrbit_normalization]

omit [Fact p.Prime] [Fintype ι] in
theorem distinguished_ordp_eq_of_liesOver (d : ι) (j : ℕ)
    {w : NumberField.FinitePlace D.F}
    (hvw : Ideal.LiesOver (P.place d).maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    Arithmetic.ordp (P.place d) (scalars D P d j d) =
      ((j ^ 2 : ℕ) : ℝ) * ((D.prime.qOrder w hw : ℝ) /
        (2 * (D.prime.ℓ : ℝ) * Arithmetic.ramIdx w)) := by
  rw [scalars_distinguished, Arithmetic.ordp_pow,
    vbadQrootAt_ordp_eq_of_liesOver D hvw hw]

end
end JoshiTeich.Act1Scene1.IutInitialThetaFiniteFactorRegion
