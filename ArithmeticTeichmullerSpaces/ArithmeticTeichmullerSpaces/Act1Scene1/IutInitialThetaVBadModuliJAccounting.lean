import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRepresentativeBound
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaModuliJAccounting

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-MODULI-J-ACCOUNTING
source: actual VBad and its full base pullback, actual Tate j-log terms and
complete moduli fibres; canonical contraction identifies the selected support.
fidelity: regroups the actual reference q-pilot exactly on actual VBad moduli
places. No reverse full-support coverage or independent fibre certificate is
assumed. Paper representatives and theta-volume remain separate obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def iutInitialThetaVBadModuliFinset :
    Finset (NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :=
  (iutInitialThetaOddModSupportFinset D).filter (fun v => v ∈ D.VBad)

theorem mem_iutInitialThetaVBadModuliFinset_iff
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
    v ∈ iutInitialThetaVBadModuliFinset D ↔ v ∈ D.VBad := by
  rw [iutInitialThetaVBadModuliFinset, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hv
    exact ⟨(iutInitialThetaOddModSupport_finite D).mem_toFinset.mpr
      (iutInitialThetaVBad_subset_VBadOdd D hv), hv⟩

theorem iutInitialThetaReferenceBaseModuliFiber_eq
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutInitialThetaVBadModuliFinset D) :
    (IutTorsionQRootSource.iutInitialThetaQPilotData D).badFinset.filter
        (fun w => iutPlaceUnder (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) w = v) =
      iutInitialThetaBaseModuliFiber D v := by
  let Q := IutTorsionQRootSource.iutInitialThetaQPilotData D
  have hvFull : v ∈ iutInitialThetaOddModSupportFinset D := (Finset.mem_filter.mp hv).1
  have hvBad := (mem_iutInitialThetaVBadModuliFinset_iff D v).mp hv
  ext w
  rw [Finset.mem_filter, mem_iutInitialThetaBaseModuliFiber_iff D v hvFull w]
  constructor
  · rintro ⟨hw, hunder⟩
    rw [← hunder]
    exact iutPlaceUnder_liesOver w
  · intro hwv
    have hwQ : w ∈ Q.badFinset := (Set.ext_iff.mp Q.badFinset_spec w).mpr ⟨v, hvBad, hwv⟩
    exact ⟨hwQ, (iutPlaceUnder_eq_of_liesOver hwv).symm⟩

theorem iutInitialThetaReferenceAbsLogQ_eq_baseJLogSum :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) =
      (∑ w : (IutTorsionQRootSource.iutInitialThetaQPilotData D).badFinset,
        Real.log ‖NumberField.FinitePlace.embedding w.1.maximalIdeal D.E.j‖) /
          (2 * (D.prime.ℓ : ℝ) * (Module.finrank ℚ D.F : ℝ)) := by
  let Q := IutTorsionQRootSource.iutInitialThetaQPilotData D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let f : Q.badFinset → B.badFinset := fun w => ⟨w.1, by
    apply (Set.ext_iff.mp B.badFinset_spec w.1).mpr
    exact iutBadPlacesOver_subset_oddMultiplicativeSupport D (Q.mem_bad w.2)⟩
  change (∑ w : Q.badFinset,
      Q.weight w.1 * (D.prime.qOrder w.1 (Q.mem_bad w.2) : ℝ) *
        Real.log (JoshiTeich.ReferenceIut.residueChar w.1)) / (2 * (D.prime.ℓ : ℝ)) = _
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w hw
  calc
    _ = iutInitialThetaBaseQPilotLogTerm D (f w) := by
      unfold iutInitialThetaBaseQPilotLogTerm
      rw [iutInitialThetaOddSupportBaseQPilotSource_qOrder_eq_admissiblePrime D (f w)
        (Q.mem_bad w.2)]
      change Arithmetic.qPilotWeight w.1 * (D.prime.qOrder w.1 (Q.mem_bad w.2) : ℝ) *
        Real.log (Arithmetic.residueChar w.1) / (2 * (D.prime.ℓ : ℝ)) = _
      ring
    _ = _ := iutInitialThetaBaseQPilotLogTerm_eq_jLog D (f w)

theorem iutInitialThetaReferenceAbsLogQ_eq_VBadModuliJLogSum :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) =
      (∑ v ∈ iutInitialThetaVBadModuliFinset D,
        Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal
          (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ :
            ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))‖) /
        (2 * (D.prime.ℓ : ℝ) *
          (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)) := by
  let Q := IutTorsionQRootSource.iutInitialThetaQPilotData D
  let M := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
  let under : NumberField.FinitePlace D.F → NumberField.FinitePlace M := iutPlaceUnder (F := M)
  let L : NumberField.FinitePlace D.F → ℝ :=
    fun w => Real.log ‖NumberField.FinitePlace.embedding w.maximalIdeal D.E.j‖
  have hmaps : ∀ w ∈ Q.badFinset, under w ∈ iutInitialThetaVBadModuliFinset D := by
    intro w hw
    rcases Q.mem_bad hw with ⟨v, hv, hwv⟩
    have hunder : under w = v := (iutPlaceUnder_eq_of_liesOver hwv).symm
    rw [hunder]
    exact (mem_iutInitialThetaVBadModuliFinset_iff D v).mpr hv
  have hgroup : (∑ v ∈ iutInitialThetaVBadModuliFinset D,
      ∑ w ∈ iutInitialThetaBaseModuliFiber D v, L w) = ∑ w ∈ Q.badFinset, L w := by
    calc
      _ = ∑ v ∈ iutInitialThetaVBadModuliFinset D,
          ∑ w ∈ Q.badFinset.filter (fun w => under w = v), L w := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [iutInitialThetaReferenceBaseModuliFiber_eq D v hv]
      _ = _ := Finset.sum_fiberwise_of_maps_to hmaps L
  have hsubtype : (∑ w : Q.badFinset, L w.1) = ∑ w ∈ Q.badFinset, L w :=
    Finset.sum_coe_sort (s := Q.badFinset) (f := L)
  rw [iutInitialThetaReferenceAbsLogQ_eq_baseJLogSum]
  change (∑ w : Q.badFinset, L w.1) /
    (2 * (D.prime.ℓ : ℝ) * (Module.finrank ℚ D.F : ℝ)) = _
  rw [hsubtype, ← hgroup, Finset.sum_div]
  calc
    _ = ∑ v ∈ iutInitialThetaVBadModuliFinset D,
        Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal
          (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ : M)‖ /
          (2 * (D.prime.ℓ : ℝ) * (Module.finrank ℚ M : ℝ)) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hf := iutInitialThetaBaseModuliFiber_normalized_jLog D v (Finset.mem_filter.mp hv).1
      change (∑ w ∈ iutInitialThetaBaseModuliFiber D v, L w) /
        (2 * (D.prime.ℓ : ℝ) * (Module.finrank ℚ D.F : ℝ)) = _
      calc
        _ = ((∑ w ∈ iutInitialThetaBaseModuliFiber D v, L w) /
            (Module.finrank ℚ D.F : ℝ)) / (2 * (D.prime.ℓ : ℝ)) := by ring
        _ = _ := by
          dsimp only [L]
          rw [hf]
          ring
    _ = _ := (Finset.sum_div _ _ _).symm

end
end JoshiTeich.Act1Scene1
