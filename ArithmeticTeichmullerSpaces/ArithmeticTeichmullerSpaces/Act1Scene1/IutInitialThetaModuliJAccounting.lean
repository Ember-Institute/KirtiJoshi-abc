import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQPilotJLog

/-!
source-id: JT-SCENE1-INITIAL-THETA-MODULI-J-ACCOUNTING
source: the actual odd moduli support and its complete pullback, canonical
place contraction, and the normalized full-fibre j-log theorem.
fidelity: constructs complete base fibres and regroups the actual full
q-pilot over the finite moduli support. No section coverage or independent
fibre-enumeration certificate is supplied by the caller.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

def iutInitialThetaOddModSupportFinset
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Finset (NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :=
  (iutInitialThetaOddModSupport_finite D).toFinset

def iutInitialThetaBaseModuliFiber
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
    Finset (NumberField.FinitePlace D.F) :=
  (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.filter
    (fun w => iutPlaceUnder (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) w = v)

theorem mem_iutInitialThetaBaseModuliFiber_iff
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutInitialThetaOddModSupportFinset D) (w : NumberField.FinitePlace D.F) :
    w ∈ iutInitialThetaBaseModuliFiber D v ↔
      Ideal.LiesOver w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal := by
  constructor
  · intro hw
    have he := (Finset.mem_filter.mp hw).2
    rw [← he]
    exact iutPlaceUnder_liesOver w
  · intro hwv
    have hvSupport : v ∈ IutOddMultiplicativeModSupport D := by
      rw [iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd D]
      exact (iutInitialThetaOddModSupport_finite D).mem_toFinset.mp hv
    have hwSupport : w ∈ IutOddMultiplicativeSupport D := by
      rw [iutOddMultiplicativeSupport_eq_badPlacesOver_modSupport]
      exact ⟨v, hvSupport, hwv⟩
    have hwFin : w ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset :=
      (Set.ext_iff.mp (iutInitialThetaOddSupportBaseQPilotSource D).badFinset_spec w).mpr hwSupport
    exact Finset.mem_filter.mpr ⟨hwFin, (iutPlaceUnder_eq_of_liesOver hwv).symm⟩

theorem iutInitialThetaBaseModuliFiber_normalized_jLog
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutInitialThetaOddModSupportFinset D) :
    (∑ w ∈ iutInitialThetaBaseModuliFiber D v,
        Real.log ‖NumberField.FinitePlace.embedding w.maximalIdeal D.E.j‖) /
          (Module.finrank ℚ D.F : ℝ) =
      Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal
        (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ :
          ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))‖ /
        (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ) := by
  exact iutInitialThetaModuliJ_normalized_fiber D v (iutInitialThetaBaseModuliFiber D v)
    (mem_iutInitialThetaBaseModuliFiber_iff D v hv)

theorem iutInitialThetaFullBaseQPilotLogSum_eq_moduliJLogSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaFullBaseQPilotLogSum D =
      (∑ v ∈ iutInitialThetaOddModSupportFinset D,
        Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal
          (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ :
            ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))‖) /
        (2 * (D.prime.ℓ : ℝ) *
          (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)) := by
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let M := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
  let under : NumberField.FinitePlace D.F → NumberField.FinitePlace M :=
    iutPlaceUnder (F := M)
  let L : NumberField.FinitePlace D.F → ℝ :=
    fun w => Real.log ‖NumberField.FinitePlace.embedding w.maximalIdeal D.E.j‖
  have hmaps : ∀ w ∈ B.badFinset, under w ∈ iutInitialThetaOddModSupportFinset D := by
    intro w hw
    have hfull := B.mem_badPlaces ⟨w, hw⟩
    change w ∈ IutOddMultiplicativeSupport D at hfull
    rw [iutOddMultiplicativeSupport_eq_badPlacesOver_modSupport D] at hfull
    rcases hfull with ⟨v, hv, hwv⟩
    have hunder : under w = v := (iutPlaceUnder_eq_of_liesOver hwv).symm
    rw [hunder]
    apply (iutInitialThetaOddModSupport_finite D).mem_toFinset.mpr
    rw [← iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd D]
    exact hv
  have hgroup : (∑ v ∈ iutInitialThetaOddModSupportFinset D,
      ∑ w ∈ iutInitialThetaBaseModuliFiber D v, L w) = ∑ w ∈ B.badFinset, L w := by
    exact Finset.sum_fiberwise_of_maps_to hmaps L
  have hsubtype : (∑ w : B.badFinset, L w.1) = ∑ w ∈ B.badFinset, L w := by
    refine Finset.sum_bij (fun w _ => w.1) ?_ ?_ ?_ ?_
    · intro w hw
      exact w.2
    · intro w hw v hv h
      exact Subtype.ext h
    · intro w hw
      exact ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩
    · intro w hw
      rfl
  rw [iutInitialThetaFullBaseQPilotLogSum_eq_jLogSum]
  change (∑ w : B.badFinset, L w.1) / (2 * (D.prime.ℓ : ℝ) * (Module.finrank ℚ D.F : ℝ)) = _
  rw [hsubtype, ← hgroup, Finset.sum_div]
  calc
    _ = ∑ v ∈ iutInitialThetaOddModSupportFinset D,
        Real.log ‖NumberField.FinitePlace.embedding v.maximalIdeal
          (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩ : M)‖ /
            (2 * (D.prime.ℓ : ℝ) * (Module.finrank ℚ M : ℝ)) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hf := iutInitialThetaBaseModuliFiber_normalized_jLog D v hv
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
