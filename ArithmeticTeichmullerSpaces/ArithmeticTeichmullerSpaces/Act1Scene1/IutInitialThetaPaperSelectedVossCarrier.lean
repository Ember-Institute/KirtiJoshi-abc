import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperVossPrimeCarrier
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRootAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSectionRepresentative

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open JoshiTeich.ReferenceIut
open NumberField
open scoped Classical

universe u
noncomputable section

variable {AG : AnabelianGeometry.{u}}
variable {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG)

/-!
source-id: JT-SCENE1-PAPER-SELECTED-VOSS-CARRIER-20261108
source: Joshi III `ss:theta-data-fixing2` and `ss:val-sets-defn` (1030--1055):
the chosen valuation section, `underline V^oss`, and its residue-characteristic
fibers; IUT I Definition 3.1(e)'s `ValuationSection`.
fidelity: defines the paper-selected carrier from the section carried by the
same `InitialThetaData` and the local TateStructure odd-semistable predicate.
boundary: this is tied to the supplied InitialThetaData section. It does not
construct an independently chosen paper `L'` representative system, prove full
VBad coverage, or identify an independently supplied Scene1 link.
-/

def iutInitialThetaPaperSelectedValuationCarrier : Set (Place ↥D.prime.torsionField) :=
  D.localData.sect.V

def iutInitialThetaPaperOddSemistableCarrier : Set (Place ↥D.prime.torsionField) :=
  (fun w : FinitePlace ↥D.prime.torsionField => Place.finite w) ''
    iutInitialThetaOddSemistablePlaces D

def iutInitialThetaPaperSelectedVossCarrier : Set (Place ↥D.prime.torsionField) :=
  iutInitialThetaPaperSelectedValuationCarrier D ∩
    iutInitialThetaPaperOddSemistableCarrier D

def iutInitialThetaPaperSelectedVossAtPrime (p : ℕ) :
    Set (Place ↥D.prime.torsionField) :=
  (fun w : FinitePlace ↥D.prime.torsionField => Place.finite w) ''
    iutInitialThetaSectionVossAtPrime D p

theorem paperSelectedVoss_finite_mem_iff_sectionVoss
    (w : FinitePlace ↥D.prime.torsionField) :
    Place.finite w ∈ iutInitialThetaPaperSelectedVossCarrier D ↔
      w ∈ iutInitialThetaSectionVoss D := by
  constructor
  · intro hw
    rcases hw with ⟨hwV, hwOdd⟩
    rcases hwV with ⟨v, hv⟩
    cases v with
    | inl v =>
        change Place.finite (D.localData.sect.sectFin v) = Place.finite w at hv
        have hv' := Sum.inl.inj hv
        refine ⟨⟨v, hv'⟩, ?_⟩
        rcases hwOdd with ⟨w', hw', hEq⟩
        have hwEq : w' = w := Sum.inl.inj hEq
        simpa [hwEq] using hw'
    | inr v =>
        change Place.infinite (D.localData.sect.sectInf v) = Place.finite w at hv
        cases hv
  · intro hw
    rcases hw with ⟨hwRep, hwOdd⟩
    rcases hwRep with ⟨v, hv⟩
    refine ⟨⟨Sum.inl v, ?_⟩, ⟨w, hwOdd, rfl⟩⟩
    change Place.finite (D.localData.sect.sectFin v) = Place.finite w
    exact congrArg Place.finite hv

theorem paperSelectedVoss_infinite_mem_false
    (w : InfinitePlace ↥D.prime.torsionField) :
    Place.infinite w ∉ iutInitialThetaPaperSelectedVossCarrier D := by
  intro hw
  rcases hw.2 with ⟨v, _, hEq⟩
  cases hEq

theorem paperSelectedVossCarrier_eq_finiteImage :
    iutInitialThetaPaperSelectedVossCarrier D =
      (fun w : FinitePlace ↥D.prime.torsionField => Place.finite w) ''
        iutInitialThetaSectionVoss D := by
  ext w
  cases w with
  | inl v =>
      change Place.finite v ∈ iutInitialThetaPaperSelectedVossCarrier D ↔
        Place.finite v ∈ (fun w : FinitePlace ↥D.prime.torsionField =>
          Place.finite w) '' iutInitialThetaSectionVoss D
      rw [paperSelectedVoss_finite_mem_iff_sectionVoss D]
      simp only [Set.mem_image]
      constructor
      · intro hv
        exact ⟨v, hv, rfl⟩
      · rintro ⟨w, hw, hEq⟩
        have hwEq : w = v := Sum.inl.inj hEq
        simpa [hwEq] using hw
  | inr v =>
      constructor
      · intro hw
        rcases hw.2 with ⟨w, _, hEq⟩
        cases hEq
      · intro hw
        rcases hw with ⟨w, _, hEq⟩
        cases hEq

theorem paperSelectedVossCarrier_finite :
    (iutInitialThetaPaperSelectedVossCarrier D).Finite := by
  rw [paperSelectedVossCarrier_eq_finiteImage]
  exact (iutInitialThetaSectionVoss_finite D).image Place.finite

theorem paperSelectedVossAtPrime_subset :
    iutInitialThetaPaperSelectedVossAtPrime D p ⊆
      iutInitialThetaPaperSelectedVossCarrier D := by
  rintro w ⟨v, hv, rfl⟩
  exact (paperSelectedVoss_finite_mem_iff_sectionVoss D v).mpr hv.1

theorem selectedQRootSource_image_eq_paperSelectedVossCarrier :
    (fun s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset =>
      Place.finite s.1) '' iutInitialThetaOddSupportSelectedQRootSourcePlaces D =
      iutInitialThetaPaperSelectedVossCarrier D := by
  rw [paperSelectedVossCarrier_eq_finiteImage]
  calc
    (fun s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset =>
        Place.finite s.1) '' iutInitialThetaOddSupportSelectedQRootSourcePlaces D =
      (fun w : FinitePlace ↥D.prime.torsionField => Place.finite w) ''
        ((fun s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset =>
          s.1) '' iutInitialThetaOddSupportSelectedQRootSourcePlaces D) := by
            rw [Set.image_image]
    _ = (fun w : FinitePlace ↥D.prime.torsionField => Place.finite w) ''
        iutInitialThetaSectionVoss D := by
          rw [iutInitialThetaOddSupportSelectedQRootSourcePlaces_image_eq_sectionVoss D]

theorem vbadSectionRepresentative_mem_paperSelectedVossCarrier
    (v : iutInitialThetaVBadModuliFinset D) :
    Place.finite (iutInitialThetaVBadSectionRepresentative D v) ∈
      iutInitialThetaPaperSelectedVossCarrier D := by
  rw [paperSelectedVoss_finite_mem_iff_sectionVoss D]
  exact iutInitialThetaVBadSectionRepresentative_mem_sectionVoss D v

end
end JoshiTeich.Act1Scene1
