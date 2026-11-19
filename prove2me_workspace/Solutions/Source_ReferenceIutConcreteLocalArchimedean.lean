/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/LocalConstruct/Archimedean.lean,
  Iut/Concrete/LocalConstruct/ArchLogShell.lean,
  Iut/Concrete/LocalConstruct/Volume.lean, Iut/Concrete/LocalConstruct/Admissible.lean,
  Iut/Concrete/LocalConstruct/ThetaAdmissible.lean
-/
import Solutions.Source_ReferenceIutConcreteLocalPacket
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalArchimedeanTensorRadialHull
import Mathlib.FieldTheory.Fixed

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open NumberField MeasureTheory
open scoped ENNReal Pointwise

open JoshiTeich.Act1Scene1

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]
variable (c : ι → Place K)

abbrev archTuple : ι → InfinitePlace K := fun j => archPlace K (c j)

/-- The projective unit ball of the archimedean tensor packet. -/
def archIntegral : Set (Tensor K .infinite c) := LocalArchimedean.archIntegral (archTuple c)

theorem one_mem_archIntegral : (1 : Tensor K .infinite c) ∈ archIntegral c :=
  LocalArchimedean.one_mem_archIntegral (archTuple c)

theorem isCompact_archIntegral : IsCompact (archIntegral c) :=
  LocalArchimedean.isCompact_archIntegral (archTuple c)

/-- The additive Haar measure normalized on the archimedean integral structure. -/
def archHaar : Measure (Tensor K .infinite c) := LocalArchimedean.normalizedHaar (archTuple c)

instance archHaar_isAddHaarMeasure : (archHaar c).IsAddHaarMeasure :=
  LocalArchimedean.normalizedHaar_isAddHaarMeasure (archTuple c)

theorem archHaar_archIntegral : archHaar c (archIntegral c) = 1 :=
  LocalArchimedean.normalizedHaar_archIntegral (archTuple c)

/-- The logarithm of the normalized Haar measure divided by the real tensor dimension. -/
def archComponentVol : Set (Tensor K .infinite c) → ℝ :=
  LocalArchimedean.normalizationLogVolume (archTuple c)

theorem archComponentVol_integral : archComponentVol c (archIntegral c) = 0 :=
  LocalArchimedean.normalizationLogVolume_archIntegral (archTuple c)

theorem algebraMap_smul_archIntegral (t : ℝ) :
    algebraMap ℝ (Tensor K .infinite c) t • archIntegral c =
      LocalArchimedean.radialRegion (archTuple c) t := by
  change algebraMap ℝ (Tensor K .infinite c) t • archIntegral c = t • archIntegral c
  ext x
  simp only [Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, Algebra.smul_def t y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (Algebra.smul_def t y).symm⟩

theorem archComponentVol_scale (t : ℝ) (ht : 0 < t) :
    archComponentVol c (algebraMap ℝ (Tensor K .infinite c) t • archIntegral c) =
      Real.log t := by
  rw [algebraMap_smul_archIntegral]
  exact LocalArchimedean.normalizationLogVolume_radialRegion (archTuple c) ht

theorem smul_archIntegral_mono (t t' : ℝ) (ht : 0 < t) (htt' : t ≤ t') :
    algebraMap ℝ (Tensor K .infinite c) t • archIntegral c ⊆
      algebraMap ℝ (Tensor K .infinite c) t' • archIntegral c := by
  rw [algebraMap_smul_archIntegral, algebraMap_smul_archIntegral]
  exact LocalArchimedean.radialRegion_mono (archTuple c) ht htt'

/-- Admissible archimedean regions have compact closure and positive finite Haar measure. -/
def archAdmissible : Set (Set (Tensor K .infinite c)) :=
  {S | S.Nonempty ∧ IsCompact (closure S) ∧ MeasurableSet S ∧
    0 < archHaar c S ∧ archHaar c S < ⊤}

theorem archAdmissible_nonempty {S : Set (Tensor K .infinite c)}
    (hS : S ∈ archAdmissible c) : S.Nonempty := hS.1

theorem archAdmissible_relCompact {S : Set (Tensor K .infinite c)}
    (hS : S ∈ archAdmissible c) : IsCompact (closure S) := hS.2.1

private theorem archAdmissible_of_isCompact {S : Set (Tensor K .infinite c)}
    (hS : IsCompact S) (hpos : 0 < archHaar c S) : S ∈ archAdmissible c := by
  have : OpensMeasurableSpace (Tensor K .infinite c) :=
    @BorelSpace.opensMeasurable (LocalArchimedean.Tensor (archTuple c)) _ _
      (LocalArchimedean.tensorBorelSpace (archTuple c))
  refine ⟨LocalArchimedean.nonempty_of_haar_pos (archTuple c) hpos, ?_,
    hS.isClosed.measurableSet, hpos, hS.measure_lt_top⟩
  simpa only [hS.isClosed.closure_eq] using hS

private theorem isCompact_smul_archIntegral (a : Tensor K .infinite c) :
    IsCompact (a • archIntegral c) := by
  change IsCompact ((fun x : Tensor K .infinite c => a * x) '' archIntegral c)
  exact (isCompact_archIntegral c).image (continuous_const.mul continuous_id)

private theorem archHaar_smul_archIntegral_pos (a : Tensor K .infinite c) (ha : IsUnit a) :
    0 < archHaar c (a • archIntegral c) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨r, hr, hball⟩ := LocalArchimedean.exists_ball_subset_archIntegral (archTuple c)
  let e : Tensor K .infinite c ≃ₜ+ Tensor K .infinite c := ContinuousAddEquiv.mulLeft u
  have hopen : IsOpen (e '' Metric.ball 0 r) := e.toHomeomorph.isOpenMap _ Metric.isOpen_ball
  have hne : (e '' Metric.ball 0 r).Nonempty := ⟨e 0, ⟨0, Metric.mem_ball_self hr, rfl⟩⟩
  refine (hopen.measure_pos (archHaar c) hne).trans_le (measure_mono ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hball hx, rfl⟩

theorem archIntegral_admissible : archIntegral c ∈ archAdmissible c :=
  archAdmissible_of_isCompact c (isCompact_archIntegral c)
    (by rw [archHaar_archIntegral]; exact zero_lt_one)

theorem smul_archIntegral_admissible (a : Tensor K .infinite c) (ha : IsUnit a) :
    a • archIntegral c ∈ archAdmissible c :=
  archAdmissible_of_isCompact c (isCompact_smul_archIntegral c a)
    (archHaar_smul_archIntegral_pos c a ha)

theorem archComponentVol_mono (a b : Tensor K .infinite c) (ha : IsUnit a) (_hb : IsUnit b)
    (h : a • archIntegral c ⊆ b • archIntegral c) :
    archComponentVol c (a • archIntegral c) ≤ archComponentVol c (b • archIntegral c) :=
  LocalArchimedean.normalizationLogVolume_mono (archTuple c) h (archHaar_smul_archIntegral_pos c a ha)
    ((isCompact_smul_archIntegral c b).measure_lt_top (μ := archHaar c)).ne

/-- The least positive radial scaling containing an admissible archimedean region. -/
theorem exists_leastHull_infinite {S : Set (Tensor K .infinite c)}
    (hS : S ∈ archAdmissible c) :
    ∃ t : ℝ, 0 < t ∧ S ⊆ algebraMap ℝ (Tensor K .infinite c) t • archIntegral c ∧
      ∀ t' : ℝ, 0 < t' → S ⊆ algebraMap ℝ (Tensor K .infinite c) t' • archIntegral c →
        t ≤ t' := by
  have hbound : Bornology.IsBounded S := hS.2.1.isBounded.subset subset_closure
  have hpos : 0 < LocalArchimedean.normalizedHaar (archTuple c) S := hS.2.2.2.1
  refine ⟨LocalArchimedean.hullRadius (archTuple c) S, LocalArchimedean.hullRadius_pos (archTuple c) hbound hpos, ?_, ?_⟩
  · rw [algebraMap_smul_archIntegral]
    exact LocalArchimedean.subset_radialHull (archTuple c) hbound hpos
  · intro t' ht' h
    rw [algebraMap_smul_archIntegral] at h
    exact LocalArchimedean.hullRadius_le_of_subset_radialRegion (archTuple c) hpos ht' h

/-- The archimedean log-shell scales the projective unit ball by π to the packet length. -/
def archLogShell : Set (Tensor K .infinite c) := LocalArchimedean.archLogShell (archTuple c)

theorem archHaar_archLogShell :
    archHaar c (archLogShell c) =
      ENNReal.ofReal ((Real.pi ^ Fintype.card ι) ^ Module.finrank ℝ (Tensor K .infinite c)) :=
  LocalArchimedean.normalizedHaar_archLogShell (archTuple c)

theorem archComponentVol_archLogShell :
    archComponentVol c (archLogShell c) = (Fintype.card ι : ℝ) * Real.log Real.pi :=
  LocalArchimedean.normalizationLogVolume_archLogShell (archTuple c)

theorem isCompact_archLogShell : IsCompact (archLogShell c) :=
  LocalArchimedean.isCompact_archLogShell (archTuple c)

theorem isCompact_closure_archLogShell : IsCompact (closure (archLogShell c)) := by
  rw [(isCompact_archLogShell c).isClosed.closure_eq]
  exact isCompact_archLogShell c

theorem archLogShell_eq_smul_archIntegral :
    archLogShell c = algebraMap ℝ (Tensor K .infinite c) (Real.pi ^ Fintype.card ι) •
      archIntegral c := by
  rw [algebraMap_smul_archIntegral]
  rfl

/-- Indeterminacies are precisely the tensor maps induced by the factor automorphisms. -/
def archIndAut : Set (Tensor K .infinite c → Tensor K .infinite c) :=
  {φ | ∃ σ : ∀ j, ArchFactor K (c j) ≃ₐ[ℝ] ArchFactor K (c j),
    φ = ⇑(LocalArchimedean.factorTensorAut (archTuple c) σ)}

theorem id_mem_archIndAut : id ∈ archIndAut c :=
  ⟨fun _ => AlgEquiv.refl, funext fun x => (LocalArchimedean.factorTensorAut_refl (archTuple c) x).symm⟩

theorem archIndAut_logShell :
    ∀ φ ∈ archIndAut c, φ '' archLogShell c ⊆ archLogShell c := by
  rintro _ ⟨σ, rfl⟩
  exact LocalArchimedean.factorTensorAut_image_archLogShell_subset (archTuple c) σ

theorem prop15 (φ : Tensor K .infinite c → Tensor K .infinite c) (hφ : φ ∈ archIndAut c) :
    φ '' archLogShell c ⊆ algebraMap ℝ (Tensor K .infinite c) (Real.pi ^ Fintype.card ι) •
      archIntegral c :=
  (archIndAut_logShell c φ hφ).trans (archLogShell_eq_smul_archIntegral c).le

private theorem finite_archFactorAlgEquiv (v : Place K) :
    Finite (ArchFactor K v ≃ₐ[ℝ] ArchFactor K v) := by
  by_cases h : (archPlace K v).IsReal
  · let e : ArchFactor K v ≃ₐ[ℝ] ℝ :=
      (ULift.algEquiv : ArchFactor K v ≃ₐ[ℝ] LocalArchimedean.archField (archPlace K v)).trans
        ((Subalgebra.equivOfEq _ _ (archField_of_isReal K h)).trans (Algebra.botEquiv ℝ ℂ))
    exact Finite.of_equiv _ (AlgEquiv.autCongr e).symm.toEquiv
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    let e : ArchFactor K v ≃ₐ[ℝ] ℂ :=
      (ULift.algEquiv : ArchFactor K v ≃ₐ[ℝ] LocalArchimedean.archField (archPlace K v)).trans
        ((Subalgebra.equivOfEq _ _ (archField_of_isComplex K hc)).trans Subalgebra.topEquiv)
    exact Finite.of_equiv _ (AlgEquiv.autCongr e).symm.toEquiv

private theorem archIndAutOrbit_eq_factorOrbit (S : Set (Tensor K .infinite c)) :
    (⋃ φ ∈ archIndAut c, φ '' S) = LocalArchimedean.factorOrbit (archTuple c) S := by
  ext x
  constructor
  · intro hx
    obtain ⟨φ, ⟨σ, rfl⟩, hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion.mpr ⟨σ, hx⟩
  · intro hx
    obtain ⟨σ, hx⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion₂.mpr ⟨_, ⟨σ, rfl⟩, hx⟩

theorem thetaShell_admissible_infinite :
    (⋃ φ ∈ archIndAut c, φ '' archLogShell c) ∈ archAdmissible c := by
  rw [archIndAutOrbit_eq_factorOrbit]
  change LocalArchimedean.factorOrbit (archTuple c) (LocalArchimedean.archLogShell (archTuple c)) ∈ archAdmissible c
  rw [LocalArchimedean.factorOrbit_archLogShell]
  exact archAdmissible_of_isCompact c (isCompact_archLogShell c)
    (LocalArchimedean.archLogShell_haar_pos_lt_top (archTuple c)).1

theorem theta_admissible_infinite (a : Tensor K .infinite c) (ha : IsUnit a) :
    (⋃ φ ∈ archIndAut c, φ '' (a • archIntegral c)) ∈ archAdmissible c := by
  have : ∀ j : ι, Finite
      (LocalArchimedean.Factor (archTuple c j) ≃ₐ[ℝ] LocalArchimedean.Factor (archTuple c j)) :=
    fun j => finite_archFactorAlgEquiv (c j)
  let S := a • archIntegral c
  have hS : IsCompact S := isCompact_smul_archIntegral c a
  have hOrbit : IsCompact (LocalArchimedean.factorOrbit (archTuple c) S) :=
    isCompact_iUnion fun σ => hS.image
      (LocalArchimedean.factorTensorAut (archTuple c) σ).toLinearMap.continuous_of_finiteDimensional
  have hsub : S ⊆ LocalArchimedean.factorOrbit (archTuple c) S := fun x hx =>
    Set.mem_iUnion.mpr
      ⟨fun _ => AlgEquiv.refl, ⟨x, hx, LocalArchimedean.factorTensorAut_refl (archTuple c) x⟩⟩
  rw [archIndAutOrbit_eq_factorOrbit]
  exact archAdmissible_of_isCompact c hOrbit
    ((archHaar_smul_archIntegral_pos c a ha).trans_le (measure_mono hsub))

end

end AbcAdaptation.Reference.Iut.LocalConstruct
