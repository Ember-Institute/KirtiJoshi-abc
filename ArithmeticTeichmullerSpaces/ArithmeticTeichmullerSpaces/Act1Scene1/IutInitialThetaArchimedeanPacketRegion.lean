import ArithmeticTeichmullerSpaces.Act1Scene1.LocalArchimedeanCompletionModel
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalArchimedeanTensorHaar
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
source-id: JT-SCENE1-INITIAL-THETA-ARCHIMEDEAN-PACKET
source: reference `Concrete/Container.lean`, infinite fiber, weight and
packet product; `Concrete/ThetaRegion.lean`, `thetaInfinite`; IUT IV
Proposition 1.5 and Joshi III `th:thetam-construction`.
fidelity: at the actual torsion field's complete infinite-place fiber,
constructs every capsule tuple and the product of the full factor orbits
of pi^|I| B_I. Proves compactness, positive finite product Haar measure,
weight mass one, and exact packet/standard-procession log contributions.
Actual completion-to-factor equivalences are supplied by the same places.
No final RHSData, paper representative weights or theta locus is identified.
Original consumer proofs; no reference source code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaArchimedeanPacketRegion

open NumberField MeasureTheory
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

abbrev Tuple (j : ℕ) := Fin (j + 1) → InfinitePlace ↥D.prime.torsionField
abbrev Total (j : ℕ) := ∀ c : Tuple D j, LocalArchimedean.Tensor c

def completionEquiv (j : ℕ) (c : Tuple D j) (i : Fin (j + 1)) :
    (c i).Completion ≃+* LocalArchimedean.Factor (c i) :=
  LocalArchimedean.completionModelEquiv (c i)

def region (j : ℕ) : Set (Total D j) := Set.pi Set.univ fun c =>
  LocalArchimedean.factorOrbit c (LocalArchimedean.archLogShell c)

def integralRegion (j : ℕ) : Set (Total D j) :=
  Set.pi Set.univ fun c => LocalArchimedean.archIntegral c

theorem region_eq_shell_product (j : ℕ) :
    region D j = Set.pi Set.univ (fun c => LocalArchimedean.archLogShell c) := by
  simp only [region, LocalArchimedean.factorOrbit_archLogShell]

theorem region_isCompact (j : ℕ) : IsCompact (region D j) :=
  isCompact_univ_pi fun c => LocalArchimedean.isCompact_factorOrbit_archLogShell c

def productMeasure (j : ℕ) : Measure (Total D j) :=
  Measure.pi fun c => LocalArchimedean.normalizedHaar c

theorem productMeasure_integralRegion (j : ℕ) :
    productMeasure D j (integralRegion D j) = 1 := by
  change Measure.pi _ (Set.pi Set.univ _) = 1
  rw [Measure.pi_pi]
  simp only [LocalArchimedean.normalizedHaar_archIntegral, Finset.prod_const_one]

theorem productMeasure_region (j : ℕ) :
    productMeasure D j (region D j) =
      ∏ c : Tuple D j, LocalArchimedean.normalizedHaar c (LocalArchimedean.archLogShell c) := by
  rw [region_eq_shell_product]
  exact Measure.pi_pi _ _

theorem productMeasure_region_pos_lt_top (j : ℕ) :
    0 < productMeasure D j (region D j) ∧ productMeasure D j (region D j) < ⊤ := by
  rw [productMeasure_region]
  constructor
  · apply bot_lt_iff_ne_bot.mpr
    exact Finset.prod_ne_zero_iff.mpr fun c _ =>
      (LocalArchimedean.archLogShell_haar_pos_lt_top c).1.ne'
  · apply ENNReal.prod_lt_top
    intro c _
    exact (LocalArchimedean.archLogShell_haar_pos_lt_top c).2

def placeWeight (v : InfinitePlace ↥D.prime.torsionField) : ℝ :=
  (v.mult : ℝ) / Module.finrank ℚ ↥D.prime.torsionField

theorem placeWeight_pos (v : InfinitePlace ↥D.prime.torsionField) : 0 < placeWeight D v :=
  div_pos (by exact_mod_cast v.mult_pos) (by exact_mod_cast Module.finrank_pos)

theorem placeWeight_sum_one : ∑ v, placeWeight D v = 1 := by
  simp only [placeWeight, ← Finset.sum_div, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  exact div_self (by exact_mod_cast (Module.finrank_pos (R := ℚ)
    (M := ↥D.prime.torsionField)).ne')

def tupleWeight (j : ℕ) (c : Tuple D j) : ℝ := ∏ i, placeWeight D (c i)

theorem tupleWeight_sum_one (j : ℕ) : ∑ c : Tuple D j, tupleWeight D j c = 1 := by
  rw [show (fun c => tupleWeight D j c) =
      (fun c : Tuple D j => ∏ i, placeWeight D (c i)) from rfl, ← Fintype.prod_sum]
  simp only [placeWeight_sum_one, Finset.prod_const_one]

def packetLogVolume (j : ℕ) : ℝ := ∑ c : Tuple D j, tupleWeight D j c *
  LocalArchimedean.normalizationLogVolume c
    (LocalArchimedean.factorOrbit c (LocalArchimedean.archLogShell c))

theorem packetLogVolume_eq (j : ℕ) :
    packetLogVolume D j = ((j + 1 : ℕ) : ℝ) * Real.log Real.pi := by
  unfold packetLogVolume
  simp only [LocalArchimedean.factorOrbit_archLogShell,
    LocalArchimedean.normalizationLogVolume_archLogShell, Fintype.card_fin]
  rw [← Finset.sum_mul, tupleWeight_sum_one, one_mul]

theorem packetLogVolume_nonneg (j : ℕ) : 0 ≤ packetLogVolume D j := by
  rw [packetLogVolume_eq]
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith [Real.two_le_pi]))

def processionLogVolume : ℝ :=
  (∑ i : Fin ((D.prime.ℓ - 1) / 2), packetLogVolume D (i.val + 1)) /
    (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ)

theorem processionLogVolume_eq : processionLogVolume D =
    (∑ i : Fin ((D.prime.ℓ - 1) / 2), ((i.val + 2 : ℕ) : ℝ) * Real.log Real.pi) /
      (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ) := by
  simp only [processionLogVolume, packetLogVolume_eq, Nat.add_assoc]

theorem processionLogVolume_nonneg : 0 ≤ processionLogVolume D := by
  unfold processionLogVolume
  exact div_nonneg (Finset.sum_nonneg fun i _ => packetLogVolume_nonneg D (i.val + 1))
    (Nat.cast_nonneg _)

end
end JoshiTeich.Act1Scene1.IutInitialThetaArchimedeanPacketRegion
