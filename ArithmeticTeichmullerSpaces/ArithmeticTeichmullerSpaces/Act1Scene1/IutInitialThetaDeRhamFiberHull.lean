import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionDeRhamEvaluation
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorPointOrbitHull

/-!
source-id: JT-SCENE1-INITIAL-THETA-DE-RHAM-FIBER-HULL
source: Joshi II pr:teichmuller-lift-A (kernel translates), local pilot
(940--1013); Joshi III principal hull and witness construction (3568--3631);
reference ThetaRegion.scaleElt/thetaFinite and images-before-hull ordering.
fidelity: the full actual de Rham theta fiber evaluates to the original
torsion q-root power. Its tensor image is one point; its finite factor orbit
and normalization hull equal the existing actual point orbit and least hull.
Finite point orbits have zero Haar; positive Haar is proved for their hull.
No full paper theta-locus, Tate-module or all-Ind1--Ind3 identity is asserted.
Original proofs, no reference-engine copy; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull

open JoshiTeich.Prologue InitialThetaDeRhamCompletion
open InitialThetaTorsionDeRhamEvaluation
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (v : NumberField.FinitePlace ↥D.prime.torsionField)
variable (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

def fiber (j : ℕ) : Set (source D w v hvw) :=
  {a | theta D w a = InitialThetaTorsionDeRhamPilot.rootImage D w v hvw ^ (j ^ 2)}

theorem mem_fiber_iff (j : ℕ) (a : source D w v hvw) :
    a ∈ fiber D w v hvw j ↔
      evaluation D w v hvw a = IutInitialThetaQRootFamily.qrootAt D v ^ (j ^ 2) := by
  rw [← (InitialThetaTorsionDeRhamPilot.embedding_injective D w v hvw).eq_iff,
    embedding_evaluation, map_pow]
  rfl

theorem pilot_mem_fiber (j : ℕ) : pilot D w v hvw j ∈ fiber D w v hvw j :=
  (mem_fiber_iff D w v hvw j _).mpr (evaluation_pilot D w v hvw j)

theorem fiber_nonempty (j : ℕ) : (fiber D w v hvw j).Nonempty :=
  ⟨pilot D w v hvw j, pilot_mem_fiber D w v hvw j⟩

theorem fiber_eq_kernel_translate (j : ℕ) (a : source D w v hvw) :
    a ∈ fiber D w v hvw j ↔ ∃ b : Ring D w,
      (a : Ring D w) = primitive D w * b + InitialThetaTorsionDeRhamPilot.pilot D w v hvw j :=
  (mem_fiber_iff D w v hvw j a).trans (pilot_fiber D w v hvw j a)

theorem evaluation_image_fiber (j : ℕ) :
    evaluation D w v hvw '' fiber D w v hvw j =
      {IutInitialThetaQRootFamily.qrootAt D v ^ (j ^ 2)} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact (mem_fiber_iff D w v hvw j a).mp ha
  · rintro x rfl
    exact ⟨pilot D w v hvw j, pilot_mem_fiber D w v hvw j, evaluation_pilot D w v hvw j⟩

section Tensor
variable {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (P : LocalCompletion.Packet ↥D.prime.torsionField p ι) (d : ι)
variable (hvd : Ideal.LiesOver (P.place d).maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal)
local instance factorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  LocalCompletion.padicAlgebra (P.residueChar_eq i)
local instance integralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

def tensorEvaluation : source D w (P.place d) hvd →+* P.Tensor :=
  (PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := fun i => P.Factor i) d).toRingHom.comp
    (evaluation D w (P.place d) hvd)

def tensorImage (j : ℕ) : Set P.Tensor :=
  tensorEvaluation D w P d hvd '' fiber D w (P.place d) hvd j

omit [Fintype ι] in
theorem tensorImage_eq_singleton (j : ℕ) : tensorImage D w P d hvd j =
    {IutInitialThetaFiniteFactorRegion.scaleElt D P d j} := by
  have hpoint : tensorEvaluation D w P d hvd (pilot D w (P.place d) hvd j) =
      IutInitialThetaFiniteFactorRegion.scaleElt D P d j := tensorPilot_eq_scaleElt D w P d hvd j
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    change tensorEvaluation D w P d hvd a = _
    rw [← hpoint]
    change PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := fun i => P.Factor i) d
      (evaluation D w (P.place d) hvd a) =
      PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := fun i => P.Factor i) d
        (evaluation D w (P.place d) hvd (pilot D w (P.place d) hvd j))
    rw [(mem_fiber_iff D w (P.place d) hvd j a).mp ha, evaluation_pilot]
  · rintro x rfl
    exact ⟨pilot D w (P.place d) hvd j, pilot_mem_fiber D w (P.place d) hvd j, hpoint⟩

def orbit (j : ℕ) : Set P.Tensor := P.factorIndeterminacyOrbit (tensorImage D w P d hvd j)

theorem orbit_eq_existing (j : ℕ) : orbit D w P d hvd j =
    P.factorPointOrbit (IutInitialThetaFiniteFactorRegion.scaleElt D P d j) := by
  rw [orbit, tensorImage_eq_singleton]
  rfl

theorem orbit_finite (j : ℕ) : (orbit D w P d hvd j).Finite := by
  rw [orbit_eq_existing]
  exact P.factorPointOrbit_finite _

theorem orbit_haar_eq_zero (j : ℕ) : P.normalizationHaar (orbit D w P d hvd j) = 0 := by
  rw [orbit_eq_existing]
  exact P.factorPointOrbit_haar_eq_zero _

theorem orbit_subset_region (j : ℕ) : orbit D w P d hvd j ⊆
    IutInitialThetaFiniteFactorRegion.region D P d j := by
  rw [orbit_eq_existing, IutInitialThetaFiniteFactorRegion.region_eq_orbit_principalRegion]
  exact P.factorPointOrbit_subset_thickOrbit _

def hull (j : ℕ) : Submodule P.normalization P.Tensor :=
  P.normalizationHull (orbit D w P d hvd j)

theorem hull_eq_existing (j : ℕ) : (hull D w P d hvd j : Set P.Tensor) =
    P.leastHull (IutInitialThetaFiniteFactorRegion.region D P d j)
      (IutInitialThetaFiniteFactorRegion.region_isCompact D P d j).isBounded
      (IutInitialThetaFiniteFactorRegion.region_haar_pos_lt_top D P d j).1 := by
  rw [hull, orbit_eq_existing]
  exact P.normalizationHull_purePointOrbit_eq_leastHull
    (IutInitialThetaFiniteFactorRegion.scalars D P d j)
    (IutInitialThetaFiniteFactorRegion.scalars_ne_zero D P d j)

theorem hull_isCompact (j : ℕ) : IsCompact (hull D w P d hvd j : Set P.Tensor) := by
  rw [hull_eq_existing]
  exact P.leastHull_isCompact _ _ _

theorem hull_haar_pos_lt_top (j : ℕ) :
    0 < P.normalizationHaar (hull D w P d hvd j) ∧
      P.normalizationHaar (hull D w P d hvd j) < ⊤ := by
  rw [hull_eq_existing]
  exact P.leastHull_haar_pos_lt_top _ _ _

theorem region_subset_hull (j : ℕ) :
    IutInitialThetaFiniteFactorRegion.region D P d j ⊆ hull D w P d hvd j := by
  rw [hull, orbit_eq_existing, IutInitialThetaFiniteFactorRegion.region_eq_orbit_principalRegion]
  exact P.thickOrbit_subset_normalizationHull_points _

theorem hull_le_principalRegion_iff (j : ℕ) (b : P.Tensor) :
    (hull D w P d hvd j : Set P.Tensor) ⊆ P.principalRegion b ↔
      orbit D w P d hvd j ⊆ P.principalRegion b :=
  P.normalizationHull_le_iff _ (P.principalNormalizationModule b)

end Tensor
end
end JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull
