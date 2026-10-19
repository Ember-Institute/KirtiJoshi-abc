import ArithmeticTeichmullerSpaces.Act1Scene1.EmbeddedResiduePullback
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionDeRhamPilot
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFiniteFactorRegion

/-!
source-id: JT-SCENE1-INITIAL-THETA-TORSION-DE-RHAM-EVALUATION
source: Joshi II eta_K, Teichmuller lifts and local pilot (932--1013);
reference ThetaRegion.scaleElt/thetaFinite; Joshi III local source and hull.
fidelity: restricts original BDeRhamPlus to residues in the embedded original
torsion completion. Its surjective evaluation lands in that same completion,
and the actual pilot evaluates to the original qrootAt^(j^2). Its distinguished
tensor image is exactly the previously constructed finite-container scaleElt.
This does not identify the full paper theta locus or its indeterminacies.
Original proofs, no reference-engine copy; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation

open JoshiTeich.Prologue InitialThetaDeRhamCompletion InitialThetaTorsionDeRhamPilot
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

def source : Subring (Ring D w) :=
  EmbeddedResiduePullback.source (theta D w) (embedding D w v hvw)

def evaluation : source D w v hvw →+* LocalCompletion.completionAt ↥D.prime.torsionField v :=
  EmbeddedResiduePullback.evaluation (theta D w) (embedding D w v hvw)

theorem embedding_evaluation (x : source D w v hvw) :
    embedding D w v hvw (evaluation D w v hvw x) = theta D w x :=
  EmbeddedResiduePullback.embedding_evaluation _ _ x

theorem evaluation_surjective : Function.Surjective (evaluation D w v hvw) :=
  EmbeddedResiduePullback.surjective _ _ (theta_surjective D w)

theorem kernel_eq_comap : RingHom.ker (evaluation D w v hvw) =
    (RingHom.ker (theta D w)).comap (source D w v hvw).subtype :=
  EmbeddedResiduePullback.kernel _ _

def quotientEquiv : (source D w v hvw ⧸ RingHom.ker (evaluation D w v hvw)) ≃+*
    LocalCompletion.completionAt ↥D.prime.torsionField v :=
  EmbeddedResiduePullback.quotientEquiv _ _ (theta_surjective D w)

def pilot (j : ℕ) : source D w v hvw :=
  ⟨InitialThetaTorsionDeRhamPilot.pilot D w v hvw j, by
    change theta D w _ ∈ (embedding D w v hvw).range
    refine ⟨IutInitialThetaQRootFamily.qrootAt D v ^ (j ^ 2), ?_⟩
    rw [map_pow, InitialThetaTorsionDeRhamPilot.theta_pilot]
    rfl⟩

theorem evaluation_pilot (j : ℕ) : evaluation D w v hvw (pilot D w v hvw j) =
    IutInitialThetaQRootFamily.qrootAt D v ^ (j ^ 2) := by
  apply embedding_injective D w v hvw
  rw [embedding_evaluation, map_pow]
  exact InitialThetaTorsionDeRhamPilot.theta_pilot D w v hvw j

theorem evaluation_pilot_vbad (j : ℕ) : evaluation D w v hvw (pilot D w v hvw j) =
    IutInitialThetaQRootFamily.vbadQrootAt D v ^ (j ^ 2) := by
  rw [IutInitialThetaQRootFamily.vbadQrootAt_eq_qrootAt_of_liesOver D hvw (supported_bad D w)]
  exact evaluation_pilot D w v hvw j

theorem pilot_fiber (j : ℕ) (a : source D w v hvw) :
    evaluation D w v hvw a = IutInitialThetaQRootFamily.qrootAt D v ^ (j ^ 2) ↔
      ∃ b : Ring D w, (a : Ring D w) = primitive D w * b +
        InitialThetaTorsionDeRhamPilot.pilot D w v hvw j := by
  rw [← (embedding_injective D w v hvw).eq_iff, embedding_evaluation, map_pow]
  change theta D w a = rootImage D w v hvw ^ (j ^ 2) ↔ _
  rw [← InitialThetaTorsionDeRhamPilot.theta_pilot D w v hvw j]
  have heq : theta D w a = theta D w (InitialThetaTorsionDeRhamPilot.pilot D w v hvw j) ↔
      (a : Ring D w) - InitialThetaTorsionDeRhamPilot.pilot D w v hvw j ∈
        RingHom.ker (theta D w) := by simp only [RingHom.mem_ker, map_sub, sub_eq_zero]
  rw [heq, kernel_eq_span, Ideal.mem_span_singleton]
  exact exists_congr fun b => sub_eq_iff_eq_add

theorem evaluation_pilot_norm (j : ℕ) :
    ‖evaluation D w v hvw (pilot D w v hvw j)‖ =
      ‖IutInitialThetaQRootFamily.qrootAt D v‖ ^ (j ^ 2) := by
  rw [evaluation_pilot, norm_pow]

section Tensor
variable {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (P : LocalCompletion.Packet ↥D.prime.torsionField p ι) (d : ι)
variable (hvd : Ideal.LiesOver (P.place d).maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal)
local instance factorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  LocalCompletion.padicAlgebra (P.residueChar_eq i)

def tensorPilot (j : ℕ) : P.Tensor :=
  PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := fun i => P.Factor i) d
    (evaluation D w (P.place d) hvd (pilot D w (P.place d) hvd j))

omit [Fintype ι] in
theorem tensorPilot_eq_scaleElt (j : ℕ) : tensorPilot D w P d hvd j =
    IutInitialThetaFiniteFactorRegion.scaleElt D P d j := by
  rw [tensorPilot, evaluation_pilot_vbad, IutInitialThetaFiniteFactorRegion.scaleElt_eq_singleAlgHom]

theorem tensorPilot_mem_region (j : ℕ) : tensorPilot D w P d hvd j ∈
    IutInitialThetaFiniteFactorRegion.region D P d j := by
  rw [tensorPilot_eq_scaleElt]
  exact IutInitialThetaFiniteFactorRegion.scaleElt_mem_region D P d j

end Tensor
end
end JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation
