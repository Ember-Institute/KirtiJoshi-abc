import ArithmeticTeichmullerSpaces.Act1Scene1.Boundary
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootAccounting

/-!
source-id: JT-SCENE1-THETA-LOG-SIGN-AUDIT
source: the existing Scene1 period/log-shell and volume-transfer contracts;
Joshi III, `th:adelic-theta-link` (1139--1154), and the sign discussion before
`cor:cor312` (3634--3650).
fidelity: proves a restriction imposed by the current contracts and compares
it with an actual InitialThetaData q-root.  Ordinary completion norm powers
do not construct the paper's change of untilt valuations.  This audit does
not identify a q-root with an admissible theta lift or change the contracts.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe u

namespace Scene1Input

variable {K O : Type u} [Field K] [NumberField K] [CommRing O]
variable {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- The current transfer convention records a nonnegative log-volume. -/
theorem logVolume_nonneg (S : Scene1Input K O p) :
    0 ≤ S.data.link.logVolume := by
  letI := S.data.link.packetHull.packetFintype
  letI := S.data.link.packetHull.hullFintype
  rw [S.volume_transfer.transferred_volume]
  exact add_nonneg
    (Finset.sum_nonneg fun i _ =>
      (S.input_laws.first_axiom.packet_weight_positive i).le)
    (Finset.sum_nonneg fun i _ =>
      (S.input_laws.first_axiom.hull_weight_positive i).le)

/-- Scaling, the ordinary log-shell sign and nonnegative volume transfer
force the base theta norm to be at least one. -/
theorem one_le_thetaBase_norm (S : Scene1Input K O p) :
    1 ≤ S.data.link.theta.norm S.data.link.thetaBase := by
  classical
  let L := S.data.link
  letI := L.theta.indexFintype
  have hScale := S.adelic_theta_link.theta_scaling
  by_contra h
  have hBase : L.theta.norm L.thetaBase < 1 := lt_of_not_ge h
  have hNormLe (i : L.theta.index) : L.theta.norm i ≤ 1 := by
    rw [hScale.norm_scaling i]
    exact pow_le_one₀ (hScale.norm_positive L.thetaBase).le hBase.le
  have hLogLe (i : L.theta.index) : Real.log (L.theta.norm i) ≤ 0 :=
    Real.log_nonpos (hScale.norm_positive i).le (hNormLe i)
  have hLogBase : Real.log (L.theta.norm L.thetaBase) < 0 :=
    Real.log_neg (hScale.norm_positive L.thetaBase) hBase
  have hSum : (∑ i, Real.log (L.theta.norm i)) < 0 := by
    have hLt := Finset.sum_lt_sum
      (s := Finset.univ) (f := fun i => Real.log (L.theta.norm i))
      (g := fun _ => (0 : ℝ))
      (fun i _ => hLogLe i) ⟨L.thetaBase, Finset.mem_univ _, hLogBase⟩
    simpa using hLt
  have hVolume : L.logVolume = ∑ i, Real.log (L.theta.norm i) := by
    calc
      L.logVolume = ∑ i, L.theta.period i := S.adelic_theta_link.normalization
      _ = ∑ i, Real.log (L.theta.norm i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (S.adelic_theta_link.period_map i).trans (S.theta_lift_log.log_shell i)
  have hNegative : L.logVolume < 0 := by
    rw [hVolume]
    exact hSum
  exact (not_lt_of_ge (S.logVolume_nonneg)) hNegative

end Scene1Input

namespace IutTorsionQRootSource

/-- The actual canonical root belongs to the strict unit ball, as follows
from its root equation and the base Tate parameter's norm. -/
theorem ofInitialThetaDataFromGlobal_qroot_norm_lt_one
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : (ofInitialThetaDataFromGlobal D).badFinset) :
    ‖(ofInitialThetaDataFromGlobal D).qroot v‖ < 1 := by
  let B := IutBaseQPilotSource.ofInitialThetaData D
  let R := ofInitialThetaDataFromGlobal D
  have hImage : ‖R.completionMap v (B.tateParameter (R.basePlace v))‖ < 1 := by
    change ‖iutEmbedCompletion (R.liesOver v)
      (B.tateParameter (R.basePlace v))‖ < 1
    exact (iutEmbedCompletion_norm_lt_one_iff (R.liesOver v) _).2
      (B.tateParameter_norm_lt_one (R.basePlace v))
  have hPow : ‖R.qroot v‖ ^ (2 * D.prime.ℓ) < 1 := by
    rw [← norm_pow, R.qroot_pow_eq v]
    exact hImage
  by_contra h
  exact (not_lt_of_ge (one_le_pow₀ (le_of_not_gt h))) hPow

end IutTorsionQRootSource

/-- A direct q-root norm cannot fill the base norm field of a Scene1 input
with the current log-shell and volume-transfer conventions. -/
theorem Scene1Input.thetaBase_norm_ne_canonical_qroot_norm
    {K O : Type u} [Field K] [NumberField K] [CommRing O]
    {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (S : Scene1Input K O p)
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    S.data.link.theta.norm S.data.link.thetaBase ≠
      ‖(IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot v‖ := by
  intro h
  have hBase := S.one_le_thetaBase_norm
  rw [h] at hBase
  exact (not_lt_of_ge hBase)
    (IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one D v)

end JoshiTeich.Act1Scene1
