import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLog
import ArithmeticTeichmullerSpaces.Act1Scene1.ThetaLogSignAudit

/-!
source-id: JT-SCENE1-INITIAL-THETA-LOCAL-LOG-WITNESS
source: actual InitialThetaData canonical q-root; Joshi III,
`le:elem-lemma` and `eq:multiplicative-coh-class` in the proof of
`th:moccor-Mochizuki-form1`; the local logarithm API is independently ported
in LocalPadicLog.
fidelity: constructs an ordinary p-adic logarithm element and a principal
unit witness in the actual torsion completion, proves log-shell membership
and the q-root norm identity. It does not construct or identify a Bloch-Kato
cohomology class or a theta locus in a different untilt.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.InitialThetaLogWitness

open JoshiTeich.Prologue
open NumberField

universe u
noncomputable section

theorem norm_residueChar_lt_one
    {K : Type u} [Field K] [NumberField K] (v : FinitePlace K) :
    ‖(Arithmetic.residueChar v : v.maximalIdeal.adicCompletion K)‖ < 1 := by
  have hmem : (Arithmetic.residueChar v : 𝓞 K) ∈ v.maximalIdeal.asIdeal :=
    (Arithmetic.natCast_mem_maximalIdeal_iff v (Arithmetic.residueChar_prime v)).2 rfl
  simpa only [map_natCast] using
    (FinitePlace.norm_lt_one_iff_mem (v := v.maximalIdeal) K
      (Arithmetic.residueChar v : 𝓞 K)).2 hmem

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

/-- A concrete normalized p-adic logarithm in the original torsion completion. -/
def value (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    v.1.maximalIdeal.adicCompletion ↥D.prime.torsionField :=
  LocalPadicLog.normalizedLog (Arithmetic.residueChar v.1)
    ((IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot v)

theorem value_mem_logShell
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    value D v ∈ LocalPadicLog.logShell (k := v.1.maximalIdeal.adicCompletion
      ↥D.prime.torsionField) (Arithmetic.residueChar v.1) := by
  letI : CharZero (v.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) :=
    charZero_of_injective_ringHom (FinitePlace.embedding v.1.maximalIdeal).injective
  exact LocalPadicLog.normalizedLog_mem_logShell
    (Arithmetic.residueChar_prime v.1) (norm_residueChar_lt_one v.1)
    (IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one D v).le

theorem norm_value_eq_qroot_norm
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    ‖value D v‖ = ‖(IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot v‖ := by
  letI : CharZero (v.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) :=
    charZero_of_injective_ringHom (FinitePlace.embedding v.1.maximalIdeal).injective
  exact LocalPadicLog.norm_normalizedLog
    (Arithmetic.residueChar_prime v.1) (norm_residueChar_lt_one v.1)
    (IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one D v).le

theorem value_ne_zero
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    value D v ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_value_eq_qroot_norm D v]
  exact norm_ne_zero_iff.mpr
    ((IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot_ne_zero v)

end
end JoshiTeich.Act1Scene1.InitialThetaLogWitness
