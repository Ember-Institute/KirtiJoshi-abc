import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
source-id: JT-SCENE1-ADIC-RESIDUE-EVALUATION
source: Mathlib AdicCompletion.evalOneₐ, ker_evalOneₐ_eq_map and
isAdicComplete_self; the de Rham completion used in Joshi II (1069--1076).
fidelity: extends an explicit residue equivalence to the actual adic completion.
Finite generation gives the exact kernel and completeness; a field residue
then gives locality. No Noetherian or local hypothesis on the source ring.
Original proofs, no copied reference-engine code; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.AdicResidueEvaluation

noncomputable section
variable {R K : Type*} [CommRing R] [Field K]
variable (I : Ideal R) (e : (R ⧸ I) ≃+* K)

def evaluation : AdicCompletion I R →+* K :=
  e.toRingHom.comp (AdicCompletion.evalOneₐ I).toRingHom

theorem evaluation_algebraMap (a : R) :
    evaluation I e (algebraMap R (AdicCompletion I R) a) = e (Ideal.Quotient.mk I a) := rfl

theorem evaluation_surjective : Function.Surjective (evaluation I e) :=
  e.surjective.comp (AdicCompletion.evalOneₐ_surjective I)

theorem kernel_eq_map (hfg : I.FG) :
    RingHom.ker (evaluation I e) = I.map (algebraMap R (AdicCompletion I R)) := by
  rw [evaluation, RingHom.ker_comp_of_injective _ e.injective]
  exact AdicCompletion.ker_evalOneₐ_eq_map I hfg

theorem kernel_eq_span (a : R) (ha : I = Ideal.span {a}) :
    RingHom.ker (evaluation I e) =
      Ideal.span {algebraMap R (AdicCompletion I R) a} := by
  have hfg : I.FG := by
    rw [ha]
    exact Submodule.fg_span_singleton a
  rw [kernel_eq_map I e hfg, ha, Ideal.map_span, Set.image_singleton]

theorem complete (hfg : I.FG) :
    IsAdicComplete (RingHom.ker (evaluation I e)) (AdicCompletion I R) := by
  rw [kernel_eq_map I e hfg]
  exact AdicCompletion.isAdicComplete_self I hfg

def quotientEquiv :
    (AdicCompletion I R ⧸ RingHom.ker (evaluation I e)) ≃+* K :=
  (evaluation I e).quotientKerEquivOfSurjective (evaluation_surjective I e)

theorem quotientEquiv_mk (a : AdicCompletion I R) :
    quotientEquiv I e (Ideal.Quotient.mk _ a) = evaluation I e a :=
  RingHom.quotientKerEquivOfSurjective_apply_mk
    (f := evaluation I e) (evaluation_surjective I e) a

section Field

theorem kernel_isMaximal : (RingHom.ker (evaluation I e)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (evaluation I e) (evaluation_surjective I e)

include e in
theorem localRing (hfg : I.FG) : IsLocalRing (AdicCompletion I R) := by
  let := kernel_isMaximal I e
  let := complete I e hfg
  exact isLocalRing_of_isAdicComplete_maximal (RingHom.ker (evaluation I e))

variable [IsLocalRing (AdicCompletion I R)]

theorem maximalIdeal_eq_kernel :
    IsLocalRing.maximalIdeal (AdicCompletion I R) = RingHom.ker (evaluation I e) :=
  (IsLocalRing.eq_maximalIdeal (kernel_isMaximal I e)).symm

theorem isUnit_iff (a : AdicCompletion I R) : IsUnit a ↔ evaluation I e a ≠ 0 := by
  rw [← not_iff_not]
  simp only [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
    maximalIdeal_eq_kernel I e, RingHom.mem_ker, not_not]

end Field
end
end JoshiTeich.Act1Scene1.AdicResidueEvaluation
