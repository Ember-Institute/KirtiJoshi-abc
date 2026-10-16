import ArithmeticTeichmullerSpaces.Act1Scene1.LocalIntegerUnitLogarithm
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionHaarIndex
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
source-id: JT-SCENE1-ACTUAL-COMPLETION-UNIT-LOGARITHM
source: actual number-field completions, finite residue fields and
Joshi III 2843--2853. No reference source code is copied.
fidelity: derives the finite residue field and its characteristic from the
actual compact integer ring and the norm of the residue prime. The full
unit logarithm is continuous, and its p*-scaled image equals the old shell.
boundary: Scene1/Derived; integral-H1 and BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion
open NumberField
open JoshiTeich.Prologue.Arithmetic
open scoped Valued
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)

theorem integerResidue_finite : Finite (IsLocalRing.ResidueField (integerRing w)) :=
  ((Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := completionAt K w) (Γ₀ := WithZero (Multiplicative ℤ))).mp
      (integerRing_compactSpace w)).2.2

theorem integerResidue_charP :
    CharP (IsLocalRing.ResidueField (integerRing w)) (residueChar w) := by
  apply (CharP.charP_iff_prime_eq_zero (residueChar_prime w)).mpr
  rw [← map_natCast (IsLocalRing.residue (integerRing w)), IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal]
  apply Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr
  apply Valued.toNormedField.norm_lt_one_iff.mp
  haveI : Fact (residueChar w).Prime := ⟨residueChar_prime w⟩
  have h := norm_natCast_prime_lt_one (p := residueChar w) (w := w) rfl
  change ‖(residueChar w : completionAt K w)‖ < 1
  rwa [← FinitePlace.embedding_apply, map_natCast] at h

local instance completionResiduePrime : Fact (residueChar w).Prime := ⟨residueChar_prime w⟩
local instance completionResidueFinite : Finite (IsLocalRing.ResidueField (integerRing w)) :=
  integerResidue_finite w
local instance completionResidueCharP :
    CharP (IsLocalRing.ResidueField (integerRing w)) (residueChar w) := integerResidue_charP w
local instance completionUnitCharZero : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
local instance completionUnitPadicAlgebra : Algebra ℚ_[residueChar w] (completionAt K w) :=
  padicAlgebra (w := w) rfl
local instance completionUnitContinuousSMul : ContinuousSMul ℚ_[residueChar w] (completionAt K w) :=
  continuousSMul_of_algebraMap _ _ (continuous_padicEmb (w := w) rfl)

private theorem norm_residuePrime_lt_one : ‖(residueChar w : completionAt K w)‖ < 1 := by
  have h := norm_natCast_prime_lt_one (p := residueChar w) (w := w) rfl
  rwa [← FinitePlace.embedding_apply, map_natCast] at h

/-- The canonical full unit branch, computed on the original completion. -/
def unitLog : Additive (integerRing w)ˣ →+ completionAt K w :=
  LocalPadicLog.integerUnitLog (Ω := AlgebraicClosure (completionAt K w))
    (residueChar w) (norm_residuePrime_lt_one w)

theorem unitLog_of_principal (a : (integerRing w)ˣ)
    (ha : ‖((a : integerRing w) : completionAt K w) - 1‖ < 1) :
    unitLog w (Additive.ofMul a) = LocalPadicLog.padicLog ((a : integerRing w) : completionAt K w) :=
  LocalPadicLog.integerUnitLog_of_principal _ _ a ha

theorem unitLog_power_formula (a : (integerRing w)ˣ) :
    unitLog w (Additive.ofMul a) =
      (LocalPadicLog.unitResidueExponent (k := completionAt K w) : completionAt K w)⁻¹ *
        LocalPadicLog.padicLog (((a : integerRing w) : completionAt K w) ^
          LocalPadicLog.unitResidueExponent (k := completionAt K w)) :=
  LocalPadicLog.integerUnitLog_power_formula _ _ a

theorem unitLog_continuous :
    Continuous (fun a : (integerRing w)ˣ => unitLog w (Additive.ofMul a)) :=
  LocalPadicLog.integerUnitLog_continuous _ _

theorem logShell_eq_scaled_unitLog_image :
    LocalPadicLog.logShell (k := completionAt K w) (residueChar w) =
      {y | ∃ a : (integerRing w)ˣ,
        y = (LocalPadicLog.paperScale (residueChar w) : completionAt K w)⁻¹ *
          unitLog w (Additive.ofMul a)} :=
  LocalPadicLog.logShell_eq_paperIntegerUnitLogShell (Ω := AlgebraicClosure (completionAt K w))
    (residueChar w) (norm_residuePrime_lt_one w)

end
end JoshiTeich.Act1Scene1.LocalCompletion
