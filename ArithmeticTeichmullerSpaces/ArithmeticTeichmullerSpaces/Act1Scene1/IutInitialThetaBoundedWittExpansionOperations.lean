import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittExpansion

/-!
source-id: JT-SCENE1-INITIAL-THETA-BOUNDED-WITT-EXPANSION-OPERATIONS
source: Joshi II se:ff-rings / W(O_F) into B (511--512, 719--727);
the actual Teichmuller expansion laws in `WittTeichmullerExpansion`.
fidelity: bounded expansions are stable under multiplication by a nonzero
Teichmuller representative, with the explicit norm bound. This is an
algebraic precursor to rho-norm representation
independence; it does not assert a rho norm, a Frechet completion, or the
paper's completed B. Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaBoundedWittExpansion

open JoshiTeich.Prologue InitialThetaTiltFontaine InitialThetaCanonicalGeometricFontaine
open InitialThetaBoundedWittLocalization
open WittTeichmullerExpansion
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrimeOps : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem hasBoundedExpansion_teichmuller_mul
    (z : Ambient D w) (hz : HasBoundedExpansion D w z)
    (r : InitialThetaTiltField.Carrier D w) (hr : r ≠ 0) :
    HasBoundedExpansion D w
      (algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z) := by
  obtain ⟨m, y, c, C, hC, hbound, hc, hz⟩ := hz
  let p := Arithmetic.residueChar w.1
  let y' : FieldWitt D w := WittVector.teichmuller p r * y
  let c' : ℕ → InitialThetaTiltField.Carrier D w := fun n => r * c n
  refine ⟨m, y', c', ‖r‖ * C, mul_pos (norm_pos_iff.mpr hr) hC, ?_, ?_, ?_⟩
  · intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg r)
  · exact expands_teichmuller_mul p r y c hc
  · calc
      (algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller p r) * z) * (p : Ambient D w) ^ m =
        algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller p r) * (z * (p : Ambient D w) ^ m) := by
            rw [mul_assoc]
      _ = algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller p r) *
            algebraMap (FieldWitt D w) (Ambient D w) y := by rw [hz]
      _ = algebraMap (FieldWitt D w) (Ambient D w) y' := by
            rw [map_mul]

theorem hasBoundedExpansion_teichmuller_mul_iff
    (z : Ambient D w) (r : InitialThetaTiltField.Carrier D w) (hr : r ≠ 0) :
    HasBoundedExpansion D w
        (algebraMap (FieldWitt D w) (Ambient D w)
            (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z) ↔
      HasBoundedExpansion D w z := by
  constructor
  · intro hz
    have hscaled := hasBoundedExpansion_teichmuller_mul D w
      (algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z)
      hz r⁻¹ (inv_ne_zero hr)
    have heq :
        algebraMap (FieldWitt D w) (Ambient D w)
            (WittVector.teichmuller (Arithmetic.residueChar w.1) r⁻¹) *
          (algebraMap (FieldWitt D w) (Ambient D w)
            (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z) = z := by
      rw [← mul_assoc, ← map_mul, ← (WittVector.teichmuller (Arithmetic.residueChar w.1)).map_mul,
        inv_mul_cancel₀ hr, (WittVector.teichmuller (Arithmetic.residueChar w.1)).map_one,
        map_one, one_mul]
    rw [heq] at hscaled
    exact hscaled
  · intro hz
    exact hasBoundedExpansion_teichmuller_mul D w z hz r hr

end
end JoshiTeich.Act1Scene1.InitialThetaBoundedWittExpansion
