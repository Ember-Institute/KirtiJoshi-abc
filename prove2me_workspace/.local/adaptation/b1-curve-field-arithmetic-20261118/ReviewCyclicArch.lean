import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Solutions.Source_TripodCyclicArch

open AbcAdaptation.Tripod WeierstrassCurve
open scoped Classical

example :
    ComplexTorsionXBound ↔
      ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] {N : ℕ},
        1 ≤ N → ∀ {x y : ℂ} (h : W.toAffine.Nonsingular x y),
          N • (Affine.Point.some x y h : W.toAffine.Point) = 0 →
          ‖x + W.b₂ / 12‖ ^ 6 ≤ A * ‖W.Δ‖ * max ‖W.j‖ 1 *
            (2 * N ^ 2 + B * (Real.log (max ‖W.j‖ (Real.exp 1)) + 1) ^ 2) ^ 6 :=
  Iff.rfl

example (hcomplex : ComplexTorsionXBound) (c : ℝ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (l : ℂ), |Real.log ‖l‖| ≤ c → |Real.log ‖l - 1‖| ≤ c →
      ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic], W = legendre l →
        ∀ {N : ℕ}, 1 ≤ N → ∀ {x y : ℂ} (h : W.toAffine.Nonsingular x y),
          N • (Affine.Point.some x y h : W.toAffine.Point) = 0 → ‖x‖ ≤ C₀ * N ^ 2 :=
  legendre_torsion_x_le_of_complex hcomplex c

#print axioms ComplexTorsionXBound
#print axioms legendre_torsion_x_le_of_complex
