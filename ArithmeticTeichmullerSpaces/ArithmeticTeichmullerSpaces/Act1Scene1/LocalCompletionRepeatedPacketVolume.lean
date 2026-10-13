import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorDegreeVolume
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
source-id: JT-SCENE1-LOCAL-REPEATED-PACKET-VOLUME
source: actual Packet degree-normalized Haar formula and Joshi III
`le:volume-lemma3` procession tensor shape.
fidelity: models a fixed completion repeated over a finite procession index
`Fin n`. It proves the exact raw degree-normalized exponent `n/[K_w:ℚ_p]`.
This is a structural tensor calculation; it does not identify procession
classes, Bloch--Kato logarithms, a theta hull, or the paper's weighted volume.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

abbrev repeatedPacket (w : NumberField.FinitePlace K)
    (hw : JoshiTeich.Prologue.Arithmetic.residueChar w = p) (n : ℕ) :
    Packet K p (Fin n) :=
  ⟨fun _ => w, fun _ => hw⟩

abbrev repeatedScalar (w : NumberField.FinitePlace K)
    (hw : JoshiTeich.Prologue.Arithmetic.residueChar w = p) (n : ℕ)
    (x : completionAt K w) :
    ∀ i, (repeatedPacket w hw n).Factor i :=
  fun _ => x

local instance repeatedFactorAlgebra (w : NumberField.FinitePlace K)
    (hw : JoshiTeich.Prologue.Arithmetic.residueChar w = p) (n : ℕ) (i : Fin n) :
    Algebra ℚ_[p] ((repeatedPacket w hw n).Factor i) :=
  padicAlgebra hw
local instance repeatedFactorFinite (w : NumberField.FinitePlace K)
    (hw : JoshiTeich.Prologue.Arithmetic.residueChar w = p) (n : ℕ) (i : Fin n) :
    Module.Finite ℚ_[p] ((repeatedPacket w hw n).Factor i) :=
  finite_padicAlgebra hw
local instance repeatedIntegralModule {ι : Type} [Fintype ι]
    (P : Packet K p ι) : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem repeatedPacket_factor_finrank (w : NumberField.FinitePlace K)
    (hw : JoshiTeich.Prologue.Arithmetic.residueChar w = p) (n : ℕ) (i : Fin n) :
    Module.finrank ℚ_[p] ((repeatedPacket w hw n).Factor i) =
      Arithmetic.localDeg w := by
  exact finrank_padic_eq_localDeg w hw

theorem repeatedPacket_degreeVolume_eq
    (w : NumberField.FinitePlace K)
    (hw : JoshiTeich.Prologue.Arithmetic.residueChar w = p)
    (n : ℕ) (x : completionAt K w)
    (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    (repeatedPacket w hw n).degreeVolume
      ((repeatedPacket w hw n).scalarLattice (repeatedScalar w hw n x)) =
      ‖x‖ ^ ((n : ℝ) / Arithmetic.localDeg w) := by
  rw [degreeVolume_scalarLattice_eq_norm_product
    (repeatedPacket w hw n) (repeatedScalar w hw n x)
    (fun _ => by simpa [repeatedScalar] using hx)
    (fun _ => by simpa [repeatedScalar] using hx1)]
  simp only [repeatedScalar, repeatedPacket]
  change (∏ _ : Fin n, ‖x‖ ^ (1 / (Arithmetic.localDeg w : ℝ))) = _
  rw [Fin.prod_const n]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
  congr 1
  field_simp [show (Arithmetic.localDeg w : ℝ) ≠ 0 by
    exact_mod_cast (Arithmetic.localDeg_pos w).ne']

theorem repeatedPacket_degreeLogVolume_eq
    (w : NumberField.FinitePlace K)
    (hw : JoshiTeich.Prologue.Arithmetic.residueChar w = p)
    (n : ℕ) (x : completionAt K w)
    (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    (repeatedPacket w hw n).degreeLogVolume
      ((repeatedPacket w hw n).scalarLattice (repeatedScalar w hw n x)) =
      (n : ℝ) * Real.log ‖x‖ / Arithmetic.localDeg w := by
  rw [degreeLogVolume_scalarLattice_eq_norm_sum
    (repeatedPacket w hw n) (repeatedScalar w hw n x)
    (fun _ => by simpa [repeatedScalar] using hx)
    (fun _ => by simpa [repeatedScalar] using hx1)]
  simp only [repeatedScalar, repeatedPacket]
  change (∑ _ : Fin n, Real.log ‖x‖ / (Arithmetic.localDeg w : ℝ)) = _
  rw [Fin.sum_const n, nsmul_eq_mul]
  ring

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
