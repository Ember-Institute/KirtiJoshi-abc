/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/SL2Image.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `47ef99c97945984ea799ee2333fcf920abecdae4`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: ports the Tate root-class to ramification divisibility step
with an explicit completion-parameter alignment certificate.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutLocalTorsionCardinality
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTateValuationBridge

/-!
source-id: IUT-COR312-ROOTCLASS-RAMIFICATION
source: `refer/iut/Iut/Concrete/SL2Image.lean`,
`EllipticCurveData.prime_dvd_ramificationIdx`.
fidelity: from a local Tate structure, the `ell²` torsion bound, and an
explicit equality between the local Tate parameter and the canonical
completion image of the base parameter, the residue root-class equation forces
`ell` to divide the relative ramification index when `ell` is prime to the
base Tate order. The parameter alignment remains an explicit source field.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutCurveModEllRepData

open JoshiTeich.Prologue
open NumberField WeierstrassCurve TateCurvesTheta
open WithZero
open JoshiTeich.ReferenceIut
open JoshiTeich.ReferenceIut.Anabelian
open scoped Classical WithZero Valued

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {ell : ℕ} (R : IutCurveModEllRepData F E Fbar ell)

local instance (priority := 1100) instDecidableEqTorsionFieldRoot :
    DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

lemma prime_dvd_ramificationIdx_of_tate
    (hp : ell.Prime)
    {w : FinitePlace F} {w' : FinitePlace ↥R.torsionField}
    (hw'w : FinitePlace.LiesOver w' w)
    (t : TateParameter (localCompletion w))
    {π : localCompletion w} (hπ : IsUniformizer π)
    (S : TateStructure (curveKw E R.torsionField w'))
    (hq : (S.t.q : localCompletion w') =
      iutEmbedCompletion hw'w (t.q : localCompletion w))
    (hcard : ell * ell ≤ Nat.card ↥(TateStructure.torsion ell
      (curveKw E R.torsionField w')))
    (hcop : ¬ ell ∣ (t.toOrdered hπ).orderNat) :
    ell ∣ w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal := by
  letI : NeZero ell := ⟨hp.ne_zero⟩
  letI : Finite ↥(TateStructure.torsion ell
      (curveKw E R.torsionField w')) := S.finite_torsion ell
  set e : ℕ := w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal with he
  set n : ℕ := (t.toOrdered hπ).orderNat with hn
  have hqBase : Valued.v (t.q : localCompletion w) = exp (-(n : ℤ)) := by
    rw [iutValued_q_toOrdered (E := t.tateCurve) t hπ, hn]
  have hqK : Valued.v (S.t.q : localCompletion w') = exp (-((e : ℤ) * n)) := by
    rw [hq, iutValuedEmbedCompletion hw'w, hqBase]
    change exp (-(n : ℤ)) ^ e = exp (-((e : ℤ) * n))
    rw [← exp_nsmul]
    congr 1
    simp [smul_eq_mul]
  obtain ⟨u, m, hu⟩ := S.exists_root_class ell hcard
  have hu' := congrArg (fun x : (localCompletion w')ˣ =>
    Valued.v (x : localCompletion w')) hu
  simp only [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
    map_pow, map_zpow₀] at hu'
  rw [hqK] at hu'
  have hu0 : Valued.v (u : localCompletion w') ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr u.ne_zero
  rw [← exp_log hu0, ← exp_nsmul, ← exp_zsmul, exp_inj,
    nsmul_eq_mul, smul_eq_mul] at hu'
  have hdvd : (ell : ℤ) ∣ (1 + ell * m) * ((e : ℤ) * n) :=
    ⟨-log (Valued.v (u : localCompletion w')), by linear_combination hu'⟩
  rw [add_mul, one_mul,
    dvd_add_left (Dvd.intro (m * ((e : ℤ) * n)) (by ring))] at hdvd
  have hdvd' : ell ∣ e * n := by exact_mod_cast hdvd
  have hcop' : ¬ ell ∣ n := by simpa [hn] using hcop
  have hdiv : ell ∣ e := (hp.dvd_mul.mp hdvd').resolve_right hcop'
  simpa [he] using hdiv

end

end JoshiTeich.Act1Scene1.IutCurveModEllRepData
