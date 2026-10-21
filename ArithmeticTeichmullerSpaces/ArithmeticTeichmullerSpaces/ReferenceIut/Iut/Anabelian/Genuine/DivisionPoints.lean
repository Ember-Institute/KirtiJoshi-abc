/-
original-path: `refer/iut/Iut/Anabelian/Genuine/Pi1.lean`
original-author: Christian Merten <lana@merten.dev>
original-commit: `7b3756ff3fde46bbd4daa89076fd4bc9c4e60baf`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the source's 2026 iut contributors notice and Apache-2.0
license before copying. The original notice is retained below.
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
fidelity: extracted the compatible-division-system proof. In characteristic zero
the chosen system uses proved divisibility, with no conditional fallback value;
added positive-level nonconstancy and the scalar-multiplication equations.
boundary: Scene1/Derived. This constructs division points, not an orbicurve
covering/core or a theta-root model.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Torsion.Divisible
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.GenericPoint

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section

set_option maxHeartbeats 1000000

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- Points on the seed curve in the actual function-field algebraic closure. -/
abbrev Pt : Type u := (E⁄(Ω E)).toAffine.Point

/-- A **compatible system of division points** of the generic point: `Q₁ = G` and
`n Q_{nℓ} = Q_ℓ`. -/
def Compatible (Q : ℕ → Pt E) : Prop :=
  Q 1 = genericPoint E ∧ ∀ n ℓ : ℕ, 0 < n → 0 < ℓ → n • Q (n * ℓ) = Q ℓ

lemma exists_compatible (hdiv : ∀ n : ℕ, 0 < n → ∀ Q : Pt E, ∃ R : Pt E, n • R = Q) :
    ∃ Q, Compatible E Q := by
  -- `R m` with `(m + 1) • R (m + 1) = R m`, `R 0 = G`
  let R : ℕ → Pt E := fun m => Nat.rec (genericPoint E)
    (fun m Rm => (hdiv (m + 1) m.succ_pos Rm).choose) m
  have hR : ∀ m, (m + 1) • R (m + 1) = R m := fun m =>
    (hdiv (m + 1) m.succ_pos (R m)).choose_spec
  have hasc : ∀ b d, (b + 1).ascFactorial d • R (b + d) = R b := by
    intro b d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Nat.ascFactorial_succ, mul_comm, mul_smul, ← add_assoc,
        show b + 1 + d = b + d + 1 by omega, hR, ih]
  have hfac : ∀ m, m.factorial • R m = genericPoint E := by
    intro m
    have := hasc 0 m
    simp only [zero_add, Nat.one_ascFactorial] at this
    exact this
  refine ⟨fun ℓ => (ℓ - 1).factorial • R ℓ, ?_, ?_⟩
  · simp only [Nat.sub_self, Nat.factorial_zero, one_smul]
    simpa using hfac 1
  · intro n ℓ hn hℓ
    simp only
    have hle : ℓ ≤ n * ℓ := Nat.le_mul_of_pos_left ℓ hn
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have key : n * (n * ℓ - 1).factorial = (ℓ - 1).factorial * (ℓ + 1).ascFactorial d := by
      have h1 := Nat.factorial_mul_ascFactorial ℓ d
      rw [← hd] at h1
      have h2 : (n * ℓ).factorial = n * ℓ * (n * ℓ - 1).factorial := by
        rw [← Nat.mul_factorial_pred (Nat.mul_pos hn hℓ).ne']
      have h3 : ℓ.factorial = ℓ * (ℓ - 1).factorial := by
        rw [← Nat.mul_factorial_pred hℓ.ne']
      rw [h2, h3] at h1
      have : ℓ * (n * (n * ℓ - 1).factorial) =
          ℓ * ((ℓ - 1).factorial * (ℓ + 1).ascFactorial d) :=
        calc ℓ * (n * (n * ℓ - 1).factorial) = n * ℓ * (n * ℓ - 1).factorial := by ring
          _ = ℓ * (ℓ - 1).factorial * (ℓ + 1).ascFactorial d := h1.symm
          _ = ℓ * ((ℓ - 1).factorial * (ℓ + 1).ascFactorial d) := by ring
      exact Nat.eq_of_mul_eq_mul_left hℓ this
    rw [smul_smul, key, mul_smul, hd, hasc]


instance instCharZeroClosure [CharZero k] : CharZero (Ω E) :=
  charZero_of_injective_algebraMap (algebraMap k (Ω E)).injective

/-- Scalar multiplication is surjective on the actual geometric elliptic curve. -/
lemma divisible [CharZero k] (n : ℕ) (hn : 0 < n) (Q : Pt E) : ∃ R : Pt E, n • R = Q :=
  JoshiTeich.ReferenceIut.Torsion.nsmul_surjective (E⁄(Ω E)) n hn.ne' Q

/-- The actual compatible system, chosen from a proved nonempty family. -/
def divSys [CharZero k] : ℕ → Pt E :=
  (exists_compatible E (fun n hn Q => divisible E n hn Q)).choose

lemma compatible_divSys [CharZero k] : Compatible E (divSys E) :=
  (exists_compatible E (fun n hn Q => divisible E n hn Q)).choose_spec

@[simp] lemma divSys_one [CharZero k] : divSys E 1 = genericPoint E :=
  (compatible_divSys E).1

lemma mul_nsmul_divSys [CharZero k] (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    n • divSys E (n * m) = divSys E m :=
  (compatible_divSys E).2 n m hn hm

lemma nsmul_divSys [CharZero k] (n : ℕ) (hn : 0 < n) :
    n • divSys E n = genericPoint E := by
  simpa only [mul_one, divSys_one] using mul_nsmul_divSys E n 1 hn Nat.one_pos

/-- Positive-level division points are not constant-field rational points. -/
theorem divSys_ne_base [CharZero k] (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) :
    divSys E n ≠ base E T := by
  intro h
  apply genericPoint_ne_base E (n • T)
  calc
    genericPoint E = n • divSys E n := (nsmul_divSys E n hn).symm
    _ = n • base E T := congrArg (fun Q : Pt E => n • Q) h
    _ = base E (n • T) := (map_nsmul (base E) n T).symm

lemma divSys_ne_zero [CharZero k] (n : ℕ) (hn : 0 < n) : divSys E n ≠ 0 := by
  simpa only [map_zero] using divSys_ne_base E n hn 0

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
