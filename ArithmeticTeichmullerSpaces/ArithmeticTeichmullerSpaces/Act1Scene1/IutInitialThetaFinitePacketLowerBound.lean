import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePacketLogVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationLogVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-FINITE-PACKET-LOWER-BOUND
source: actual scalar-normalization determinant/Haar formula and the
distinguished-factor region; `refer/iut/Iut/Concrete/ThetaRegion.lean`,
`scaleElt` / `thetaFinite`, supply the local container shape.
Joshi III `le:volume-lemma3` supplies the containment-to-volume comparison
pattern. This does not identify this container with the paper theta locus.
fidelity: computes the component log-volume of its contained scalar
normalization, proves the component lower bound, and integrates it over
all actual torsion-place tuples. The exact tuple marginal law gives
packetLogVolume >= -j^2 * log(p) * actual VBad weighted q-root order.
No paper weight, locus, BK or final Corollary identity is assumed.
Original consumer proofs; no reference source code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLowerBound

open JoshiTeich.Prologue MeasureTheory
open IutInitialThetaFinitePacketRegion IutInitialThetaFinitePacketLogVolume
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local instance fiberFinite (p : Nat.Primes) : Finite (Fiber D p) :=
  Arithmetic.fiber_finite (p : ℕ)
local instance fiberFintype (p : Nat.Primes) : Fintype (Fiber D p) := Fintype.ofFinite _
local instance factorAlgebra (p : Nat.Primes) (j : ℕ) (c : Tuple D p j)
    (i : Fin (j + 1)) : Algebra ℚ_[(p : ℕ)] ((packet D p j c).Factor i) :=
  LocalCompletion.padicAlgebra ((packet D p j c).residueChar_eq i)

theorem tupleWeight_coordinate_sum (p : Nat.Primes) (j : ℕ) (d : Fin (j + 1))
    (f : Fiber D p → ℝ) :
    (∑ c : Tuple D p j, tupleWeight D p j c * f (c d)) =
      ∑ v : Fiber D p, placeWeight D p v * f v := by
  have hterm (c : Tuple D p j) :
      tupleWeight D p j c * f (c d) =
        ∏ i, placeWeight D p (c i) * (if i = d then f (c i) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    rfl
  have hsum (i : Fin (j + 1)) :
      (∑ v : Fiber D p, placeWeight D p v * (if i = d then f v else 1)) =
        if i = d then (∑ v : Fiber D p, placeWeight D p v * f v) else 1 := by
    by_cases hi : i = d
    · simp only [hi, ite_true]
    · simp only [hi, ite_false, mul_one, placeWeight_sum_one]
  calc
    _ = ∑ c : Tuple D p j, ∏ i, placeWeight D p (c i) *
        (if i = d then f (c i) else 1) := Finset.sum_congr rfl (fun c _ => hterm c)
    _ = ∏ i : Fin (j + 1), ∑ v : Fiber D p,
        placeWeight D p v * (if i = d then f v else 1) :=
      (Fintype.prod_sum (fun (i : Fin (j + 1)) (v : Fiber D p) =>
        placeWeight D p v * (if i = d then f v else 1))).symm
    _ = _ := by simp_rw [hsum]; simp

theorem normalized_root_log_eq_ordp (p : Nat.Primes) (v : Fiber D p) :
    Real.log ‖IutInitialThetaQRootFamily.vbadQrootAt D v.1‖ /
        (Arithmetic.localDeg v.1 : ℝ) =
      -Real.log (p : ℕ) * Arithmetic.ordp v.1
        (IutInitialThetaQRootFamily.vbadQrootAt D v.1) := by
  have hd : (Arithmetic.localDeg v.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.localDeg_pos v.1).ne'
  have hp : Real.log (p : ℕ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
  unfold Arithmetic.ordp
  rw [v.2]
  field_simp

set_option maxHeartbeats 2000000 in
theorem componentLogVolume_principalRegion (p : Nat.Primes) (j : ℕ)
    (c : Tuple D p j) :
    componentLogVolume D p j c
      ((packet D p j c).principalRegion
        (IutInitialThetaFiniteFactorRegion.scaleElt D (packet D p j c) (Fin.last j) j)) =
      ((j ^ 2 : ℕ) : ℝ) *
        (Real.log ‖IutInitialThetaQRootFamily.vbadQrootAt D (c (Fin.last j)).1‖ /
          (Arithmetic.localDeg (c (Fin.last j)).1 : ℝ)) := by
  let P := packet D p j c
  let z := IutInitialThetaFiniteFactorRegion.scalars D P (Fin.last j) j
  let hz := IutInitialThetaFiniteFactorRegion.scalars_ne_zero D P (Fin.last j) j
  change P.normalizationLogVolume (P.principalRegion (P.pure z)) = _
  rw [P.normalizationLogVolume_pure_principalRegion z hz]
  have ht (i : Fin (j + 1)) :
      Real.log ‖z i‖ / (Arithmetic.localDeg (P.place i) : ℝ) =
        if i = Fin.last j then
          ((j ^ 2 : ℕ) : ℝ) *
            (Real.log ‖IutInitialThetaQRootFamily.vbadQrootAt D (c (Fin.last j)).1‖ /
              (Arithmetic.localDeg (c (Fin.last j)).1 : ℝ)) else 0 := by
    by_cases hi : i = Fin.last j
    · subst i
      rw [ite_eq_left rfl]
      dsimp [z]
      rw [IutInitialThetaFiniteFactorRegion.scalars_distinguished, norm_pow, Real.log_pow]
      change ((j ^ 2 : ℕ) : ℝ) *
          Real.log ‖IutInitialThetaQRootFamily.vbadQrootAt D (c (Fin.last j)).1‖ /
            (Arithmetic.localDeg (c (Fin.last j)).1 : ℝ) = _
      exact mul_div_assoc _ _ _
    · rw [ite_eq_right hi]
      have hz1 : z i = 1 :=
        IutInitialThetaFiniteFactorRegion.scalars_other D P (Fin.last j) j i hi
      simp [hz1]
  simp_rw [ht]
  simp

private theorem neg_mul_mul_eq_mul_neg_mul (a b c : ℝ) : -a * b * c = a * (-b * c) := by
  ring

set_option maxHeartbeats 8000000 in
theorem componentLogVolume_region_lower_bound (p : Nat.Primes) (j : ℕ)
    (c : Tuple D p j) :
    -((j ^ 2 : ℕ) : ℝ) * Real.log (p : ℕ) *
        Arithmetic.ordp (c (Fin.last j)).1
          (IutInitialThetaQRootFamily.vbadQrootAt D (c (Fin.last j)).1) ≤
      componentLogVolume D p j c
        (IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j) := by
  let P := packet D p j c
  let z := IutInitialThetaFiniteFactorRegion.scalars D P (Fin.last j) j
  let hz := IutInitialThetaFiniteFactorRegion.scalars_ne_zero D P (Fin.last j) j
  have hmono : componentLogVolume D p j c (P.principalRegion (P.pure z)) ≤
      componentLogVolume D p j c
        (IutInitialThetaFiniteFactorRegion.region D P (Fin.last j) j) :=
    P.normalizationLogVolume_principalRegion_le_factorOrbit z hz
  calc
    _ = ((j ^ 2 : ℕ) : ℝ) * (-Real.log (p : ℕ) *
        Arithmetic.ordp (c (Fin.last j)).1
          (IutInitialThetaQRootFamily.vbadQrootAt D (c (Fin.last j)).1)) := by
      exact neg_mul_mul_eq_mul_neg_mul _ _ _
    _ = ((j ^ 2 : ℕ) : ℝ) *
        (Real.log ‖IutInitialThetaQRootFamily.vbadQrootAt D (c (Fin.last j)).1‖ /
          (Arithmetic.localDeg (c (Fin.last j)).1 : ℝ)) :=
      congrArg (fun x : ℝ => ((j ^ 2 : ℕ) : ℝ) * x)
        (normalized_root_log_eq_ordp D p (c (Fin.last j))).symm
    _ = componentLogVolume D p j c (P.principalRegion (P.pure z)) :=
      (componentLogVolume_principalRegion D p j c).symm
    _ ≤ _ := hmono

theorem tupleWeight_order_sum (p : Nat.Primes) (j : ℕ) :
    (∑ c : Tuple D p j, tupleWeight D p j c *
      Arithmetic.ordp (c (Fin.last j)).1
        (IutInitialThetaQRootFamily.vbadQrootAt D (c (Fin.last j)).1)) =
      IutInitialThetaQRootFamily.vbadWeightedFiber D (p : ℕ) := by
  exact tupleWeight_coordinate_sum D p j (Fin.last j)
    (fun v => Arithmetic.ordp v.1 (IutInitialThetaQRootFamily.vbadQrootAt D v.1))

theorem packetLogVolume_lower_bound (p : Nat.Primes) (j : ℕ) :
    -((j ^ 2 : ℕ) : ℝ) * Real.log (p : ℕ) *
        IutInitialThetaQRootFamily.vbadWeightedFiber D (p : ℕ) ≤ packetLogVolume D p j := by
  calc
    _ = ∑ c : Tuple D p j, tupleWeight D p j c *
        (-((j ^ 2 : ℕ) : ℝ) * Real.log (p : ℕ) *
          Arithmetic.ordp (c (Fin.last j)).1
            (IutInitialThetaQRootFamily.vbadQrootAt D (c (Fin.last j)).1)) := by
      rw [← tupleWeight_order_sum D p j, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ _ := Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left (componentLogVolume_region_lower_bound D p j c)
        (tupleWeight_pos D p j c).le

theorem packetLogVolume_bounds (p : Nat.Primes) (j : ℕ) :
    -((j ^ 2 : ℕ) : ℝ) * Real.log (p : ℕ) *
        IutInitialThetaQRootFamily.vbadWeightedFiber D (p : ℕ) ≤ packetLogVolume D p j ∧
      packetLogVolume D p j ≤ 0 :=
  ⟨packetLogVolume_lower_bound D p j, packetLogVolume_nonpos D p j⟩

end
end JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLowerBound
