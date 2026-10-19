import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerClosureTransport
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCoefficientChange

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-RATIONAL-CLOSURE-TRANSPORT
source: Joshi I ss:distinct-kummer-theories/pr:galois-cohomology-and-teich
(1588--1632), and Joshi III integral/rational Kummer coefficients (3190--3236).
fidelity: natural preferred-closure transport determines a Z_p unit between
independently chosen Tate bases. The actual cyclotomic characters agree
under Galois conjugation. Rational coefficient transport includes the unit,
and commutes with the original integral-to-rational H1 comparison. Root-tower
Kummer classes transport to the same base element in the target closure.
No alignment of Tate bases or arbitrary H1 identification is assumed.
Fixed base field only; holomorphoid producers and H1_e/BK remain separate.
Original proofs; no reference code copied; Prologue-R5 unchanged.
-/
namespace JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω Ξ : Type v} [Field Ω] [Field Ξ]
variable [Algebra K Ω] [Algebra K Ξ]
variable [CharZero Ω] [IsAlgClosed Ω] [CharZero Ξ] [IsAlgClosed Ξ]
variable (e : Ω ≃ₐ[K] Ξ) (p : ℕ) [Fact p.Prime]

def coordinateEquiv : ℤ_[p] ≃L[ℤ_[p]] ℤ_[p] :=
  ((TateBasis.equiv (p := p) (Ω := Ω)).trans (ClosureTransport.tateEquiv e p)).trans
    (TateBasis.equiv (p := p) (Ω := Ξ)).symm

def basisScalar : ℤ_[p] := coordinateEquiv e p 1

theorem coordinateEquiv_apply (r : ℤ_[p]) :
    coordinateEquiv e p r = r * basisScalar e p := by
  have h := (coordinateEquiv e p).map_smul r 1
  simpa only [basisScalar, smul_eq_mul, mul_one] using h

theorem coordinate_tateEquiv (x : Additive (cyclotomicTateGroup p Ω)) :
    (TateBasis.equiv (p := p) (Ω := Ξ)).symm (ClosureTransport.tateEquiv e p x) =
      (TateBasis.equiv (p := p) (Ω := Ω)).symm x * basisScalar e p := by
  have h := coordinateEquiv_apply e p ((TateBasis.equiv (p := p) (Ω := Ω)).symm x)
  change (TateBasis.equiv (p := p) (Ω := Ξ)).symm
    (ClosureTransport.tateEquiv e p ((TateBasis.equiv (p := p) (Ω := Ω))
      ((TateBasis.equiv (p := p) (Ω := Ω)).symm x))) = _ at h
  rwa [(TateBasis.equiv (p := p) (Ω := Ω)).apply_symm_apply] at h

theorem basisScalar_mul_inverse :
    basisScalar e p * (coordinateEquiv e p).symm 1 = 1 := by
  have h := (coordinateEquiv e p).apply_symm_apply 1
  rw [coordinateEquiv_apply] at h
  exact (mul_comm _ _).trans h

def basisUnit : ℤ_[p]ˣ := Units.mkOfMulEqOne (basisScalar e p)
  ((coordinateEquiv e p).symm 1) (basisScalar_mul_inverse e p)

theorem basisUnit_val : (basisUnit e p : ℤ_[p]) = basisScalar e p := rfl

variable [Algebra.IsIntegral K Ω] [Algebra.IsIntegral K Ξ]

theorem character_eq (σ : Ξ ≃ₐ[K] Ξ) :
    Cyclotomic.character (K := K) (Ω := Ω) p (GaloisClosureTransport.groupIso e σ) =
      Cyclotomic.character (K := K) (Ω := Ξ) p σ := by
  apply Units.ext
  have h := congrArg (TateBasis.equiv (p := p) (Ω := Ξ)).symm
    (ClosureTransport.tateEquiv_equivariant e p σ (TateBasis.equiv (p := p) (Ω := Ω) 1))
  rw [coordinate_tateEquiv, Cyclotomic.coordinate_action_character,
    Cyclotomic.coordinate_action_character, coordinate_tateEquiv,
    (TateBasis.equiv (p := p) (Ω := Ω)).symm_apply_apply, mul_one, one_mul] at h
  apply mul_right_cancel₀ (basisUnit e p).ne_zero
  exact h

def coefficientEquiv : Rational.topRep (K := K) (Ω := Ω) p ≃L[ℚ_[p]]
    Rational.topRep (K := K) (Ω := Ξ) p :=
  ((basisUnit e p).map (PadicInt.Coe.ringHom (p := p)).toMonoidHom) •
    ContinuousLinearEquiv.refl ℚ_[p] (ULift.{v} ℚ_[p])

theorem coefficientEquiv_down (q : Rational.topRep (K := K) (Ω := Ω) p) :
    (coefficientEquiv e p q).down = (basisScalar e p : ℚ_[p]) * q.down := rfl

theorem coefficientEquiv_equivariant (σ : Ξ ≃ₐ[K] Ξ)
    (q : Rational.topRep (K := K) (Ω := Ω) p) :
    coefficientEquiv e p ((Rational.topRep p).ρ (GaloisClosureTransport.groupIso e σ) q) =
      (Rational.topRep p).ρ σ (coefficientEquiv e p q) := by
  apply ULift.ext
  change (basisScalar e p : ℚ_[p]) *
      Rational.representation p (GaloisClosureTransport.groupIso e σ) q.down =
    Rational.representation p σ ((basisScalar e p : ℚ_[p]) * q.down)
  rw [Rational.representation_apply, Rational.representation_apply, character_eq]
  ring

def marking : ContinuousH1Transport.Marking
    (Rational.topRep (K := K) (Ω := Ω) p) (Rational.topRep (K := K) (Ω := Ξ) p) where
  groupIso := GaloisClosureTransport.groupIso e
  coefficientIso := coefficientEquiv e p
  equivariant := coefficientEquiv_equivariant e p

def h1Equiv : continuousCohomology 1 (Rational.topRep (K := K) (Ω := Ω) p) ≃L[ℚ_[p]]
    continuousCohomology 1 (Rational.topRep (K := K) (Ω := Ξ) p) := (marking e p).h1Equiv

theorem coefficient_change (x : padicTateTopRep (K := K) (Ω := Ω) p) :
    coefficientEquiv e p (Rational.integralCoefficient p x) =
      Rational.integralCoefficient p (ClosureTransport.tateEquiv e p x) := by
  apply ULift.ext
  change (basisScalar e p : ℚ_[p]) *
      ((TateBasis.equiv (p := p) (Ω := Ω)).symm x : ℚ_[p]) =
    ((TateBasis.equiv (p := p) (Ω := Ξ)).symm (ClosureTransport.tateEquiv e p x) : ℚ_[p])
  have h := congrArg (fun r : ℤ_[p] => (r : ℚ_[p])) (coordinate_tateEquiv e p x)
  rw [PadicInt.coe_mul] at h
  exact (mul_comm _ _).trans h.symm

theorem h1Equiv_standardMap
    (x : continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p)) :
    h1Equiv e p (Rational.standardMap p x) =
      Rational.standardMap p (ClosureTransport.h1Equiv e p x) := by
  obtain ⟨f, hf, rfl⟩ := ContinuousH1Recognition.classOf_surjective _ x
  change (marking e p).h1Equiv
    (ContinuousH1Semilinear.map _ _ (Rational.integralCoefficient p)
      (Rational.integralCoefficient_equivariant p) (ContinuousH1Homogeneous.classOf _ f hf)) = _
  rw [ContinuousH1Semilinear.map_classOf, (marking e p).h1Equiv_classOf]
  change _ = Rational.standardMap p
    ((ClosureTransport.marking e p).h1Equiv (ContinuousH1Homogeneous.classOf _ f hf))
  rw [(ClosureTransport.marking e p).h1Equiv_classOf, Rational.standardMap,
    ContinuousH1Semilinear.map_classOf]
  congr 1
  ext σ
  exact coefficient_change e p (f (GaloisClosureTransport.groupIso e σ))

theorem h1Equiv_rootTower {a : K} (T : RootTower (Ω := Ω) p a) (ha : a ≠ 0) :
    h1Equiv e p (Rational.classOfCocycle p
      (T.continuousCocycleValue (Fact.out : p.Prime).pos ha)) =
    Rational.classOfCocycle p
      ((ClosureTransport.mapRootTower e T).continuousCocycleValue (Fact.out : p.Prime).pos ha) := by
  rw [← Rational.standardMap_classOfCocycle, h1Equiv_standardMap,
    ClosureTransport.h1Equiv_rootTower, Rational.standardMap_classOfCocycle]

theorem h1Equiv_kummerClass {a : K} (T : RootTower (Ω := Ω) p a) (ha : a ≠ 0) :
    h1Equiv e p (Rational.toH1 p (T.kummerClass (Fact.out : p.Prime).pos ha)) =
      Rational.toH1 p ((rootTower (Ω := Ξ) p (Fact.out : p.Prime).pos a).kummerClass
        (Fact.out : p.Prime).pos ha) := by
  rw [← Rational.standardMap_toPadicH1, h1Equiv_standardMap,
    ClosureTransport.h1Equiv_kummerClass, Rational.standardMap_toPadicH1]

end
end JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport
