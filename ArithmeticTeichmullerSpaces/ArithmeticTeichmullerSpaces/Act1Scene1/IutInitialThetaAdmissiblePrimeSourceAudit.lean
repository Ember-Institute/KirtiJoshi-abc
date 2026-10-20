import ArithmeticTeichmullerSpaces.Act1Scene1.IutModEllRepAdmissibleAdapter
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTorsionRationality
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaMaximalPrimeData

/-!
source-id: JT-SCENE1-INITIAL-THETA-ADMISSIBLE-PRIME-SOURCE-AUDIT
source: Joshi III ss:theta-data-fixing2 (1023--1055), IUT I Definition 3.1(b--c),
and the reference `ThetaData/AdmissiblePrime.lean`.
fidelity: packages the admissible-prime fields already chosen by one actual
InitialThetaData. The representation is the genuine elliptic-torsion action,
its SL2 image and open kernel are retained, the torsion field is the fixed field
of that same representation, and all residue/q-order coprimality laws are
projected from the same prime data. This is a source audit package, not an
existence theorem for InitialThetaData or a new prime constructor.
Original proofs; no reference code copied; Prologue-R5 unchanged.
-/
namespace JoshiTeich.Act1Scene1.InitialThetaAdmissiblePrimeSourceAudit

open JoshiTeich.Prologue JoshiTeich.ReferenceIut
open NumberField
open scoped Classical MatrixGroups
universe u
noncomputable section

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG)

structure Source (D : InitialThetaData AG TG) where
  ell_prime : D.prime.ℓ.Prime
  five_le : 5 ≤ D.prime.ℓ
  six_torsion_rational : SixTorsionRational D.F D.E D.Fbar
  representation : (D.Fbar ≃ₐ[D.F] D.Fbar) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod D.prime.ℓ)
  representation_spec : ∀ σ P,
    D.prime.torsionBasis ⟨galPointMap D.F D.E D.Fbar σ P.1,
      galPointMap_torsionBy D.F D.E D.Fbar σ P.2⟩ =
      (representation σ : Matrix (Fin 2) (Fin 2) (ZMod D.prime.ℓ)).mulVec
        (D.prime.torsionBasis P)
  sl2_image : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod D.prime.ℓ),
    A.toGL ∈ representation.range
  kernel_open : IsOpen (representation.ker : Set (D.Fbar ≃ₐ[D.F] D.Fbar))
  torsion_field : IntermediateField D.F D.Fbar
  torsion_field_eq_fixed :
    torsion_field = IntermediateField.fixedField representation.ker
  galois_mod_degree_prime :
    IsGaloisOfDegreePrimeTo D.F D.E D.prime.ℓ
  residue_coprime : ∀ v ∈ D.VBad, Nat.Coprime D.prime.ℓ (residueChar v)
  q_order_coprime : ∀ w (hw : w ∈ badPlacesOver D.F D.E D.VBad),
    (D.prime.tate w hw).toOrdered (D.prime.unif_isUniformizer w hw) |>.PrimeToOrder D.prime.ℓ

def source : Source D where
  ell_prime := D.prime.ℓ_prime
  five_le := D.prime.five_le
  six_torsion_rational := D.global.six_torsion_rational
  representation := D.prime.rep
  representation_spec := D.prime.rep_spec
  sl2_image := D.prime.sl_le_range
  kernel_open := D.prime.ker_isOpen
  torsion_field := D.prime.torsionField
  torsion_field_eq_fixed := rfl
  galois_mod_degree_prime := D.prime.galois_deg_prime
  residue_coprime := D.prime.residueChar_coprime
  q_order_coprime := D.prime.q_order_coprime

theorem source_ell : D.prime.ℓ = D.prime.ℓ := rfl
theorem source_torsion_field : (source D).torsion_field = D.prime.torsionField := rfl
theorem source_representation : (source D).representation = D.prime.rep := rfl

theorem source_fixed_field_eq_rep_adapter :
    IutCurveModEllRepData.torsionField D.E D.Fbar
        (iutInitialThetaModEllRepData D) = (source D).torsion_field := by
  rfl

theorem source_sl2_image (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod D.prime.ℓ)) :
    A.toGL ∈ (source D).representation.range :=
  (source D).sl2_image A

theorem source_residue_coprime (v : FinitePlace ↥(fieldOfModuli D.F D.E))
    (hv : v ∈ D.VBad) : Nat.Coprime D.prime.ℓ (residueChar v) :=
  (source D).residue_coprime v hv

theorem source_q_order_coprime
    (w : FinitePlace D.F) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    (D.prime.tate w hw).toOrdered (D.prime.unif_isUniformizer w hw) |>.PrimeToOrder D.prime.ℓ :=
  (source D).q_order_coprime w hw

end
end JoshiTeich.Act1Scene1.InitialThetaAdmissiblePrimeSourceAudit
