import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionFieldBaseTranslation
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedQuotient

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the actual unsigned stabilizer `Hgp` and proved ambient torsion translations.
fidelity: original proof. Extracts the unique constant-point displacement
of each actual unsigned stabilizer element, proves multiplicativity, and
realizes every rational torsion displacement by the established ambient lift.
boundary: Scene1/Derived. The consumer identifies the actual stabilizer
quotient with TK/M. No infinity-boundary equivalence is asserted.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve
open scoped Classical
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

private theorem exists_unsigned_displacement
    (n : ℕ) (TK : AddSubgroup E.toAffine.Point) (σ : Hgp E n TK false) :
    ∃ T : TK, base E (T : E.toAffine.Point) = act E σ.val (Qpt E n) - Qpt E n := by
  have hm := (mem_Hgp_false E).mp σ.property
  obtain ⟨T, hT, hEq⟩ := hm
  exact ⟨⟨T, hT.1⟩, hEq⟩

/-- The actual rational displacement of an unsigned stabilizer element. -/
def torsionTranslationDisplacementPoint
    (n : ℕ) (TK : AddSubgroup E.toAffine.Point) (σ : Hgp E n TK false) : TK :=
  Classical.choose (exists_unsigned_displacement E n TK σ)

theorem torsionTranslationDisplacementPoint_spec
    (n : ℕ) (TK : AddSubgroup E.toAffine.Point) (σ : Hgp E n TK false) :
    base E (torsionTranslationDisplacementPoint E n TK σ : E.toAffine.Point) =
      act E σ.val (Qpt E n) - Qpt E n :=
  Classical.choose_spec (exists_unsigned_displacement E n TK σ)

private theorem base_injective : Function.Injective (base E) :=
  pointMap_injective E (algebraMap k (Ω E))

private theorem torsionTranslationDisplacementPoint_one
    (n : ℕ) (TK : AddSubgroup E.toAffine.Point) :
    torsionTranslationDisplacementPoint E n TK 1 = 0 := by
  apply Subtype.ext
  apply base_injective E
  rw [torsionTranslationDisplacementPoint_spec, Subgroup.coe_one, act_one,
    sub_self, AddSubgroup.coe_zero, map_zero]

private theorem torsionTranslationDisplacementPoint_mul
    (n : ℕ) (TK : AddSubgroup E.toAffine.Point) (σ τ : Hgp E n TK false) :
    torsionTranslationDisplacementPoint E n TK (σ * τ) =
      torsionTranslationDisplacementPoint E n TK σ +
        torsionTranslationDisplacementPoint E n TK τ := by
  apply Subtype.ext
  apply base_injective E
  change base E (torsionTranslationDisplacementPoint E n TK (σ * τ) : E.toAffine.Point) =
    base E ((torsionTranslationDisplacementPoint E n TK σ : E.toAffine.Point) +
      (torsionTranslationDisplacementPoint E n TK τ : E.toAffine.Point))
  rw [map_add, torsionTranslationDisplacementPoint_spec,
    torsionTranslationDisplacementPoint_spec, torsionTranslationDisplacementPoint_spec,
    Subgroup.coe_mul, act_mul]
  have hτ : act E τ.val (Qpt E n) = Qpt E n +
      base E (torsionTranslationDisplacementPoint E n TK τ : E.toAffine.Point) := by
    rw [torsionTranslationDisplacementPoint_spec]
    abel
  rw [hτ, map_add, act_base]
  rw [torsionTranslationDisplacementPoint_spec]
  abel

/-- Actual unsigned stabilizer elements map to their rational torsion translations. -/
def torsionTranslationDisplacement
    (n : ℕ) (_hn : 0 < n) (TK : AddSubgroup E.toAffine.Point)
    (_hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n) :
    Hgp E n TK false →* Multiplicative TK where
  toFun σ := Multiplicative.ofAdd (torsionTranslationDisplacementPoint E n TK σ)
  map_one' := congrArg Multiplicative.ofAdd
    (torsionTranslationDisplacementPoint_one E n TK)
  map_mul' σ τ := congrArg Multiplicative.ofAdd
    (torsionTranslationDisplacementPoint_mul E n TK σ τ)

/-- The homomorphism retains the same actual displacement in the same closure. -/
theorem torsionTranslationDisplacement_spec
    (n : ℕ) (hn : 0 < n) (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n)
    (σ : Hgp E n TK false) :
    base E ((Multiplicative.toAdd (torsionTranslationDisplacement E n hn TK hTK σ) : TK) :
        E.toAffine.Point) = act E σ.val (Qpt E n) - Qpt E n :=
  torsionTranslationDisplacementPoint_spec E n TK σ

/-- Every rational torsion displacement is realized by an actual ambient automorphism. -/
theorem torsionTranslationDisplacement_surjective
    (n : ℕ) (hn : 0 < n) (TK : AddSubgroup E.toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy E.toAffine.Point n) :
    Function.Surjective (torsionTranslationDisplacement E n hn TK hTK) := by
  intro y
  let T : TK := Multiplicative.toAdd y
  have hT : n • (T : E.toAffine.Point) = 0 :=
    AddSubgroup.torsionBy.nsmul_iff.mp (hTK T.property)
  obtain ⟨σ, hσ⟩ := exists_ambient_divisionPoint_translation E n hn
    (T : E.toAffine.Point) hT
  have hd : act E σ (Qpt E n) - Qpt E n = base E (T : E.toAffine.Point) := by
    rw [hσ]
    abel
  have hmem : σ ∈ Hgp E n TK false := by
    rw [mem_Hgp_false, hd]
    have heff : effLevel n = n := by simp only [effLevel, if_neg (Nat.ne_of_gt hn)]
    refine ⟨(T : E.toAffine.Point), ⟨T.property, ?_⟩, rfl⟩
    rw [heff]
    exact hTK T.property
  refine ⟨⟨σ, hmem⟩, ?_⟩
  apply Multiplicative.ext
  apply Subtype.ext
  apply base_injective E
  change base E (torsionTranslationDisplacementPoint E n TK ⟨σ, hmem⟩ : E.toAffine.Point) =
    base E (T : E.toAffine.Point)
  exact (torsionTranslationDisplacementPoint_spec E n TK ⟨σ, hmem⟩).trans hd

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
