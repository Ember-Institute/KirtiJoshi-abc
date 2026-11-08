import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedQuotient
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.DivisionFields
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.Normalization
import Mathlib.SetTheory.Cardinal.Finite

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the actual division-point multiplication equation; the proved geometric
torsion cardinality and the seed's actual rational torsion cardinality.
fidelity: a rational torsion subgroup with the full geometric cardinality
exhausts ambient torsion. The full unsigned translation subgroup is therefore
the level-one unsigned subgroup, with equality of their actual fixed fields.
boundary: no assertion about the number of infinity primes is made here.
Original proof.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open scoped Classical
universe u
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

/-- The original point map restricted to the actual n-torsion subgroups. -/
def baseTorsionMap (n : ℕ) :
    AddSubgroup.torsionBy E.toAffine.Point n →+
      AddSubgroup.torsionBy (Pt E) n :=
  ((base E).domRestrict _).codRestrict _ fun T =>
    AddSubgroup.torsionBy.nsmul_iff.mpr (by
      have hT := AddSubgroup.torsionBy.nsmul_iff.mp T.property
      change n • ((base E).domRestrict _ T) = 0
      rw [← map_nsmul]
      exact congrArg (base E) hT)

theorem baseTorsionMap_injective (n : ℕ) : Function.Injective (baseTorsionMap E n) := by
  intro T U h
  apply Subtype.ext
  exact pointMap_injective E (algebraMap k (Ω E)) (congrArg Subtype.val h)

/-- The known full cardinality proves that every ambient torsion point is rational. -/
theorem baseTorsionMap_surjective (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point n) = n ^ 2) :
    Function.Surjective (baseTorsionMap E n) := by
  have hgeom : Nat.card (AddSubgroup.torsionBy (Pt E) n) = n ^ 2 :=
    JoshiTeich.Act1Scene1.iutGeometricTorsion_card (E⁄(Ω E)) n hn.ne'
  letI : Finite (AddSubgroup.torsionBy (Pt E) n) :=
    Nat.finite_of_card_ne_zero (by rw [hgeom]; exact pow_ne_zero 2 hn.ne')
  exact ((Nat.bijective_iff_injective_and_card (baseTorsionMap E n)).mpr
    ⟨baseTorsionMap_injective E n, hcard.trans hgeom.symm⟩).surjective

/-- Full rational torsion makes the translation subgroup exactly the level-one subgroup. -/
theorem Hgp_fullTorsion_false_eq_levelOne (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point n) = n ^ 2) :
    Hgp E n (AddSubgroup.torsionBy E.toAffine.Point n) false = Hgp E 1 ⊥ false := by
  apply le_antisymm
  · apply Hgp_le E hn (mul_one n)
    · intro T hT
      simpa only [AddSubgroup.mem_bot] using AddSubgroup.torsionBy.nsmul_iff.mp hT
    · exact fun h => h
  · intro σ hσ
    have hfix : act E σ (genericPoint E) = genericPoint E := by
      simpa only [Qpt_one] using (mem_Hgp_bot_false_iff E 1 σ).mp hσ
    have hmul : n • Qpt E n = genericPoint E := by
      rw [Qpt_eq_divSys E hn]
      exact nsmul_divSys E n hn
    have hT : n • (act E σ (Qpt E n) - Qpt E n) = 0 := by
      rw [nsmul_sub, ← map_nsmul, hmul, hfix, sub_self]
    let T : AddSubgroup.torsionBy (Pt E) n :=
      ⟨act E σ (Qpt E n) - Qpt E n, AddSubgroup.torsionBy.nsmul_iff.mpr hT⟩
    obtain ⟨R, hR⟩ := baseTorsionMap_surjective E n hn hcard T
    have hRval : base E R.val = act E σ (Qpt E n) - Qpt E n :=
      congrArg Subtype.val hR
    rw [mem_Hgp_false]
    refine ⟨R.val, ⟨R.property, ?_⟩, hRval⟩
    rw [show effLevel n = n by simp [effLevel, hn.ne']]
    exact R.property

/-- Equality of actual fixed fields, not an abstract field isomorphism. -/
theorem stabilizerField_fullTorsion_false_eq_levelOne (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point n) = n ^ 2) :
    stabilizerField E n (AddSubgroup.torsionBy E.toAffine.Point n) false =
      stabilizerField E 1 ⊥ false := by
  unfold stabilizerField
  rw [Hgp_fullTorsion_false_eq_levelOne E n hn hcard]

/-- The same equality after changing the named base to the x-line. -/
theorem normalizationField_fullTorsion_false_eq_levelOne (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point n) = n ^ 2) :
    normalizationField E n (AddSubgroup.torsionBy E.toAffine.Point n) false =
      normalizationField E 1 ⊥ false := by
  unfold normalizationField
  rw [stabilizerField_fullTorsion_false_eq_levelOne E n hn hcard]

/-- The full-translation fixed field is the embedded elliptic function field. -/
def fullTorsionBaseFunctionFieldEquiv (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point n) = n ^ 2) :
    E.toAffine.FunctionField ≃+*
      stabilizerField E n (AddSubgroup.torsionBy E.toAffine.Point n) false :=
  (baseFunctionFieldEquiv E).trans
    (IntermediateField.equivOfEq
      (stabilizerField_fullTorsion_false_eq_levelOne E n hn hcard).symm).toRingEquiv

@[simp] theorem coe_fullTorsionBaseFunctionFieldEquiv (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point n) = n ^ 2)
    (f : E.toAffine.FunctionField) :
    ((fullTorsionBaseFunctionFieldEquiv E n hn hcard f :
      stabilizerField E n (AddSubgroup.torsionBy E.toAffine.Point n) false) : Ω E) =
        ιF E f := by
  change ((baseFunctionFieldEquiv E f : stabilizerField E 1 ⊥ false) : Ω E) = ιF E f
  rfl

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

/-- Equality of actual subfields identifies the integral closures without changing ambient values. -/
def coordRingEquivOfEq {L L' : IntermediateField (rationalBase k t) Ω} (h : L = L') :
    coordRing t L ≃+* coordRing t L' :=
  RingEquiv.cast (R := fun N : IntermediateField (rationalBase k t) Ω => coordRing t N) h

@[simp] theorem coe_coordRingEquivOfEq
    {L L' : IntermediateField (rationalBase k t) Ω} (h : L = L') (a : coordRing t L) :
    (((coordRingEquivOfEq h a : coordRing t L') : L') : Ω) = ((a : L) : Ω) := by
  subst L'
  rfl

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
