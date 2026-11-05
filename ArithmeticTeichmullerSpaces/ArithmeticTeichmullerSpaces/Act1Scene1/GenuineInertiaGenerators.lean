import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionPointInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineUnsignedNormalizationFields

/-!
source-id: JT-SCENE1-GENUINE-VALUATION-INERTIA-GENERATORS
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Pi1.lean`:240 and
`refer/iut/Iut/Anabelian/Genuine/Cover.lean`:72,111-116, used as mathematical
and API references only. The definitions and proofs below are independent.
fidelity: actual valuation-inertia generators over the elliptic base equal those
over every actual unsigned division cover. The proof uses the proved local
division-point inertia theorem and the actual unsigned Galois subgroup.
Joshi-adaptation: this supplies the generator-set comparison for the actual
elliptic function fields, with the effective level convention also at level zero.
boundary: Scene1/Derived. No fundamental-group quotient or comparison with the
etale fundamental group is constructed here. Closed normal inertia subgroups,
cover maps, Cartesian covering, core, cusp, theta-root, holomorphoid, and the
InitialThetaGeometryProducer obligations remain separate.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open scoped Classical
universe u
noncomputable section

variable {k : Type u} [Field k] (E : WeierstrassCurve k)

/-- The original valuation-inertia condition on the function-field closure. -/
def valuationInertiaAt (σ : Gal E) (W : ValuationSubring (Ω E)) : Prop :=
  ∀ a ∈ W, W.valuation (σ a - a) < 1

variable [E.IsElliptic]

/-- Valuation-inertia generators over the actual elliptic base generic point. -/
def baseValuationInertiaGenerators : Set (Gal E) :=
  {σ | act E σ (genericPoint E) = genericPoint E ∧
    ∃ W : ValuationSubring (Ω E),
      (∀ c : k, algebraMap k (Ω E) c ∈ W) ∧ xG E ∈ W ∧
        valuationInertiaAt E σ W}

variable [CharZero k]

/-- Valuation-inertia generators over an actual unsigned division cover. -/
def unsignedValuationInertiaGenerators (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) : Set (Gal E) :=
  {σ | act E σ (Qpt E ell) - Qpt E ell ∈ Mbar E ell M ∧
    ∃ W : ValuationSubring (Ω E),
      (∀ c : k, algebraMap k (Ω E) c ∈ W) ∧ xG E ∈ W ∧
        valuationInertiaAt E σ W}

/-- Unsigned cover generators fix the base generic point with the same valuation witness. -/
theorem unsignedValuationInertiaGenerators_subset_base (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    unsignedValuationInertiaGenerators E ell M ⊆ baseValuationInertiaGenerators E := by
  intro σ hσ
  obtain ⟨hT, W, hk, hx, hI⟩ := hσ
  have hH : σ ∈ Hgp E ell M false := by
    refine ⟨(1 : ℤ), Or.inl rfl, ?_⟩
    simpa only [one_smul] using hT
  exact ⟨act_generic_of_unsigned E hH, W, hk, hx, hI⟩

/-- Base valuation inertia fixes the actual division point, hence gives a cover generator. -/
theorem baseValuationInertiaGenerators_subset_unsigned (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    baseValuationInertiaGenerators E ⊆ unsignedValuationInertiaGenerators E ell M := by
  intro σ hσ
  obtain ⟨hG, W, hk, hx, hI⟩ := hσ
  have hQ : act E σ (Qpt E ell) = Qpt E ell :=
    valuationInertia_fixes_divSys E σ W hk hx hI hG (effLevel ell) (effLevel_pos ell)
  have hT : act E σ (Qpt E ell) - Qpt E ell ∈ Mbar E ell M := by
    rw [hQ, sub_self]
    exact (Mbar E ell M).zero_mem
  exact ⟨hT, W, hk, hx, hI⟩

/-- The actual unsigned division covers have exactly the base valuation-inertia generators. -/
theorem unsignedValuationInertiaGenerators_eq_base (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    unsignedValuationInertiaGenerators E ell M = baseValuationInertiaGenerators E :=
  Set.Subset.antisymm (unsignedValuationInertiaGenerators_subset_base E ell M)
    (baseValuationInertiaGenerators_subset_unsigned E ell M)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
