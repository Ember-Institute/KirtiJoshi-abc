import ArithmeticTeichmullerSpaces.Act1Scene1.DivisionPointInertia
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.DivisionFields

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Inertia.lean`, inertia_fixes_division;
`Genuine/Cover.lean`, inertia over the base curve fixes division coordinates.
fidelity: valuation inertia over the actual base-curve generic point fixes every
actual division point and belongs to every actual unsigned torsion-translation
subgroup. It fixes the corresponding actual unsigned fixed fields pointwise.
boundary: Scene1/Derived. This is the valuation-inertia statement. The comparison
with normalization-prime inertia and unramified covering remains open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped Classical
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- Base-curve valuation inertia fixes every actual positive-level division point. -/
theorem valuationInertia_fixes_divSys (σ : Gal E) (W : ValuationSubring (Ω E))
    (hk : ∀ c : k, algebraMap k (Ω E) c ∈ W) (hx : xG E ∈ W)
    (hσ : ∀ a ∈ W, W.valuation (σ a - a) < 1)
    (hG : act E σ (genericPoint E) = genericPoint E) (n : ℕ) (hn : 0 < n) :
    act E σ (divSys E n) = divSys E n :=
  DivisionPointInertia.inertia_fixes_of_nsmul_valuation E W hk (σk E σ) hσ n hn
    (nonsingular_generic E) hx hG (divSys E n) (nsmul_divSys E n hn)

theorem valuationInertia_mem_QField_fixing (σ : Gal E) (W : ValuationSubring (Ω E))
    (hk : ∀ c : k, algebraMap k (Ω E) c ∈ W) (hx : xG E ∈ W)
    (hσ : ∀ a ∈ W, W.valuation (σ a - a) < 1)
    (hG : act E σ (genericPoint E) = genericPoint E) (ell : ℕ) :
    σ ∈ (QField E ell).fixingSubgroup :=
  (mem_QField_fixing_iff E ell σ).mpr
    ((act_eq_self_iff_coordinates E σ (Qpt E ell)).mp
      (valuationInertia_fixes_divSys E σ W hk hx hσ hG (effLevel ell) (effLevel_pos ell)))

theorem valuationInertia_mem_unsignedGroup (σ : Gal E) (W : ValuationSubring (Ω E))
    (hk : ∀ c : k, algebraMap k (Ω E) c ∈ W) (hx : xG E ∈ W)
    (hσ : ∀ a ∈ W, W.valuation (σ a - a) < 1)
    (hG : act E σ (genericPoint E) = genericPoint E)
    (ell : ℕ) (M : AddSubgroup E.toAffine.Point) : σ ∈ Hgp E ell M false :=
  QField_fixing_le E ell M false
    (valuationInertia_mem_QField_fixing E σ W hk hx hσ hG ell)

/-- This inertia acts trivially on the actual unsigned cover function field. -/
theorem valuationInertia_fixes_unsignedField (σ : Gal E) (W : ValuationSubring (Ω E))
    (hk : ∀ c : k, algebraMap k (Ω E) c ∈ W) (hx : xG E ∈ W)
    (hσ : ∀ a ∈ W, W.valuation (σ a - a) < 1)
    (hG : act E σ (genericPoint E) = genericPoint E)
    (ell : ℕ) (M : AddSubgroup E.toAffine.Point) (x : stabilizerField E ell M false) :
    σ (x : Ω E) = (x : Ω E) :=
  ((IntermediateField.mem_fixedField_iff _ _).mp x.2) σ
    (valuationInertia_mem_unsignedGroup E σ W hk hx hσ hG ell M)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
