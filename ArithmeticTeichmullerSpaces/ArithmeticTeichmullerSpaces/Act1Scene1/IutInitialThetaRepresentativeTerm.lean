import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSectionLink
import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQRepresentativeFiberMass

/-!
source-id: JT-SCENE1-INITIAL-THETA-REPRESENTATIVE-TERM
source: the actual canonical section Tate parameters, their positive q-order,
the residue characteristic, and the computed fibre-mass q-pilot bound.
fidelity: derives strictly positive representative terms and a nonzero finite
sum from InitialThetaData, then removes the independent nonnegativity input
from the representative upper bound. The actual source map, prime identity,
and local-term comparison remain explicit construction obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe u

noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

def iutInitialThetaSectionRepresentativeTerm
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace ↥D.prime.torsionField) : ℝ :=
  ((iutInitialThetaOddTateSectionTateParameterData D).qOrder w : ℝ) /
    (2 * (D.prime.ℓ : ℝ)) * Real.log (Arithmetic.residueChar w)

theorem iutInitialThetaSectionRepresentativeTerm_pos
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaOddTateSectionTateParameterData D).places) :
    0 < iutInitialThetaSectionRepresentativeTerm D w.1 := by
  have hOrder : 0 < ((iutInitialThetaOddTateSectionTateParameterData D).qOrder w.1 : ℝ) := by
    exact_mod_cast (iutInitialThetaOddTateSectionTateParameterData D).qOrder_pos
      (iutInitialThetaOddTateSectionTateParameterData_laws D) w.1 w.2
  have hEll : 0 < (D.prime.ℓ : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by decide : 0 < 5) D.prime.five_le
  have hPrime : 1 < (Arithmetic.residueChar w.1 : ℝ) := by
    exact_mod_cast (Arithmetic.residueChar_prime w.1).one_lt
  unfold iutInitialThetaSectionRepresentativeTerm
  exact mul_pos (div_pos hOrder (mul_pos (by norm_num) hEll)) (Real.log_pos hPrime)

theorem iutInitialThetaSectionRepresentativeSum_pos
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    0 < ∑ w : (iutInitialThetaOddTateSectionTateParameterData D).places,
      iutInitialThetaSectionRepresentativeTerm D w.1 := by
  obtain ⟨w, hw⟩ := (iutInitialThetaOddTateSectionTateParameterData_laws D).places_nonempty
  apply Finset.sum_pos
  · intro v hv
    exact iutInitialThetaSectionRepresentativeTerm_pos D v
  · exact ⟨⟨w, hw⟩, Finset.mem_univ _⟩

theorem Corollary312QPilotData.absLogQ_le_initialThetaSectionRepresentativeSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data D.F O p}
    (P : Corollary312QPilotData p T)
    (f : P.badFinset → (iutInitialThetaOddTateSectionTateParameterData D).places)
    (hTerm : ∀ w : P.badFinset,
      -Real.log (Corollary312PaperNormalizedSourceQFactor p T
        ⟨w.1, P.mem_bad p w.2⟩) =
          iutInitialThetaSectionRepresentativeTerm D (f w).1)
    (hPrime : ∀ w : P.badFinset,
      Arithmetic.residueChar w.1 = Arithmetic.residueChar (f w).1)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hRaw : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : T.ell = D.prime.ℓ) :
    P.absLogQ p ≤
      ∑ r : (iutInitialThetaOddTateSectionTateParameterData D).places,
        iutInitialThetaSectionRepresentativeTerm D r.1 := by
  classical
  have hEllPos : 0 < T.ell := by
    rw [hEll]
    exact Nat.lt_of_lt_of_le (by decide : 0 < 5) D.prime.five_le
  exact P.absLogQ_le_unweightedRepresentativeSum p f
    (fun r => iutInitialThetaSectionRepresentativeTerm D r.1) hTerm
    (fun r => Arithmetic.residueChar r.1) hPrime
    (fun r => (iutInitialThetaSectionRepresentativeTerm_pos D r).le)
    hOrder hRaw hEllPos

end
end JoshiTeich.Act1Scene1
