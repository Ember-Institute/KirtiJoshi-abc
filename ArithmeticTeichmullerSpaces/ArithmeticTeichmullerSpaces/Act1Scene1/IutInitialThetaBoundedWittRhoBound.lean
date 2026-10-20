import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittExpansionOperations

/-!
source-id: JT-SCENE1-INITIAL-THETA-BOUNDED-WITT-RHO-BOUND
source: Joshi II se:ff-rings / W(O_F) into B (511--512, 719--727), and
the rho-weighted coefficient bounds used for the Frechet B norms in Joshi
Teichmuller Spaces 2, §7--§9.
fidelity: records the explicit finite rho-weighted bound on the genuine
Teichmuller digits of an actual bounded Witt expansion. For 0 ≤ rho ≤ 1 this
bound follows from the existing uniform digit bound, and at rho = 1 it is
equivalent to the existing bounded-expansion witness. This is only a
rho-bound predicate; it does not define a numerical seminorm, a Frechet
completion, or the paper's completed B. Original proofs; Scene1/Derived;
Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaBoundedWittRhoBound

open JoshiTeich.Prologue InitialThetaTiltFontaine InitialThetaCanonicalGeometricFontaine
open InitialThetaBoundedWittLocalization
open InitialThetaBoundedWittExpansion
open WittTeichmullerExpansion
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrimeRho : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def HasRhoBoundedExpansion (rho : ℝ) (z : Ambient D w) : Prop :=
  ∃ m : ℕ, ∃ y : FieldWitt D w, ∃ c : ℕ → InitialThetaTiltField.Carrier D w,
    ∃ C : ℝ, 0 < C ∧ (∀ n : ℕ, ‖c n‖ ≤ C) ∧
      Expands (Arithmetic.residueChar w.1) y c ∧
      z * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
        algebraMap (FieldWitt D w) (Ambient D w) y ∧
      (∀ n : ℕ, ‖c n‖ * rho ^ n ≤ C)

theorem hasRhoBoundedExpansion_of_hasBoundedExpansion
    (rho : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (z : Ambient D w) (hz : HasBoundedExpansion D w z) :
    HasRhoBoundedExpansion D w rho z := by
  obtain ⟨m, y, c, C, hC, hbound, hc, hz⟩ := hz
  refine ⟨m, y, c, C, hC, hbound, hc, hz, ?_⟩
  intro n
  have hpow : rho ^ n ≤ 1 := pow_le_one₀ hrho0 hrho1
  exact (mul_le_of_le_one_right (norm_nonneg _) hpow).trans (hbound n)

theorem hasBoundedExpansion_of_hasRhoBoundedExpansion_one
    (z : Ambient D w) (hz : HasRhoBoundedExpansion D w 1 z) :
    HasBoundedExpansion D w z := by
  obtain ⟨m, y, c, C, hC, hbound, hc, hz, _⟩ := hz
  exact ⟨m, y, c, C, hC, hbound, hc, hz⟩

end
end JoshiTeich.Act1Scene1.InitialThetaBoundedWittRhoBound
