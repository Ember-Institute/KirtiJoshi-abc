import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusCompletion
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoExpansion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ALL-RADIUS-EXPANSION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, simultaneous
convergence for the family of rho norms on the bounded period subring.
fidelity: the same genuine integral Witt digit partial sums converge in
the complete diagonal-closure ring. The same numerator and localization
denominator give convergent expansions of every original bounded Witt
element at all radii simultaneously. No radius-dependent choices of
numerators or digits are used. Original proofs; no reference code copied.
boundary: Scene1/Derived; no metrizability, Frechet algebra, Frobenius
period eigenspace, or paper B identification is asserted. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusExpansion

open JoshiTeich.Prologue
open InitialThetaBoundedWittLocalization
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Ainf := InitialThetaTiltFontaine.Ainf D w
abbrev Carrier := InitialThetaWittAllRadiusCompletion.Carrier D w

def ainfMap : Ainf D w →+* Carrier D w :=
  (InitialThetaWittAllRadiusCompletion.inclusion D w).comp (inclusion D w)

theorem tendsto_partial (a : Ainf D w) :
    Filter.Tendsto
      (fun N : ℕ => ainfMap D w (InitialThetaWittRhoExpansion.digitPartialSum D w a N))
      Filter.atTop (𝓝 (ainfMap D w a)) := by
  apply (InitialThetaWittAllRadiusCompletion.tendsto_iff_coordinates D w _ _ _).mpr
  intro ρ
  exact InitialThetaWittRhoExpansion.tendsto_partial D w ρ a

theorem exists_localized_expansion (x : InitialThetaBoundedWittLocalization.Ring D w) :
    ∃ a : Ainf D w, ∃ b : InitialThetaBoundedWittLocalization.Ring D w,
      inclusion D w a * b = x ∧
      Filter.Tendsto
        (fun N : ℕ => InitialThetaWittAllRadiusCompletion.inclusion D w
          (inclusion D w (InitialThetaWittRhoExpansion.digitPartialSum D w a N) * b))
        Filter.atTop (𝓝 (InitialThetaWittAllRadiusCompletion.inclusion D w x)) := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (denominator D w) x
  obtain ⟨u, hu⟩ := ((IsLocalization.Away.algebraMap_isUnit (denominator D w)
    (S := InitialThetaBoundedWittLocalization.Ring D w)).pow m)
  have hab : inclusion D w a * (u⁻¹ : _) = x := by
    change algebraMap (InitialThetaTiltFontaine.Ainf D w)
      (InitialThetaBoundedWittLocalization.Ring D w) a * (u⁻¹ : _) = x
    rw [← ha, ← hu, mul_assoc, Units.mul_inv, mul_one]
  refine ⟨a, (u⁻¹ : _), hab, ?_⟩
  have h := (tendsto_partial D w a).mul_const
    (InitialThetaWittAllRadiusCompletion.inclusion D w (u⁻¹ : _))
  simpa only [ainfMap, RingHom.comp_apply, ← map_mul, hab] using h

theorem exists_simultaneous_coordinate_expansion
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    ∃ a : Ainf D w, ∃ b : InitialThetaBoundedWittLocalization.Ring D w,
      inclusion D w a * b = x ∧
      ∀ ρ : InitialThetaWittRhoCompletion.Radius,
        Filter.Tendsto
          (fun N : ℕ => InitialThetaWittRhoCompletion.inclusion D w ρ
            (inclusion D w (InitialThetaWittRhoExpansion.digitPartialSum D w a N) * b))
          Filter.atTop (𝓝 (InitialThetaWittRhoCompletion.inclusion D w ρ x)) := by
  obtain ⟨a, b, hab, h⟩ := exists_localized_expansion D w x
  exact ⟨a, b, hab,
    (InitialThetaWittAllRadiusCompletion.tendsto_iff_coordinates D w _ _ _).mp h⟩

end
end JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusExpansion
