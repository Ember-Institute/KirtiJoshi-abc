import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittIntegralImageTopology
import Mathlib.Topology.Sequences

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-INTEGRAL-IMAGE-CLOSED
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, existence
of original integral Witt representatives of analytic limits.
fidelity: each original Ainf image is closed in the original rho
completion. A rho-Cauchy integral sequence converges to an actual Ainf
image, and its same coefficients give convergence at every radius.
Annular coordinate limits of a single integral sequence therefore have
one simultaneous original Ainf representative.
Faithfulness identifies the integral image in the full common ring as
the preimage of any single-radius integral image, hence also closed.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no integral approximation of the annular
eigen exponential is supplied as input or asserted to exist. That
remaining construction and full period representation stay open. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittIntegralImageClosed

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittRhoCoefficientLimits InitialThetaWittIntegralImageTopology
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

theorem exists_integral_limit_of_cauchy (ρ : Radius) (a : ℕ → InitialThetaTiltFontaine.Ainf D w)
    (ha : CauchySeq (fun m => InitialThetaWittRhoExpansion.ainfMap D w ρ (a m))) :
    ∃ b : InitialThetaTiltFontaine.Ainf D w, ∀ s : Radius,
      Filter.Tendsto (fun m => InitialThetaWittRhoExpansion.ainfMap D w s (a m)) Filter.atTop
        (𝓝 (InitialThetaWittRhoExpansion.ainfMap D w s b)) := by
  obtain ⟨b, hb⟩ := exists_coefficient_limit D w ρ a ha
  exact ⟨b, fun s => tendsto_ainfMap_of_coeff D w s a b hb⟩

theorem exists_integral_of_tendsto (ρ : Radius) (a : ℕ → InitialThetaTiltFontaine.Ainf D w)
    (x : InitialThetaWittRhoCompletion.Completed D w ρ)
    (ha : Filter.Tendsto (fun m => InitialThetaWittRhoExpansion.ainfMap D w ρ (a m)) Filter.atTop (𝓝 x)) :
    ∃ b : InitialThetaTiltFontaine.Ainf D w, InitialThetaWittRhoExpansion.ainfMap D w ρ b = x := by
  obtain ⟨b, hb⟩ := exists_integral_limit_of_cauchy D w ρ a ha.cauchySeq
  exact ⟨b, tendsto_nhds_unique (hb ρ) ha⟩

theorem ainfMap_range_isClosed (ρ : Radius) : IsClosed (Set.range (InitialThetaWittRhoExpansion.ainfMap D w ρ)) := by
  apply IsSeqClosed.isClosed
  intro x y hx hy
  choose a ha using hx
  have ht : Filter.Tendsto (fun m => InitialThetaWittRhoExpansion.ainfMap D w ρ (a m)) Filter.atTop (𝓝 y) := by
    simpa only [ha] using hy
  exact exists_integral_of_tendsto D w ρ a y ht

theorem exists_integral_of_mem_closure (ρ : Radius) (x : InitialThetaWittRhoCompletion.Completed D w ρ)
    (hx : x ∈ closure (Set.range (InitialThetaWittRhoExpansion.ainfMap D w ρ))) :
    ∃ b : InitialThetaTiltFontaine.Ainf D w, InitialThetaWittRhoExpansion.ainfMap D w ρ b = x := by
  rwa [(ainfMap_range_isClosed D w ρ).closure_eq] at hx

theorem exists_integral_of_annular_tendsto (ρ : Radius) (a : ℕ → InitialThetaTiltFontaine.Ainf D w)
    (v : InitialThetaWittAnnularExponential.Carrier D w ρ)
    (ha : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      Filter.Tendsto (fun m => InitialThetaWittRhoExpansion.ainfMap D w s.val (a m)) Filter.atTop
        (𝓝 (InitialThetaWittAnnularExponential.evaluate D w ρ s v))) :
    ∃ b : InitialThetaTiltFontaine.Ainf D w, ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      InitialThetaWittRhoExpansion.ainfMap D w s.val b = InitialThetaWittAnnularExponential.evaluate D w ρ s v := by
  obtain ⟨b, hb⟩ := exists_integral_limit_of_cauchy D w ρ a (ha ⟨ρ, le_rfl⟩).cauchySeq
  exact ⟨b, fun s => tendsto_nhds_unique (hb s.val) (ha s)⟩

theorem common_integral_range_eq_preimage (ρ : Radius) :
    Set.range (InitialThetaWittAllRadiusExpansion.ainfMap D w) =
      InitialThetaWittAllRadiusCompletion.evaluate D w ρ ⁻¹'
        Set.range (InitialThetaWittRhoExpansion.ainfMap D w ρ) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, InitialThetaWittRadiusFaithfulness.evaluate_injective D w ρ ?_⟩
    exact ha

theorem common_integral_range_isClosed (ρ : Radius) :
    IsClosed (Set.range (InitialThetaWittAllRadiusExpansion.ainfMap D w)) := by
  rw [common_integral_range_eq_preimage D w ρ]
  exact (ainfMap_range_isClosed D w ρ).preimage
    (InitialThetaWittAllRadiusCompletion.evaluate_continuous D w ρ)

theorem exists_common_integral_of_coordinate_mem (ρ : Radius)
    (x : InitialThetaWittAllRadiusCompletion.Carrier D w)
    (hx : InitialThetaWittAllRadiusCompletion.evaluate D w ρ x ∈
      Set.range (InitialThetaWittRhoExpansion.ainfMap D w ρ)) :
    ∃ a : InitialThetaTiltFontaine.Ainf D w, InitialThetaWittAllRadiusExpansion.ainfMap D w a = x := by
  change x ∈ Set.range (InitialThetaWittAllRadiusExpansion.ainfMap D w)
  rw [common_integral_range_eq_preimage D w ρ]
  exact hx

end
end JoshiTeich.Act1Scene1.InitialThetaWittIntegralImageClosed
