import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenKernelTwistedComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRationalTatePeriod

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TWISTED-TATE-PERIOD
source: Joshi II `eq:tate-module-of-lubin-tate` and the exact sequence
in the proof of `pr:teichmuller-lift-A` (935--958).
fidelity: divides the actual rational Tate periods by the nonzero
normalized primitive orbit product using the proved full-kernel
continuous equivalence. This constructs a continuous closed embedding
into the original twisted solution space, with a nonzero canonical
solution t/P and one-dimensional image. The twisted equation simplifies
to phi(y)=-xi*y. Full Tate-kernel equality is proved equivalent to
surjectivity and to unique scalar representation by this actual solution.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the full kernel and twisted space retain
all their elements and their original topology. No classification or
surjectivity law is input or asserted unconditionally. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTwistedTatePeriod

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittNormalizedOrbitProduct InitialThetaWittThetaPrincipalKernel
open InitialThetaWittEigenKernelTwistedComparison
open InitialThetaWittRationalTatePeriod InitialThetaWittRationalTateSource
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem prime_mul_factor_zero :
    (Arithmetic.residueChar w.1 : Carrier D w) * factor D w 0 = -primitive D w := by
  rw [factor, InitialThetaWittFrobeniusThetaOrbit.primitiveOrbit_zero]
  calc
    _ = ((scaleUnit D w : Carrier D w) * Arithmetic.residueChar w.1) * primitive D w := by ring
    _ = _ := by rw [scaleUnit_mul_prime]; ring

theorem mem_twisted_iff (y : Carrier D w) : y ∈ twistedSubmodule D w ↔
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w y = -primitive D w * y := by
  rw [mem_twistedSubmodule, prime_mul_factor_zero]

theorem periodMap_mem_fullKernel (v : RationalTate D w) :
    periodMap D w v ∈ fullKernel D w :=
  ⟨periodMap_range_le_frobeniusPrime D w ⟨v, rfl⟩,
    periodMap_range_le_kernel D w ⟨v, rfl⟩⟩

def kernelPeriodMap : RationalTate D w →L[Padic (Arithmetic.residueChar w.1)] fullKernel D w :=
  (periodMap D w).codRestrict (fullKernel D w) (periodMap_mem_fullKernel D w)

def twistedPeriodMap : RationalTate D w →L[Padic (Arithmetic.residueChar w.1)] twistedSubmodule D w :=
  (productContinuousLinearEquiv D w).symm.toContinuousLinearMap.comp (kernelPeriodMap D w)

theorem product_mul_twistedPeriodMap (v : RationalTate D w) :
    product D w * (twistedPeriodMap D w v).val = periodMap D w v :=
  congrArg Subtype.val ((productContinuousLinearEquiv D w).apply_symm_apply (kernelPeriodMap D w v))

theorem twistedPeriodMap_injective : Function.Injective (twistedPeriodMap D w) := by
  intro v v' h
  apply periodMap_injective D w
  have he := congrArg (fun y : twistedSubmodule D w => product D w * y.val) h
  simpa only [product_mul_twistedPeriodMap] using he

theorem twistedPeriodMap_isClosedEmbedding : Topology.IsClosedEmbedding (twistedPeriodMap D w) :=
  LinearMap.isClosedEmbedding_of_injective (f := (twistedPeriodMap D w).toLinearMap)
    (LinearMap.ker_eq_bot.mpr (twistedPeriodMap_injective D w))

theorem twistedPeriodMap_range_finrank :
    Module.finrank (Padic (Arithmetic.residueChar w.1)) (twistedPeriodMap D w).range = 1 :=
  (LinearMap.finrank_range_of_inj (f := (twistedPeriodMap D w).toLinearMap)
    (twistedPeriodMap_injective D w)).trans (rationalTate_finrank D w)

def sourceGenerator : RationalTate D w := (coefficientEquiv D w).symm 1

def canonicalSolution : twistedSubmodule D w := twistedPeriodMap D w (sourceGenerator D w)

theorem product_mul_canonicalSolution :
    product D w * (canonicalSolution D w).val =
      InitialThetaWittTateLogarithm.tateLog D w (InitialThetaCyclotomicTateTilt.generator D w) := by
  rw [canonicalSolution, product_mul_twistedPeriodMap, periodMap_apply, sourceGenerator,
    LinearEquiv.apply_symm_apply, one_smul]

theorem canonicalSolution_ne_zero : canonicalSolution D w ≠ 0 := by
  intro hzero
  have h := product_mul_canonicalSolution D w
  rw [hzero, Submodule.coe_zero, mul_zero] at h
  exact InitialThetaWittTateLogarithmInjective.canonical_tateLog_ne_zero D w h.symm

theorem canonicalSolution_equation :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (canonicalSolution D w).val =
      -primitive D w * (canonicalSolution D w).val :=
  (mem_twisted_iff D w _).mp (canonicalSolution D w).property

theorem twistedPeriodMap_apply (v : RationalTate D w) :
    twistedPeriodMap D w v = coefficientEquiv D w v • canonicalSolution D w := by
  have hv : v = coefficientEquiv D w v • sourceGenerator D w := by
    apply (coefficientEquiv D w).injective
    simp only [sourceGenerator, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  calc
    twistedPeriodMap D w v = twistedPeriodMap D w (coefficientEquiv D w v • sourceGenerator D w) :=
      congrArg (twistedPeriodMap D w) hv
    _ = _ := (twistedPeriodMap D w).map_smul _ _

theorem twistedPeriodMap_range_eq_span : (twistedPeriodMap D w).range =
    Submodule.span (Padic (Arithmetic.residueChar w.1)) {canonicalSolution D w} := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    change twistedPeriodMap D w v ∈ _
    rw [twistedPeriodMap_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro hy
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨(coefficientEquiv D w).symm a, ?_⟩
    change twistedPeriodMap D w ((coefficientEquiv D w).symm a) = y
    rw [twistedPeriodMap_apply, LinearEquiv.apply_symm_apply]
    exact ha

theorem product_mul_mem_periodRange_iff (y : twistedSubmodule D w) :
    product D w * y.val ∈ (periodMap D w).range ↔ y ∈ (twistedPeriodMap D w).range := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    apply (multiplyProduct_injective D w)
    apply Subtype.ext
    change product D w * (twistedPeriodMap D w v).val = product D w * y.val
    rw [product_mul_twistedPeriodMap]
    exact hv
  · rintro ⟨v, rfl⟩
    change product D w * (twistedPeriodMap D w v).val ∈ (periodMap D w).range
    rw [product_mul_twistedPeriodMap]
    exact ⟨v, rfl⟩

theorem fullKernel_eq_periodRange_iff_surjective :
    fullKernel D w = (periodMap D w).range ↔ Function.Surjective (twistedPeriodMap D w) := by
  constructor
  · intro hfull y
    have hy : product D w * y.val ∈ (periodMap D w).range := by
      rw [← hfull]
      exact (mem_fullKernel_product_iff D w y.val).mpr y.property
    exact (product_mul_mem_periodRange_iff D w y).mp hy
  · intro hsurj
    ext x
    constructor
    · intro hx
      let y := (productContinuousLinearEquiv D w).symm ⟨x, hx⟩
      have hy : product D w * y.val = x :=
        congrArg Subtype.val ((productContinuousLinearEquiv D w).apply_symm_apply ⟨x, hx⟩)
      rw [← hy]
      exact (product_mul_mem_periodRange_iff D w y).mpr (hsurj y)
    · rintro ⟨v, rfl⟩
      exact periodMap_mem_fullKernel D w v

theorem unique_scalar_representation_iff_surjective :
    (∀ y : twistedSubmodule D w, ∃! a : Padic (Arithmetic.residueChar w.1),
      a • canonicalSolution D w = y) ↔ Function.Surjective (twistedPeriodMap D w) := by
  constructor
  · intro h y
    obtain ⟨a, ha, _⟩ := h y
    refine ⟨(coefficientEquiv D w).symm a, ?_⟩
    rw [twistedPeriodMap_apply, LinearEquiv.apply_symm_apply]
    exact ha
  · intro h y
    obtain ⟨v, hv⟩ := h y
    have ha : coefficientEquiv D w v • canonicalSolution D w = y := by
      rw [← twistedPeriodMap_apply]
      exact hv
    refine ⟨coefficientEquiv D w v, ha, ?_⟩
    intro b hb
    apply (coefficientEquiv D w).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    apply twistedPeriodMap_injective D w
    rw [twistedPeriodMap_apply, LinearEquiv.apply_symm_apply]
    exact hb.trans hv.symm

theorem fullKernel_eq_periodRange_iff_unique_scalar :
    fullKernel D w = (periodMap D w).range ↔
      ∀ y : twistedSubmodule D w, ∃! a : Padic (Arithmetic.residueChar w.1),
        a • canonicalSolution D w = y :=
  (fullKernel_eq_periodRange_iff_surjective D w).trans
    (unique_scalar_representation_iff_surjective D w).symm

end
end JoshiTeich.Act1Scene1.InitialThetaWittTwistedTatePeriod
