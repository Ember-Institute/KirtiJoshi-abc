import ArithmeticTeichmullerSpaces.Act1Scene1.CyclotomicTateTilt
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTiltFontaine
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerPrimitiveTower

/-!
source-id: JT-SCENE1-INITIAL-THETA-CYCLOTOMIC-TATE-TILT
source: Joshi II eq:tate-module-of-lubin-tate (935--938) and
pr:teichmuller-lift-A (940--958), with the multiplicative formal group.
fidelity: embeds the actual cyclotomic root tower in the same tilt integers
and Ainf. The element [epsilon]-1 lies in the original Fontaine kernel,
is zero exactly for the trivial tower, and satisfies the multiplicative
formal-group law. It is a precursor to the logarithmic Tate period, not
an identification with the additive Tate submodule of B^{phi=p}.
Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaCyclotomicTateTilt

open JoshiTeich.Prologue InitialThetaCanonicalGeometricFontaine
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ < 1) :=
  primeNormFact D w

abbrev Tate := LocalKummer.cyclotomicTateGroup (Arithmetic.residueChar w.1) (coefficientField D w)

/-- The original compatible roots determine an element of the actual tilt integers. -/
def epsilon : Tate D w →* InitialThetaTiltIntegers.Integers D w :=
  (InitialThetaTiltIntegers.preTiltEquiv D w).toMonoidHom.comp
    (CyclotomicTateTilt.toPreTilt (coefficientField D w) (Arithmetic.residueChar w.1))

theorem epsilon_injective : Function.Injective (epsilon D w) :=
  (InitialThetaTiltIntegers.preTiltEquiv D w).injective.comp
    (CyclotomicTateTilt.toPreTilt_injective (coefficientField D w) (Arithmetic.residueChar w.1))

theorem sharp_epsilon (x : Tate D w) : InitialThetaTiltIntegers.sharp D w (epsilon D w x) = 1 := by
  change InitialThetaTiltIntegers.sharp D w (InitialThetaTiltIntegers.preTiltEquiv D w
    (CyclotomicTateTilt.toPreTilt (coefficientField D w) (Arithmetic.residueChar w.1) x)) = 1
  rw [InitialThetaTiltIntegers.sharp_preTiltEquiv]
  exact CyclotomicTateTilt.untilt_toPreTilt (coefficientField D w) (Arithmetic.residueChar w.1) x

def teichmuller : Tate D w →* InitialThetaTiltFontaine.Ainf D w :=
  (WittVector.teichmuller (Arithmetic.residueChar w.1)).comp (epsilon D w)

theorem theta_teichmuller (x : Tate D w) :
    InitialThetaTiltFontaine.theta D w (teichmuller D w x) = 1 := by
  change InitialThetaTiltFontaine.theta D w
    (WittVector.teichmuller (Arithmetic.residueChar w.1) (epsilon D w x)) = 1
  rw [InitialThetaTiltFontaine.theta_teichmuller, sharp_epsilon]

theorem teichmuller_injective : Function.Injective (teichmuller D w) := by
  intro x y h
  apply epsilon_injective D w
  have hc := congrArg (fun a : InitialThetaTiltFontaine.Ainf D w => a.coeff 0) h
  simpa only [teichmuller, MonoidHom.comp_apply, WittVector.teichmuller_coeff_zero] using hc

/-- Multiplicative-formal-group coordinate, before applying a period logarithm. -/
def kernelCoordinate (x : Tate D w) : InitialThetaTiltFontaine.Ainf D w :=
  teichmuller D w x - 1

theorem kernelCoordinate_mem_ker (x : Tate D w) :
    kernelCoordinate D w x ∈ RingHom.ker (InitialThetaTiltFontaine.theta D w) := by
  change InitialThetaTiltFontaine.theta D w (teichmuller D w x - 1) = 0
  rw [map_sub, theta_teichmuller, map_one, sub_self]

theorem kernelCoordinate_one : kernelCoordinate D w 1 = 0 := by
  rw [kernelCoordinate, map_one, sub_self]

theorem kernelCoordinate_injective : Function.Injective (kernelCoordinate D w) := by
  intro x y h
  apply teichmuller_injective D w
  have he := congrArg (fun a : InitialThetaTiltFontaine.Ainf D w => a + 1) h
  simpa only [kernelCoordinate, sub_add_cancel] using he

theorem kernelCoordinate_eq_zero_iff (x : Tate D w) :
    kernelCoordinate D w x = 0 ↔ x = 1 := by
  rw [← kernelCoordinate_one D w]
  exact (kernelCoordinate_injective D w).eq_iff

theorem kernelCoordinate_mul (x y : Tate D w) :
    kernelCoordinate D w (x * y) = kernelCoordinate D w x + kernelCoordinate D w y +
      kernelCoordinate D w x * kernelCoordinate D w y := by
  simp only [kernelCoordinate, map_mul]
  ring

theorem theta_kernelCoordinate_add (x : Tate D w) (a : InitialThetaTiltFontaine.Ainf D w) :
    InitialThetaTiltFontaine.theta D w (kernelCoordinate D w x + a) =
      InitialThetaTiltFontaine.theta D w a := by
  rw [map_add, show InitialThetaTiltFontaine.theta D w (kernelCoordinate D w x) = 0 from
    kernelCoordinate_mem_ker D w x, zero_add]

/-- The existing primitive compatible root tower, in this same actual untilt. -/
def generator : Tate D w :=
  LocalKummer.TateBasis.generator (p := Arithmetic.residueChar w.1) (Ω := coefficientField D w)

theorem generator_ne_one : generator D w ≠ 1 := by
  intro h
  have hc := congrArg (fun x : Tate D w => x.1 1) h
  change (LocalKummer.TateBasis.generator
    (p := Arithmetic.residueChar w.1) (Ω := coefficientField D w)).1 1 = 1 at hc
  exact (LocalKummer.TateBasis.generator_isPrimitive 1).ne_one
    (by simpa only [pow_one] using (Arithmetic.residueChar_prime w.1).one_lt) hc

def canonicalKernelCoordinate : InitialThetaTiltFontaine.Ainf D w :=
  kernelCoordinate D w (generator D w)

theorem canonicalKernelCoordinate_ne_zero : canonicalKernelCoordinate D w ≠ 0 := by
  exact fun h => generator_ne_one D w ((kernelCoordinate_eq_zero_iff D w _).mp h)

theorem canonicalKernelCoordinate_mem_ker :
    canonicalKernelCoordinate D w ∈ RingHom.ker (InitialThetaTiltFontaine.theta D w) :=
  kernelCoordinate_mem_ker D w (generator D w)

end
end JoshiTeich.Act1Scene1.InitialThetaCyclotomicTateTilt
