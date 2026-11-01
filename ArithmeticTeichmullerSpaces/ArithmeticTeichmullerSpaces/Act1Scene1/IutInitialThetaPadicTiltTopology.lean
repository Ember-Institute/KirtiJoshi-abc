import ArithmeticTeichmullerSpaces.Act1Scene1.PadicTiltField
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicTiltComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTiltIntegers
import Mathlib.Topology.UniformSpace.Equiv

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-TILT-TOPOLOGY
source: Joshi II `se:ff-rings`, with fixed F=C_p^flat, and the proved
actual tilt valuation comparison with the standard C_p tilt.
fidelity: compares the original normed tilt to the independently constructed
standard C_p tilt. The local-degree norm law gives both uniform continuity
directions, a uniform equivalence, a homeomorphism and an equivalence of
the original tilt integer rings. No comparison or topology law is input.
boundary: Scene1/Derived; the original norm and its degree power are retained.
Witt/rho completion and paper B identities remain open. Original proofs;
no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicTiltTopology

open JoshiTeich.Prologue
open scoped NNReal Topology
noncomputable section

private def ring_inverse {A B : Type*}
    {mulA : Mul A} {mulB : Mul B} {addA : Add A} {addB : Add B}
    (e : @RingEquiv A B mulA mulB addA addB) : B → A :=
  e.toEquiv.invFun

private theorem ring_inverse_left {A B : Type*}
    {mulA : Mul A} {mulB : Mul B} {addA : Add A} {addB : Add B}
    (e : @RingEquiv A B mulA mulB addA addB) (x : A) :
    ring_inverse e (e.toEquiv.toFun x) = x :=
  e.toEquiv.left_inv x

private theorem ring_inverse_right {A B : Type*}
    {mulA : Mul A} {mulB : Mul B} {addA : Add A} {addB : Add B}
    (e : @RingEquiv A B mulA mulB addA addB) (y : B) :
    e.toEquiv.toFun (ring_inverse e y) = y :=
  e.toEquiv.right_inv y

private theorem norm_pow_bridge {A B : Type*} [Norm A] [Norm B]
    (f : A → B) (vA : A → ℝ≥0) (vB : B → ℝ≥0)
    (hA : ∀ x, ‖x‖ = (vA x : ℝ)) (hB : ∀ y, ‖y‖ = (vB y : ℝ))
    (d : ℕ) (hv : ∀ x, vB (f x) ^ d = vA x) (x : A) :
    ‖f x‖ ^ d = ‖x‖ := by
  rw [hB, hA]
  exact_mod_cast hv x

private theorem inverse_dist_bridge {A B : Type*} [Dist A] [Dist B]
    (f : A → B) (g : B → A) (hfg : ∀ y, f (g y) = y) (d : ℕ)
    (h : ∀ x y, dist (f x) (f y) ^ d = dist x y) (x y : B) :
    dist (g x) (g y) = dist x y ^ d := by
  simpa only [hfg] using (h (g x) (g y)).symm

private theorem forward_uniform_bridge {A B : Type*} [PseudoMetricSpace A] [PseudoMetricSpace B]
    (f : A → B) (d : ℕ) (h : ∀ x y, dist (f x) (f y) ^ d = dist x y) :
    UniformContinuous f := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  refine ⟨ε ^ d, pow_pos hε _, ?_⟩
  intro x y hxy
  exact lt_of_pow_lt_pow_left₀ _ hε.le (by rwa [h])

private theorem inverse_uniform_bridge {A B : Type*} [PseudoMetricSpace A] [PseudoMetricSpace B]
    (g : B → A) (d : ℕ) (hd : d ≠ 0)
    (h : ∀ x y, dist (g x) (g y) = dist x y ^ d) : UniformContinuous g := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro x y hxy
  rw [h]
  exact (pow_le_of_le_one dist_nonneg (lt_of_lt_of_le hxy (min_le_right _ _)).le hd).trans_lt
    (lt_of_lt_of_le hxy (min_le_left _ _))

private def uniformEquiv_bridge {A B : Type*} [UniformSpace A] [UniformSpace B]
    (f : A → B) (g : B → A) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    (hf : UniformContinuous f) (hg : UniformContinuous g) : A ≃ᵤ B where
  toEquiv := ⟨f, g, hgf, hfg⟩
  uniformContinuous_toFun := hf
  uniformContinuous_invFun := hg

universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Standard := PadicTiltField.Carrier (Arithmetic.residueChar w.1)

local instance actualRawField : Field (InitialThetaTiltField.Carrier D w) :=
  InitialThetaTiltField.carrierField D w
local instance standardRawField : Field (Standard D w) :=
  FractionRing.field (PadicTiltField.Source (Arithmetic.residueChar w.1))

local instance actualNormedField : NormedField (InitialThetaTiltField.Carrier D w) :=
  InitialThetaTiltTopology.carrierNormedField D w
local instance standardNormedField : NormedField (Standard D w) :=
  PadicTiltField.carrierNormedField (Arithmetic.residueChar w.1)

local instance actualUniformSpace : UniformSpace (InitialThetaTiltField.Carrier D w) :=
  (inferInstance : PseudoMetricSpace (InitialThetaTiltField.Carrier D w)).toUniformSpace
local instance standardUniformSpace : UniformSpace (Standard D w) :=
  PadicTiltField.carrierUniformSpace (Arithmetic.residueChar w.1)

local instance actualTopologicalSpace : TopologicalSpace (InitialThetaTiltField.Carrier D w) :=
  (actualUniformSpace D w).toTopologicalSpace
local instance standardTopologicalSpace : TopologicalSpace (Standard D w) :=
  PadicTiltField.carrierTopologicalSpace (Arithmetic.residueChar w.1)

abbrev ringEquiv :=
  InitialThetaPadicTiltComparison.tiltEquiv D w

def inverse := (ringEquiv D w).toEquiv.invFun

theorem inverse_ringEquiv (x : InitialThetaTiltField.Carrier D w) :
    inverse D w (ringEquiv D w x) = x := ring_inverse_left (ringEquiv D w) x

theorem ringEquiv_inverse (y) :
    ringEquiv D w (inverse D w y) = y := ring_inverse_right (ringEquiv D w) y

theorem norm_pow (x : InitialThetaTiltField.Carrier D w) :
    ‖ringEquiv D w x‖ ^ Arithmetic.localDeg w.1 = ‖x‖ :=
  norm_pow_bridge (ringEquiv D w) (InitialThetaTiltField.valuation D w)
    (GeometricTiltField.fractionValuation (PadicComplex (Arithmetic.residueChar w.1))
      (Arithmetic.residueChar w.1))
    (InitialThetaTiltTopology.norm_eq_valuation D w)
    (PadicTiltField.norm_eq_valuation (Arithmetic.residueChar w.1))
    (Arithmetic.localDeg w.1)
    (InitialThetaPadicTiltComparison.tiltEquiv_valuation_pow D w) x

theorem dist_pow (x y : InitialThetaTiltField.Carrier D w) :
    dist (ringEquiv D w x) (ringEquiv D w y) ^ Arithmetic.localDeg w.1 = dist x y := by
  rw [dist_eq_norm, ← map_sub, norm_pow, dist_eq_norm]

theorem inverse_dist (x y : Standard D w) :
    dist (inverse D w x) (inverse D w y) =
      dist x y ^ Arithmetic.localDeg w.1 :=
  inverse_dist_bridge (ringEquiv D w) (inverse D w)
    (ringEquiv_inverse D w) (Arithmetic.localDeg w.1) (dist_pow D w) x y

theorem ringEquiv_uniformContinuous : UniformContinuous (ringEquiv D w) :=
  forward_uniform_bridge (ringEquiv D w) (Arithmetic.localDeg w.1) (dist_pow D w)

theorem inverse_uniformContinuous : UniformContinuous (inverse D w) :=
  inverse_uniform_bridge (inverse D w) (Arithmetic.localDeg w.1)
    (Arithmetic.localDeg_pos w.1).ne' (inverse_dist D w)

def uniformEquiv :=
  uniformEquiv_bridge (ringEquiv D w) (inverse D w)
    (inverse_ringEquiv D w) (ringEquiv_inverse D w)
    (ringEquiv_uniformContinuous D w) (inverse_uniformContinuous D w)

def homeomorph :=
  (uniformEquiv D w).toHomeomorph

theorem uniformEquiv_apply (x : InitialThetaTiltField.Carrier D w) :
    uniformEquiv D w x = ringEquiv D w x := rfl

def integerEquiv : InitialThetaTiltIntegers.Integers D w ≃+*
    LocalGeometricFontaine.integerRing (InitialThetaPadicTiltComparison.StandardTilt D w) :=
  GeometricTiltComparison.integerEquiv (ringEquiv D w)
    (Arithmetic.localDeg w.1) (Arithmetic.localDeg_pos w.1) (norm_pow D w)

theorem integerEquiv_apply (x : InitialThetaTiltIntegers.Integers D w) :
    (integerEquiv D w x : InitialThetaPadicTiltComparison.StandardTilt D w) =
      ringEquiv D w x :=
  GeometricTiltComparison.integerEquiv_apply (ringEquiv D w)
    (Arithmetic.localDeg w.1) (Arithmetic.localDeg_pos w.1) (norm_pow D w) x

theorem integerEquiv_norm_pow (x : InitialThetaTiltIntegers.Integers D w) :
    ‖integerEquiv D w x‖ ^ Arithmetic.localDeg w.1 = ‖x‖ := by
  change ‖(integerEquiv D w x : InitialThetaPadicTiltComparison.StandardTilt D w)‖ ^
      Arithmetic.localDeg w.1 =
    ‖(x : InitialThetaTiltField.Carrier D w)‖
  rw [integerEquiv_apply]
  exact norm_pow D w x

end
end JoshiTeich.Act1Scene1.InitialThetaPadicTiltTopology
