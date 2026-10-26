import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenAnnularSmallness
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialContraction

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ANNULAR-EXPONENTIAL
source: Joshi II `se:ff-rings` and the multiplicative-formal-group
period construction in `pr:teichmuller-lift-A`.
fidelity: takes the closure of the original bounded Witt diagonal over
the actual radii s>=rho. The common-ring restriction lands in this same
closure. The convergent exponential coordinates are a limit of common
partial sums in that closure, hence form one actual annular unit. Its
value and inverse have norm at most one in every coordinate. Every full
phi=p element gives such a unit after a proved actual p-power scaling.
On overlapping powered radii the same unit satisfies the actual
Frobenius power equation, derived from convergence and the eigen law.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the annular carrier is explicitly distinct
from the full all-radius ring. No Teichmuller representative, integral
Witt identity or full period representation is assumed. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAnnularExponential

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittExponentialSeries InitialThetaWittExponentialMultiplication
open InitialThetaWittExponentialCoefficients InitialThetaWittEigenRadiusDynamics
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev AnnularRadius (ρ : Radius) := {s : Radius // ρ.val ≤ s.val}
abbrev Product (ρ : Radius) := ∀ s : AnnularRadius ρ, InitialThetaWittRhoCompletion.Completed D w s.val

def diagonal (ρ : Radius) : InitialThetaBoundedWittLocalization.Ring D w →+* Product D w ρ :=
  RingHom.pi (fun s => InitialThetaWittRhoCompletion.inclusion D w s.val)

def closedSubring (ρ : Radius) : Subring (Product D w ρ) := (diagonal D w ρ).range.topologicalClosure

abbrev Carrier (ρ : Radius) := ↥(closedSubring D w ρ)

instance carrierComplete (ρ : Radius) : CompleteSpace (Carrier D w ρ) :=
  (Subring.isClosed_topologicalClosure (diagonal D w ρ).range).isComplete.completeSpace_coe

def restrictionHom (ρ : Radius) : InitialThetaWittAllRadiusCompletion.Carrier D w →+* Product D w ρ :=
  RingHom.pi (fun s => InitialThetaWittAllRadiusCompletion.evaluate D w s.val)

theorem restrictionHom_continuous (ρ : Radius) : Continuous (restrictionHom D w ρ) :=
  continuous_pi (fun s => InitialThetaWittAllRadiusCompletion.evaluate_continuous D w s.val)

theorem restrictionHom_mem (ρ : Radius) (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    restrictionHom D w ρ x ∈ closedSubring D w ρ := by
  refine (InitialThetaWittAllRadiusCompletion.inclusion_denseRange D w).induction_on
    (p := fun y => restrictionHom D w ρ y ∈ closedSubring D w ρ) x ?_ ?_
  · exact (Subring.isClosed_topologicalClosure (diagonal D w ρ).range).preimage
      (restrictionHom_continuous D w ρ)
  · intro y
    exact Subring.le_topologicalClosure _ ⟨y, rfl⟩

def restriction (ρ : Radius) : InitialThetaWittAllRadiusCompletion.Carrier D w →+* Carrier D w ρ :=
  (restrictionHom D w ρ).codRestrict (closedSubring D w ρ) (restrictionHom_mem D w ρ)

def evaluate (ρ : Radius) (s : AnnularRadius ρ) : Carrier D w ρ →+*
    InitialThetaWittRhoCompletion.Completed D w s.val :=
  (Pi.evalRingHom (fun r : AnnularRadius ρ => InitialThetaWittRhoCompletion.Completed D w r.val) s).comp
    (closedSubring D w ρ).subtype

theorem evaluate_restriction (ρ : Radius) (s : AnnularRadius ρ)
    (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    evaluate D w ρ s (restriction D w ρ x) = InitialThetaWittAllRadiusCompletion.evaluate D w s.val x := rfl

theorem ext (ρ : Radius) {x y : Carrier D w ρ}
    (h : ∀ s : AnnularRadius ρ, evaluate D w ρ s x = evaluate D w ρ s y) : x = y :=
  Subtype.ext (funext h)

theorem hasSum_exp_product (ρ : Radius) (z : InitialThetaWittAllRadiusCompletion.Carrier D w)
    (hz : ∀ s : AnnularRadius ρ, ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z‖ < s.val.val.toReal) :
    HasSum (fun n : ℕ => restrictionHom D w ρ (commonPadicMap D w (coefficient D w n) * z ^ n))
      (fun s : AnnularRadius ρ => exp D w s.val (InitialThetaWittAllRadiusCompletion.evaluate D w s.val z)) := by
  apply Pi.hasSum.mpr
  intro s
  change HasSum (fun n : ℕ => InitialThetaWittAllRadiusCompletion.evaluate D w s.val
    (commonPadicMap D w (coefficient D w n) * z ^ n)) _
  simp only [map_mul, map_pow, evaluate_padic]
  exact hasSum_exp D w s.val _ (hz s)

theorem exp_product_mem (ρ : Radius) (z : InitialThetaWittAllRadiusCompletion.Carrier D w)
    (hz : ∀ s : AnnularRadius ρ, ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z‖ < s.val.val.toReal) :
    (fun s : AnnularRadius ρ => exp D w s.val (InitialThetaWittAllRadiusCompletion.evaluate D w s.val z)) ∈
      closedSubring D w ρ := by
  apply (Subring.isClosed_topologicalClosure (diagonal D w ρ).range).mem_of_tendsto
    (hasSum_exp_product D w ρ z hz)
  exact Filter.Eventually.of_forall (fun t : Finset ℕ =>
    (closedSubring D w ρ).sum_mem (fun n _ => restrictionHom_mem D w ρ _))

def annularExp (ρ : Radius) (z : InitialThetaWittAllRadiusCompletion.Carrier D w)
    (hz : ∀ s : AnnularRadius ρ, ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z‖ < s.val.val.toReal) :
    Carrier D w ρ := ⟨_, exp_product_mem D w ρ z hz⟩

theorem evaluate_annularExp (ρ : Radius) (z : InitialThetaWittAllRadiusCompletion.Carrier D w)
    (hz : ∀ s : AnnularRadius ρ, ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z‖ < s.val.val.toReal)
    (s : AnnularRadius ρ) : evaluate D w ρ s (annularExp D w ρ z hz) =
      exp D w s.val (InitialThetaWittAllRadiusCompletion.evaluate D w s.val z) := rfl

theorem neg_inDomain (ρ : Radius) (z : InitialThetaWittAllRadiusCompletion.Carrier D w)
    (hz : ∀ s : AnnularRadius ρ, ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z‖ < s.val.val.toReal) :
    ∀ s : AnnularRadius ρ, ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val (-z)‖ < s.val.val.toReal := by
  intro s
  simpa only [map_neg, norm_neg] using hz s

theorem annularExp_mul_neg (ρ : Radius) (z : InitialThetaWittAllRadiusCompletion.Carrier D w)
    (hz : ∀ s : AnnularRadius ρ, ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z‖ < s.val.val.toReal) :
    annularExp D w ρ z hz * annularExp D w ρ (-z) (neg_inDomain D w ρ z hz) = 1 := by
  apply ext D w ρ
  intro s
  rw [map_mul, map_one, evaluate_annularExp, evaluate_annularExp, map_neg]
  exact exp_mul_exp_neg D w s.val _ (hz s)

def annularExpUnit (ρ : Radius) (z : InitialThetaWittAllRadiusCompletion.Carrier D w)
    (hz : ∀ s : AnnularRadius ρ, ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z‖ < s.val.val.toReal) :
    (Carrier D w ρ)ˣ where
  val := annularExp D w ρ z hz
  inv := annularExp D w ρ (-z) (neg_inDomain D w ρ z hz)
  val_inv := annularExp_mul_neg D w ρ z hz
  inv_val := (mul_comm _ _).trans (annularExp_mul_neg D w ρ z hz)

theorem norm_evaluate_annularExp_le_one (ρ : Radius) (z : InitialThetaWittAllRadiusCompletion.Carrier D w)
    (hz : ∀ s : AnnularRadius ρ, ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z‖ < s.val.val.toReal)
    (s : AnnularRadius ρ) : ‖evaluate D w ρ s (annularExp D w ρ z hz)‖ ≤ 1 :=
  InitialThetaWittExponentialContraction.norm_exp_le_one D w s.val _ (hz s)

theorem eigen_annular_frobenius (ρ : Radius) (z : Eigen D w)
    (hz : ∀ s : AnnularRadius ρ, ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z.val‖ < s.val.val.toReal)
    (s : AnnularRadius ρ)
    (hs : ρ.val ≤ (InitialThetaWittRhoFrobeniusCompletion.poweredRadius D w s.val).val) :
    InitialThetaWittRhoFrobeniusEquiv.completedEquiv D w s.val
        (evaluate D w ρ s (annularExp D w ρ z.val hz)) =
      evaluate D w ρ ⟨InitialThetaWittRhoFrobeniusCompletion.poweredRadius D w s.val, hs⟩
        (annularExp D w ρ z.val hz) ^ Arithmetic.residueChar w.1 := by
  rw [evaluate_annularExp, evaluate_annularExp,
    InitialThetaWittExponentialFrobenius.frobenius_exp D w s.val _ (hz s),
    InitialThetaWittExponentialFrobenius.eigen_frobenius_coordinate,
    exp_nsmul D w _ _ (hz ⟨InitialThetaWittRhoFrobeniusCompletion.poweredRadius D w s.val, hs⟩)]

theorem exists_eigen_annular_unit (ρ : Radius) (z : Eigen D w) : ∃ k : ℕ, ∃ v : (Carrier D w ρ)ˣ,
    ∀ s : AnnularRadius ρ,
      evaluate D w ρ s v.val = exp D w s.val (InitialThetaWittAllRadiusCompletion.evaluate D w s.val
        (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val) ∧
      ‖evaluate D w ρ s v.val‖ ≤ 1 ∧ ‖evaluate D w ρ s (v⁻¹).val‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := InitialThetaWittEigenAnnularSmallness.exists_prime_pow_smul_annular D w ρ z
  let x := (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val
  have hx : ∀ s : AnnularRadius ρ, ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val x‖ < s.val.val.toReal :=
    fun s => hk s.val s.property
  refine ⟨k, annularExpUnit D w ρ x hx, fun s => ?_⟩
  exact ⟨rfl, norm_evaluate_annularExp_le_one D w ρ x hx s,
    norm_evaluate_annularExp_le_one D w ρ (-x) (neg_inDomain D w ρ x hx) s⟩

end
end JoshiTeich.Act1Scene1.InitialThetaWittAnnularExponential
