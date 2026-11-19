/-
Adapted from Heights/WeierstrassFiniteAnalytic.lean, blob
8833dafe13ecac147ca8abca6f830dc18bc734da at revision
3539e2a12dd3470c057a4eb531dc3fd627d4c97b of https://github.com/lana-agents/heights.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

noncomputable section

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

/-- The affine Weierstrass polynomial, viewed as a complex-valued function on
`ℂ × ℂ`. -/
def complexWeierstrassEquation (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) : ℂ :=
  p.2 ^ 2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2 -
    (p.1 ^ 3 + W.a₂ * p.1 ^ 2 + W.a₄ * p.1 + W.a₆)

/-- The partial derivative of the affine equation with respect to `x`. -/
def complexWeierstrassEquationX (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) : ℂ :=
  W.a₁ * p.2 - (3 * p.1 ^ 2 + 2 * W.a₂ * p.1 + W.a₄)

/-- The partial derivative of the affine equation with respect to `y`. -/
def complexWeierstrassEquationY (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) : ℂ :=
  2 * p.2 + W.a₁ * p.1 + W.a₃

@[simp] theorem complexWeierstrassEquation_eq_zero_iff
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    complexWeierstrassEquation W p = 0 ↔
      W.toAffine.Equation p.1 p.2 := by
  rw [WeierstrassCurve.Affine.equation_iff']
  rfl

@[simp] theorem complexWeierstrassEquationX_eq_polynomialX
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    complexWeierstrassEquationX W p =
      W.toAffine.polynomialX.evalEval p.1 p.2 := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialX]
  rfl

@[simp] theorem complexWeierstrassEquationY_eq_polynomialY
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    complexWeierstrassEquationY W p =
      W.toAffine.polynomialY.evalEval p.1 p.2 := by
  rw [WeierstrassCurve.Affine.evalEval_polynomialY]
  rfl

/-- The affine equation is an entire function on `ℂ × ℂ`. -/
theorem contDiff_complexWeierstrassEquation (W : WeierstrassCurve ℂ) :
    ContDiff ℂ ω (complexWeierstrassEquation W) := by
  unfold complexWeierstrassEquation
  fun_prop

/-- The exact complex Fréchet derivative of the affine equation. -/
theorem hasFDerivAt_complexWeierstrassEquation
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    HasFDerivAt (complexWeierstrassEquation W)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationX W p) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationY W p)) p := by
  have hx : HasFDerivAt (fun q : ℂ × ℂ => q.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) p := hasFDerivAt_fst
  have hy : HasFDerivAt (fun q : ℂ × ℂ => q.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) p := hasFDerivAt_snd
  have hyy := hy.pow 2
  have ha1xy := ((hasFDerivAt_const W.a₁ p).mul hx).mul hy
  have ha3y := (hasFDerivAt_const W.a₃ p).mul hy
  have hxxx := hx.pow 3
  have ha2xx := (hasFDerivAt_const W.a₂ p).mul (hx.pow 2)
  have ha4x := (hasFDerivAt_const W.a₄ p).mul hx
  have ha6 : HasFDerivAt (fun _ : ℂ × ℂ => W.a₆)
      (0 : (ℂ × ℂ) →L[ℂ] ℂ) p := hasFDerivAt_const W.a₆ p
  have h := ((hyy.add ha1xy).add ha3y).sub
      (((hxxx.add ha2xx).add ha4x).add ha6)
  change HasFDerivAt (complexWeierstrassEquation W) _ p at h
  have hd := h.differentiableAt.hasFDerivAt
  have hfd : fderiv ℂ (complexWeierstrassEquation W) p =
      (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationX W p) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationY W p) := by
    rw [h.fderiv]
    apply ContinuousLinearMap.ext
    rintro ⟨z, w⟩
    simp [complexWeierstrassEquationX, complexWeierstrassEquationY]
    ring
  rwa [hfd] at hd

private theorem isInvertible_smulRight_id (a : ℂ) (ha : a ≠ 0) :
    ((ContinuousLinearMap.id ℂ ℂ).smulRight a).IsInvertible := by
  let u : ℂˣ := Units.mk0 a ha
  refine ⟨(ContinuousLinearEquiv.unitsEquivAut ℂ) u, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  simp [u, mul_comm]

/-- If the `y`-derivative is nonzero, the partial Fréchet derivative in the
second factor is invertible. -/
theorem isInvertible_fderiv_inr_complexWeierstrassEquation
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    (fderiv ℂ (complexWeierstrassEquation W) p ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  rw [(hasFDerivAt_complexWeierstrassEquation W p).fderiv]
  have heq :
      (((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
            (complexWeierstrassEquationX W p) +
        (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
            (complexWeierstrassEquationY W p)) ∘L
          ContinuousLinearMap.inr ℂ ℂ ℂ) =
        (ContinuousLinearMap.id ℂ ℂ).smulRight
          (complexWeierstrassEquationY W p) := by
    apply ContinuousLinearMap.ext
    intro z
    simp
  rw [heq]
  exact isInvertible_smulRight_id _ hy

/-- The implicit holomorphic `y`-coordinate near a point where `∂F/∂y ≠ 0`. -/
def complexWeierstrassImplicitY (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) : ℂ → ℂ :=
  (contDiff_complexWeierstrassEquation W).contDiffAt.implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)

/-- Near its base point, the implicit `y`-function parametrizes the same level
set of the Weierstrass equation. -/
theorem eventually_complexWeierstrassEquation_iff_implicitY
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hy : complexWeierstrassEquationY W p ≠ 0) :
    ∀ᶠ q in 𝓝 p,
      complexWeierstrassEquation W q = complexWeierstrassEquation W p ↔
        complexWeierstrassImplicitY W p hy q.1 = q.2 :=
  (contDiff_complexWeierstrassEquation W).contDiffAt.eventually_apply_eq_iff_implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquation W p hy)


/-- The affine equation with coordinates exchanged.  Its second variable is
`x`, so the ordinary product-domain implicit theorem solves for `x`. -/
def complexWeierstrassEquationSwap (W : WeierstrassCurve ℂ)
    (p : ℂ × ℂ) : ℂ :=
  complexWeierstrassEquation W (p.2, p.1)

/-- The swapped equation is entire. -/
theorem contDiff_complexWeierstrassEquationSwap (W : WeierstrassCurve ℂ) :
    ContDiff ℂ ω (complexWeierstrassEquationSwap W) := by
  unfold complexWeierstrassEquationSwap
  exact (contDiff_complexWeierstrassEquation W).comp (by fun_prop)

/-- The exact derivative of the equation after exchanging coordinates. -/
theorem hasFDerivAt_complexWeierstrassEquationSwap
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ) :
    HasFDerivAt (complexWeierstrassEquationSwap W)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationY W (p.2, p.1)) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationX W (p.2, p.1))) p := by
  have hs : HasFDerivAt (fun q : ℂ × ℂ => (q.2, q.1))
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).prod
        (ContinuousLinearMap.fst ℂ ℂ ℂ)) p :=
    hasFDerivAt_snd.prodMk hasFDerivAt_fst
  have h := (hasFDerivAt_complexWeierstrassEquation W (p.2, p.1)).comp p hs
  change HasFDerivAt (complexWeierstrassEquationSwap W) _ p at h
  have hd := h.differentiableAt.hasFDerivAt
  have hfd : fderiv ℂ (complexWeierstrassEquationSwap W) p =
      (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationY W (p.2, p.1)) +
       (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
          (complexWeierstrassEquationX W (p.2, p.1)) := by
    rw [h.fderiv]
    apply ContinuousLinearMap.ext
    rintro ⟨z, w⟩
    simp
    ring
  rwa [hfd] at hd

/-- If the `x`-derivative is nonzero, the second-factor derivative of the
swapped equation is invertible. -/
theorem isInvertible_fderiv_inr_complexWeierstrassEquationSwap
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W (p.2, p.1) ≠ 0) :
    (fderiv ℂ (complexWeierstrassEquationSwap W) p ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  rw [(hasFDerivAt_complexWeierstrassEquationSwap W p).fderiv]
  have heq :
      (((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight
            (complexWeierstrassEquationY W (p.2, p.1)) +
        (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight
            (complexWeierstrassEquationX W (p.2, p.1))) ∘L
          ContinuousLinearMap.inr ℂ ℂ ℂ) =
        (ContinuousLinearMap.id ℂ ℂ).smulRight
          (complexWeierstrassEquationX W (p.2, p.1)) := by
    apply ContinuousLinearMap.ext
    intro z
    simp
  rw [heq]
  exact isInvertible_smulRight_id _ hx

/-- The implicit holomorphic `x`-coordinate near a point where `∂F/∂x ≠ 0`.
Its argument is the `y`-coordinate. -/
def complexWeierstrassImplicitX (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) : ℂ → ℂ :=
  (contDiff_complexWeierstrassEquationSwap W).contDiffAt.implicitFunction
    (by simp) (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W
      (p.2, p.1) hx)

/-- Near its base point, the implicit `x`-function parametrizes the same level
set of the Weierstrass equation. -/
theorem eventually_complexWeierstrassEquation_iff_implicitX
    (W : WeierstrassCurve ℂ) (p : ℂ × ℂ)
    (hx : complexWeierstrassEquationX W p ≠ 0) :
    ∀ᶠ q in 𝓝 p,
      complexWeierstrassEquation W q = complexWeierstrassEquation W p ↔
        complexWeierstrassImplicitX W p hx q.2 = q.1 := by
  have h :=
    (contDiff_complexWeierstrassEquationSwap W).contDiffAt.eventually_apply_eq_iff_implicitFunction
      (u := (p.2, p.1)) (by simp)
      (isInvertible_fderiv_inr_complexWeierstrassEquationSwap W (p.2, p.1) hx)
  have hswap : Tendsto (fun q : ℂ × ℂ => (q.2, q.1)) (𝓝 p) (𝓝 (p.2, p.1)) :=
    (continuous_snd.prodMk continuous_fst).continuousAt
  filter_upwards [h.filter_mono hswap] with q hq
  simpa [complexWeierstrassEquationSwap, complexWeierstrassImplicitX] using hq

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
