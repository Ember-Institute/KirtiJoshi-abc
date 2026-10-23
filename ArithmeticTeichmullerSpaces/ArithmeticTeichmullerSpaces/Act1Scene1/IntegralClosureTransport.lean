/-
original-path: `refer/iut/.lake/packages/pi1/Pi1/Orbicurve/Iso.lean`
original-author: Christian Merten <lana@merten.dev> (Git author; no author header)
original-coauthor: Claude Opus 5.5 (1M context) <noreply@anthropic.com> (Git trailer)
original-commit: `e0266a572e2ef7c144227c2703c450e466984528`
source-snapshot: `ca7def953193f861a462aa0831eec8f0a31ff69f` (pi1 package)
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the package Apache-2.0 LICENSE before copying.
The source has no copyright header and the package has no NOTICE file.
modifications: extract only compatible integral-closure transport. Use the
local namespace and precise Mathlib imports, without the orbicurve interface.
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Pi1/Orbicurve/Iso.lean, integralClosureEquiv.
fidelity: compatible ring equivalences induce an equivalence of their actual
integral closures. The induced map preserves the ambient values.
boundary: Scene1/Derived. The arithmetic consumer supplies both equivalences
and their scalar compatibility; no geometric law is an input.
-/

namespace JoshiTeich.Act1Scene1.IntegralClosureTransport

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [Algebra R S] [Algebra R' S'] (α : R ≃+* R') (β : S ≃+* S')
  (h : ∀ r, β (algebraMap R S r) = algebraMap R' S' (α r))

include h in
theorem isIntegral_map {x : S} (hx : IsIntegral R x) : IsIntegral R' (β x) := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map α.toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (algebraMap R' S').comp α.toRingHom = β.toRingHom.comp (algebraMap R S) :=
    RingHom.ext fun r => (h r).symm
  rw [hc]
  have heval := Polynomial.hom_eval₂ p (algebraMap R S) β.toRingHom x
  rw [hpx, map_zero] at heval
  exact heval.symm

include h in
theorem isIntegral_map_iff {x : S} : IsIntegral R' (β x) ↔ IsIntegral R x := by
  refine ⟨fun hx => ?_, isIntegral_map α β h⟩
  have hinv : ∀ r', β.symm (algebraMap R' S' r') = algebraMap R S (α.symm r') := by
    intro r'
    apply β.injective
    rw [RingEquiv.apply_symm_apply, h, RingEquiv.apply_symm_apply]
  have hx' := isIntegral_map α.symm β.symm hinv hx
  rwa [RingEquiv.symm_apply_apply] at hx'

def equiv : integralClosure R S ≃+* integralClosure R' S' where
  toFun x := ⟨β x, isIntegral_map α β h x.2⟩
  invFun y := ⟨β.symm y, by
    have hy : IsIntegral R' (β (β.symm y)) := by
      rw [RingEquiv.apply_symm_apply]
      exact y.2
    exact (isIntegral_map_iff α β h).mp hy⟩
  left_inv x := Subtype.ext (β.symm_apply_apply x)
  right_inv y := Subtype.ext (β.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul β (x : S) y)
  map_add' x y := Subtype.ext (map_add β (x : S) y)

@[simp] theorem coe_equiv (x : integralClosure R S) :
    ((equiv α β h x : integralClosure R' S') : S') = β x := rfl

end JoshiTeich.Act1Scene1.IntegralClosureTransport
