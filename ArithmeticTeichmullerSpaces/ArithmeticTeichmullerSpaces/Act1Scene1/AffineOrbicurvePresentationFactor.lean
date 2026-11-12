import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentationCategory

/-!
source-id: JT-SCENE1-AFFINE-ORBICURVE-PRESENTATION-FACTOR
source: IUT I Definition 3.1(d); ramification indices in an integral tower.
fidelity: a factor of an unramified cover between presentations with
multiplicity one inherits the precise Cover law from the same cone leg.
Original proofs; no reference implementation copied.
boundary: a factorization criterion inside the existing presentation category.
-/

namespace JoshiTeich.Act1Scene1.AffineOrbicurvePresentation

universe u
noncomputable section
variable {k : Type u} [Field k]

def Cover.factorThroughUnramified {D B Z : AffineOrbicurvePresentation k}
    (u : Cover B Z) (b : Cover D Z) (j : B.A →ₐ[k] D.A)
    (hj : Function.Injective j) (hfac : j.comp u.f = b.f)
    (hB : ∀ q, B.mult q = 1) (hZ : ∀ q, Z.mult q = 1)
    (hu : ∀ q : Ideal B.A, q.IsMaximal →
      (letI := u.f.toRingHom.toAlgebra; q.ramificationIdx Z.A) = 1) : Cover D B := by
  have hfacR : j.toRingHom.comp u.f.toRingHom = b.f.toRingHom :=
    congrArg AlgHom.toRingHom hfac
  have hint : j.toRingHom.IsIntegral := by
    apply RingHom.IsIntegral.tower_top u.f.toRingHom j.toRingHom
    rw [hfacR]
    exact b.isIntegral
  refine ⟨j, hj, hint, ?_⟩
  intro w hw
  have : w.IsMaximal := hw
  have hq : (w.comap j.toRingHom).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' j.toRingHom hint w
  have ht := FunctionFieldNormalization.ramificationIdx_comp u.f.toRingHom j.toRingHom hj w
  rw [hu _ hq, one_mul] at ht
  have hidx :
      (letI := (j.toRingHom.comp u.f.toRingHom).toAlgebra; w.ramificationIdx Z.A) =
      (letI := b.f.toRingHom.toAlgebra; w.ramificationIdx Z.A) :=
    congrArg (fun f : Z.A →+* D.A => letI := f.toAlgebra; w.ramificationIdx Z.A) hfacR
  exact (congrArg (fun n => n * D.mult w) (ht.symm.trans hidx)).trans
    ((b.ramification w hw).trans ((hZ _).trans (hB _).symm))

end
end JoshiTeich.Act1Scene1.AffineOrbicurvePresentation
