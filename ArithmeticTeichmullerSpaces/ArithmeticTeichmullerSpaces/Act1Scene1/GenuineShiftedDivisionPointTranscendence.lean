import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionFieldTranslation

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the actual division-field translation and selected division-point transcendence.
fidelity: translation of the SAME selected Qpt by the SAME constant point has
transcendental x coordinate. The proof transports algebraicity through the
existing automorphism of the original QField and its original inclusion.
Original composition of existing project theorems; no reference code copied.
boundary: no coordinate-field generation or normalization residue identity.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
noncomputable section
universe u

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

local instance shiftedDivisionTranscendence_decidableEq : DecidableEq (Ω E) :=
  fun a b => Classical.propDecidable (a = b)

/-- Translation preserves transcendence of the same selected division point's x coordinate. -/
theorem Qpt_add_base_x_transcendental
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) :
    Transcendental k (ptX (Affine.Point.add (W := (E⁄(Ω E)).toAffine)
      (Qpt E n) (base E T))) := by
  let qx : QField E n :=
    ⟨ptX (Qpt E n), IntermediateField.subset_adjoin _ _ (by simp)⟩
  let σ : QField E n ≃ₐ[k] QField E n := divisionFieldTranslationEquiv E n hn T
  let ι : QField E n →ₐ[k] Ω E := divisionFieldInclusion E n
  have heval : ι (σ qx) = ptX (Affine.Point.add (W := (E⁄(Ω E)).toAffine)
      (Qpt E n) (base E T)) :=
    divisionFieldTranslationEquiv_X E n hn T
  intro hx
  have hmap : IsAlgebraic k ((ι.comp σ.toAlgHom) qx) := by
    change IsAlgebraic k (ι (σ qx))
    rwa [heval]
  have hqx : IsAlgebraic k qx :=
    (isAlgebraic_algHom_iff (ι.comp σ.toAlgHom) (ι.comp σ.toAlgHom).injective).mp hmap
  exact Qpt_xCoord_transcendental E n hn (by
    change IsAlgebraic k (ι qx)
    exact hqx.algHom ι)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
