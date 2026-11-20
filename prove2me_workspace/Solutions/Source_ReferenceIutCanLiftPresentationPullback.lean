/-
Source: lana-agents/pi1 at ca7def953193f861a462aa0831eec8f0a31ff69f (Apache-2.0),
Pi1/Orbicurve/Pullback.lean, pullback_ofSubfield.
-/
import Solutions.Source_ReferenceIutCanLiftSubfieldPullback
import Solutions.Source_ReferenceIutCanLiftNormalizationEmbed
import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentationIso

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open AffineOrbicurvePresentation IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

noncomputable section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

/-- The affine presentation on a normalization ring with the given multiplicities. -/
def subfieldPresentation (ht : Transcendental k t) (L : IntermediateField (rationalBase k t) Ω)
    [FiniteDimensional (rationalBase k t) L] [Algebra.IsSeparable (rationalBase k t) L]
    (m : Ideal (coordRing t L) → ℕ) (m_pos : ∀ w, w.IsMaximal → 0 < m w)
    (m_fin : {w : Ideal (coordRing t L) | w.IsMaximal ∧ m w ≠ 1}.Finite) :
    AffineOrbicurvePresentation k where
  A := coordRing t L
  isDedekindDomain := dedekindRing t ht L
  finiteType := finiteTypeRing t ht L
  not_isField := notFieldRing t ht L
  mult := m
  mult_pos := m_pos
  finite_mult := m_fin

private theorem cover_ramification_of_map {X Y : AffineOrbicurvePresentation k}
    (f : Cover X Y) {g : Y.A →ₐ[k] X.A} (hg : f.f = g) (w : Ideal X.A) (hw : w.IsMaximal) :
    (letI := g.toRingHom.toAlgebra; w.ramificationIdx Y.A) * X.mult w = Y.mult (w.comap g) := by
  subst g
  exact f.ramification w hw

private theorem transportedCover_ramification {Y Z : AffineOrbicurvePresentation k} {R : Type u}
    [CommRing R] [IsDomain R] [Algebra k R] [IsDedekindDomain R] [Algebra.FiniteType k R]
    (ψ : Z.A ≃ₐ[k] R) (f : Cover Z Y) (g : Y.A →ₐ[k] R)
    (hg : ∀ a, ψ (f.f a) = g a) (w : Ideal R) (hw : w.IsMaximal) :
    (letI := g.toRingHom.toAlgebra; w.ramificationIdx Y.A) *
      (ofAlgEquiv Z R ψ.symm).mult w = Y.mult (w.comap g) := by
  let ζ := (ofAlgEquivEquiv Z R ψ.symm).symm.toCover
  exact cover_ramification_of_map (ζ.comp f) (AlgHom.ext hg) w hw

variable [CharZero k] [Normal (rationalBase k t) Ω]

private theorem commonCover_of_subfields (ht : Transcendental k t)
    {B A Z : IntermediateField (rationalBase k t) Ω}
    [FiniteDimensional (rationalBase k t) B]
    [FiniteDimensional (rationalBase k t) A] [Algebra.IsSeparable (rationalBase k t) A]
    [FiniteDimensional (rationalBase k t) Z] [Algebra.IsSeparable (rationalBase k t) Z]
    (hBA : B ≤ A) (hBZ : B ≤ Z)
    (mB : Ideal (coordRing t B) → ℕ) (mB_pos : ∀ w, w.IsMaximal → 0 < mB w)
    (mB_fin : {w : Ideal (coordRing t B) | w.IsMaximal ∧ mB w ≠ 1}.Finite)
    {mA : Ideal (coordRing t A) → ℕ} {mA_pos mA_fin}
    {mZ : Ideal (coordRing t Z) → ℕ} {mZ_pos mZ_fin}
    (hA : ∀ w : Ideal (coordRing t A), w.IsMaximal →
      ramificationIndex hBA w * mA w = mB (w.comap (ringMap hBA)))
    (hZ : ∀ w : Ideal (coordRing t Z), w.IsMaximal →
      ramificationIndex hBZ w * mZ w = mB (w.comap (ringMap hBZ))) :
    ∃ W : AffineOrbicurvePresentation k,
      Nonempty (Cover W (subfieldPresentation ht Z mZ mZ_pos mZ_fin)) ∧
        Nonempty (Cover W (subfieldPresentation ht A mA mA_pos mA_fin)) := by
  obtain ⟨m, m_pos, m_fin, hmZ, hmA⟩ :=
    exists_pullback_subfield ht hBA hBZ mB mB_pos mB_fin mA mZ hA hZ
  have : CharZero (rationalBase k t) :=
    charZero_of_injective_algebraMap (algebraMap k (rationalBase k t)).injective
  have : FiniteDimensional (rationalBase k t) ↥(Z ⊔ A) := finiteDimensional_sup Z A
  have : Algebra.IsSeparable (rationalBase k t) ↥(Z ⊔ A) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  let W := subfieldPresentation ht (Z ⊔ A) m m_pos m_fin
  let hZL : Z ≤ Z ⊔ A := le_sup_left
  let hAL : A ≤ Z ⊔ A := le_sup_right
  exact ⟨W,
    ⟨⟨ringMap hZL, ringMap_injective hZL, ringMap_isIntegral hZL, hmZ⟩⟩,
    ⟨⟨ringMap hAL, ringMap_injective hAL, ringMap_isIntegral hAL, hmA⟩⟩⟩

/-- The compositum construction dominates a cover of the base and the specified subfield cover. -/
theorem pullback_ofSubfield (ht : Transcendental k t)
    [IsAlgClosed Ω]
    {B A : IntermediateField (rationalBase k t) Ω}
    [FiniteDimensional (rationalBase k t) B] [Algebra.IsSeparable (rationalBase k t) B]
    [FiniteDimensional (rationalBase k t) A] [Algebra.IsSeparable (rationalBase k t) A]
    (hBA : B ≤ A) {mB : Ideal (coordRing t B) → ℕ} {mB_pos mB_fin}
    {mA : Ideal (coordRing t A) → ℕ} {mA_pos mA_fin}
    (f : Cover (subfieldPresentation ht A mA mA_pos mA_fin)
      (subfieldPresentation ht B mB mB_pos mB_fin))
    (hf : f.f = ringMap hBA)
    (Z : AffineOrbicurvePresentation k) (φ : Cover Z (subfieldPresentation ht B mB mB_pos mB_fin)) :
    ∃ W : AffineOrbicurvePresentation k, Nonempty (Cover W Z) ∧
      Nonempty (Cover W (subfieldPresentation ht A mA mA_pos mA_fin)) := by
  have : CharZero (rationalBase k t) :=
    charZero_of_injective_algebraMap (algebraMap k (rationalBase k t)).injective
  obtain ⟨LZ, hLZ, hBZ, ψ, hψ⟩ := exists_algEquiv_coordRing t Z.A φ.f φ.injective φ.isIntegral
  have : Algebra.IsSeparable (rationalBase k t) LZ :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : IsDedekindDomain (coordRing t LZ) := dedekindRing t ht LZ
  have : Algebra.FiniteType k (coordRing t LZ) := finiteTypeRing t ht LZ
  let ZL := ofAlgEquiv Z (coordRing t LZ) ψ.symm
  let ζ : Cover ZL Z := (ofAlgEquivEquiv Z (coordRing t LZ) ψ.symm).symm.toCover
  obtain ⟨W, ⟨πZ⟩, hπA⟩ :=
    commonCover_of_subfields ht hBA hBZ mB mB_pos mB_fin
      (mA := mA) (mA_pos := mA_pos) (mA_fin := mA_fin)
      (mZ := ZL.mult) (mZ_pos := ZL.mult_pos) (mZ_fin := ZL.finite_mult)
      (cover_ramification_of_map f hf) (transportedCover_ramification ψ φ (ringMap hBZ) hψ)
  exact ⟨W, ⟨πZ.comp ζ⟩, hπA⟩

end

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
