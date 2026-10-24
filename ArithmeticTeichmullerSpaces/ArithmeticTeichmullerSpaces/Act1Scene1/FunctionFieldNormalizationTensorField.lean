import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationTensor

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); fraction fields of the actual normalization
rings and generation of a compositum by its two subfields.
fidelity: when the common field is the compositum, the tensor image generates
exactly that field. This identifies the selected ambient field, without
assuming that the tensor algebra is a domain or that its map is injective.
boundary: Scene1/Derived. The orbicurve pullback law remains separate.
-/

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open scoped Classical TensorProduct IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
variable {F Z N : IntermediateField (rationalBase k t) Ω}

def normalizationTensorAmbientMap (hF : F ≤ N) (hZ : Z ≤ N) :
    (coordRing t F ⊗[polynomialBase k t] coordRing t Z) →ₐ[polynomialBase k t] Ω :=
  (N.val.restrictScalars (polynomialBase k t)).comp (normalizationTensorFieldMap hF hZ)

theorem normalizationTensorAmbientMap_tmul (hF : F ≤ N) (hZ : Z ≤ N)
    (a : coordRing t F) (b : coordRing t Z) :
    normalizationTensorAmbientMap hF hZ (a ⊗ₜ b) = ((a : F) : Ω) * ((b : Z) : Ω) := rfl

theorem field_le_of_coordRing_le [FiniteDimensional (rationalBase k t) F]
    [Algebra.IsSeparable (rationalBase k t) F] (U : Subfield Ω)
    (h : ∀ a : coordRing t F, ((a : F) : Ω) ∈ U) : F.toSubfield ≤ U := by
  have : IsFractionRing (coordRing t F) F := fractionFieldRing t F
  intro x hx
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := coordRing t F) (⟨x, hx⟩ : F)
  have he := congrArg (fun z : F => (z : Ω)) hab
  change ((a : F) : Ω) / ((b : F) : Ω) = x at he
  exact he ▸ U.div_mem (h a) (h b)

theorem normalizationTensorAmbientMap_fieldClosure
    [FiniteDimensional (rationalBase k t) F] [Algebra.IsSeparable (rationalBase k t) F]
    [FiniteDimensional (rationalBase k t) Z] [Algebra.IsSeparable (rationalBase k t) Z]
    (hF : F ≤ N) (hZ : Z ≤ N) (hN : F ⊔ Z = N) :
    Subfield.closure (Set.range (normalizationTensorAmbientMap hF hZ)) = N.toSubfield := by
  apply le_antisymm
  · apply Subfield.closure_le.mpr
    rintro x ⟨a, rfl⟩
    exact (normalizationTensorFieldMap hF hZ a).2
  · have hF' : F.toSubfield ≤ Subfield.closure (Set.range (normalizationTensorAmbientMap hF hZ)) :=
      field_le_of_coordRing_le (F := F) _ fun a =>
        Subfield.subset_closure ⟨a ⊗ₜ (1 : coordRing t Z),
          (normalizationTensorAmbientMap_tmul hF hZ a 1).trans (mul_one _)⟩
    have hZ' : Z.toSubfield ≤ Subfield.closure (Set.range (normalizationTensorAmbientMap hF hZ)) :=
      field_le_of_coordRing_le (F := Z) _ fun b =>
        Subfield.subset_closure ⟨(1 : coordRing t F) ⊗ₜ b,
          (normalizationTensorAmbientMap_tmul hF hZ 1 b).trans (one_mul _)⟩
    have hsup : (F ⊔ Z).toSubfield ≤
        Subfield.closure (Set.range (normalizationTensorAmbientMap hF hZ)) := by
      rw [IntermediateField.sup_toSubfield]
      exact sup_le hF' hZ'
    simpa only [hN] using hsup

theorem normalizationTensorFieldMap_fieldClosure
    [FiniteDimensional (rationalBase k t) F] [Algebra.IsSeparable (rationalBase k t) F]
    [FiniteDimensional (rationalBase k t) Z] [Algebra.IsSeparable (rationalBase k t) Z]
    (hF : F ≤ N) (hZ : Z ≤ N) (hN : F ⊔ Z = N) :
    Subfield.closure (Set.range (normalizationTensorFieldMap hF hZ)) = ⊤ := by
  have htop : (⊤ : Subfield N).map N.val.toRingHom = N.toSubfield := by
    ext x
    constructor
    · rintro ⟨a, _, rfl⟩
      exact a.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hmap : (Subfield.closure (Set.range (normalizationTensorFieldMap hF hZ))).map N.val.toRingHom =
      (⊤ : Subfield N).map N.val.toRingHom := by
    rw [htop, RingHom.map_field_closure, ← Set.range_comp]
    exact normalizationTensorAmbientMap_fieldClosure hF hZ hN
  have h := congrArg (Subfield.comap N.val.toRingHom) hmap
  simpa only [Subfield.comap_map] using h

theorem fractionRing_of_fieldClosure {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] (hinj : Function.Injective (algebraMap R K))
    (hgen : Subfield.closure (Set.range (algebraMap R K)) = ⊤) : IsFractionRing R K := by
  let f : FractionRing R →ₐ[R] K :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId R K) hinj
  have hf : f.toRingHom.fieldRange = ⊤ :=
    (IsFractionRing.lift_fieldRange (K := FractionRing R) hinj).trans hgen
  exact IsFractionRing.of_algEquiv
    (AlgEquiv.ofBijective f ⟨f.injective, RingHom.fieldRange_eq_top_iff.mp hf⟩)

theorem normalizationTensorImage_fractionField
    [FiniteDimensional (rationalBase k t) F] [Algebra.IsSeparable (rationalBase k t) F]
    [FiniteDimensional (rationalBase k t) Z] [Algebra.IsSeparable (rationalBase k t) Z]
    (hF : F ≤ N) (hZ : Z ≤ N) (hN : F ⊔ Z = N) :
    IsFractionRing (normalizationTensorFieldMap hF hZ).range N := by
  apply fractionRing_of_fieldClosure Subtype.val_injective
  have hrange : Set.range (algebraMap (normalizationTensorFieldMap hF hZ).range N) =
      Set.range (normalizationTensorFieldMap hF hZ) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · rintro ⟨a, rfl⟩
      exact ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩
  rw [hrange]
  exact normalizationTensorFieldMap_fieldClosure hF hZ hN

theorem normalizationTensorImage_isIntegralClosure (hF : F ≤ N) (hZ : Z ≤ N) :
    IsIntegralClosure (coordRing t N) (normalizationTensorFieldMap hF hZ).range N := by
  let f := normalizationTensorFieldMap hF hZ
  have : Algebra.IsIntegral (polynomialBase k t)
      (coordRing t F ⊗[polynomialBase k t] coordRing t Z) := normalizationTensor_integral
  have hs : Function.Surjective f.rangeRestrict := fun ⟨_, hy⟩ =>
    Exists.elim hy fun x hx => ⟨x, Subtype.ext hx⟩
  have : Algebra.IsIntegral (polynomialBase k t) f.range :=
    Algebra.IsIntegral.of_surjective (R := polynomialBase k t)
      (A := coordRing t F ⊗[polynomialBase k t] coordRing t Z) (B := f.range) f.rangeRestrict hs
  exact IsIntegralClosure.tower_top (R := polynomialBase k t) (A := f.range) (B := N) (C := coordRing t N)

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
