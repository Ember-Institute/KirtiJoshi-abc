import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationInertia

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Mathlib ramification in a tower.
fidelity: compares the ramification indices along both paths of a square of
actual normalization inclusions. Closed points contract to closed points.
boundary: Scene1/Derived. This is a ring-theoretic square comparison; it does
not assert that a scheme or orbicurve square is cartesian.
-/

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

/-- The index for the algebra of the literal normalization inclusion. -/
abbrev ramificationIndex {F L : IntermediateField (rationalBase k t) Ω}
    (h : F ≤ L) (w : Ideal (coordRing t L)) : ℕ :=
  letI := ringMapAlgebra h
  w.ramificationIdx (coordRing t F)

theorem normalization_comap_isMaximal {F L : IntermediateField (rationalBase k t) Ω}
    (h : F ≤ L) (w : Ideal (coordRing t L)) (hw : w.IsMaximal) :
    (w.comap (ringMap h)).IsMaximal := by
  have : w.IsMaximal := hw
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
    (ringMap h).toRingHom (ringMap_isIntegral h) w

theorem ramificationIndex_tower {F L N : IntermediateField (rationalBase k t) Ω}
    [FiniteDimensional (rationalBase k t) L] [Algebra.IsSeparable (rationalBase k t) L]
    (ht : Transcendental k t) (hFL : F ≤ L) (hLN : L ≤ N) (w : Ideal (coordRing t N)) :
    ramificationIndex (hFL.trans hLN) w =
      ramificationIndex hFL (w.comap (ringMap hLN)) * ramificationIndex hLN w := by
  have := dedekindRing t ht L
  exact ramificationIdx_comp (ringMap hFL).toRingHom (ringMap hLN).toRingHom
    (ringMap_injective hLN) w

/-- Both products compute the index for the same composite ambient inclusion. -/
theorem ramificationIndex_square {A B C D : IntermediateField (rationalBase k t) Ω}
    [FiniteDimensional (rationalBase k t) B] [Algebra.IsSeparable (rationalBase k t) B]
    [FiniteDimensional (rationalBase k t) C] [Algebra.IsSeparable (rationalBase k t) C]
    (ht : Transcendental k t) (hAB : A ≤ B) (hAC : A ≤ C) (hBD : B ≤ D) (hCD : C ≤ D)
    (w : Ideal (coordRing t D)) :
    ramificationIndex hAC (w.comap (ringMap hCD)) * ramificationIndex hCD w =
      ramificationIndex hAB (w.comap (ringMap hBD)) * ramificationIndex hBD w :=
  (ramificationIndex_tower ht hAC hCD w).symm.trans
    (ramificationIndex_tower ht hAB hBD w)

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
