import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.Topology.Irreducible

/-!
source-id: JT-SCENE1-FINITE-ETALE-RANK-ONE-ISO
source: Mathlib finite flat morphism rank and local constancy;
IUT I Definition 3.1(d), comparison on the unbranched covering open.
fidelity: a finite flat locally finitely presented morphism over a
preconnected target is an isomorphism if it has rank one at a single point,
or if its restriction to a nonempty open is an isomorphism.
Original proofs; no reference implementation copied.
boundary: this is a scheme-theoretic comparison criterion. It does not
assume or construct an orbicurve realization or a geometry producer.
-/

namespace JoshiTeich.Act1Scene1

open CategoryTheory AlgebraicGeometry
universe u
section Rank
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] [PreconnectedSpace Y]

theorem finiteFlat_isIso_of_finrank_eq_one_at (y : Y) (hy : f.finrank y = 1) :
    IsIso f := by
  apply (Scheme.Hom.isIso_iff_finrank_eq f).mpr
  ext z
  exact ((Scheme.Hom.isLocallyConstant_finrank f).apply_eq_of_preconnectedSpace z y).trans hy

theorem finiteFlat_isIso_of_nonempty_isIso_restrict
    (U : Y.Opens) (hU : (U : Set Y).Nonempty) [IsIso (f ∣_ U)] : IsIso f := by
  obtain ⟨y, hy⟩ := hU
  let u : U := ⟨y, hy⟩
  apply finiteFlat_isIso_of_finrank_eq_one_at f (U.ι u)
  have hp := Scheme.Hom.finrank_of_isPullback
    (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι (isPullback_morphismRestrict f U).flip u
  exact hp.symm.trans (congrFun (Scheme.Hom.finrank_eq_one_of_isIso (f ∣_ U)) u)

end Rank

theorem isIso_double_restrict_of_isIso_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (W V : Y.Opens) [IsIso (f ∣_ W)] :
    IsIso ((f ∣_ V) ∣_ (V.ι ⁻¹ᵁ W)) := by
  have hVW : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W.ι ''ᵁ (W.ι ⁻¹ᵁ V) := by
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_comm V W
  let e := morphismRestrictRestrict f V (V.ι ⁻¹ᵁ W) ≪≫
    morphismRestrictEq f hVW ≪≫
    (morphismRestrictRestrict f W (W.ι ⁻¹ᵁ V)).symm
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).mpr
    (inferInstanceAs (IsIso ((f ∣_ W) ∣_ (W.ι ⁻¹ᵁ V))))

theorem finiteFlat_isIso_restrict_of_dense_isIso_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    (W V : Y.Opens) (hW : Dense (W : Set Y)) (hV : (V : Set Y).Nonempty)
    [IsIso (f ∣_ W)] [Flat (f ∣_ V)] [IsFinite (f ∣_ V)]
    [LocallyOfFinitePresentation (f ∣_ V)] : IsIso (f ∣_ V) := by
  have : Nonempty V.toScheme := ⟨⟨hV.some, hV.some_mem⟩⟩
  have : IrreducibleSpace V.toScheme := V.ι.isOpenEmbedding.irreducibleSpace
  have hVW : ((V.ι ⁻¹ᵁ W : V.toScheme.Opens) : Set V.toScheme).Nonempty := by
    obtain ⟨y, hyV, hyW⟩ := hW.inter_open_nonempty (V : Set Y) V.isOpen hV
    exact ⟨⟨y, hyV⟩, hyW⟩
  have : IsIso ((f ∣_ V) ∣_ (V.ι ⁻¹ᵁ W)) :=
    isIso_double_restrict_of_isIso_restrict f W V
  exact finiteFlat_isIso_of_nonempty_isIso_restrict (f ∣_ V) (V.ι ⁻¹ᵁ W) hVW

end JoshiTeich.Act1Scene1
