/-
Source: Pi1/Orbicurve/Lefschetz.lean and Pi1/Orbicurve/Descent.lean
at revision ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.
-/
import Solutions.Source_ReferenceIutCanLiftConstantExtensionRamification
import Solutions.Source_ReferenceIutCanLiftRamificationTransport
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationSquare
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Ideal IntermediateField Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

noncomputable section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {s t : Ω}

/-- Integrality transfers from the polynomial ring in an integral parameter. -/
theorem isIntegral_polynomialBase_trans {x : Ω} (hs : IsIntegral (polynomialBase k t) s)
    (hx : IsIntegral (polynomialBase k s) x) : IsIntegral (polynomialBase k t) x := by
  let R : Subalgebra (polynomialBase k t) Ω := Algebra.adjoin (polynomialBase k t) {s}
  letI : Algebra.IsIntegral (polynomialBase k t) R :=
    Algebra.IsIntegral.adjoin (fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hs)
  have hle : polynomialBase k s ≤ R.restrictScalars k :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (Algebra.self_mem_adjoin_singleton _ s))
  let ι : polynomialBase k s →+* R := (Subalgebra.inclusion hle).toRingHom
  have hxR : IsIntegral R x := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map ι, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpx
  exact isIntegral_trans x hxR

theorem transcendental_of_integral_parameter (ht : Transcendental k t)
    (hts : IsIntegral (polynomialBase k s) t) : Transcendental k s := by
  intro hs
  apply ht
  letI : Algebra.IsIntegral k (polynomialBase k s) :=
    Algebra.IsIntegral.adjoin (fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hs.isIntegral)
  exact (isIntegral_trans t hts).isAlgebraic

/-- View the same ambient field over the rational field in the new parameter. -/
def changeParameterField (F : IntermediateField (rationalBase k t) Ω) (hs : s ∈ F) :
    IntermediateField (rationalBase k s) Ω :=
  IntermediateField.extendScalars (show rationalBase k s ≤ F.restrictScalars k from
    IntermediateField.adjoin_simple_le_iff.mpr hs)

@[simp] theorem mem_changeParameterField {F : IntermediateField (rationalBase k t) Ω}
    (hs : s ∈ F) (x : Ω) : x ∈ changeParameterField F hs ↔ x ∈ F := Iff.rfl

private def changeParameterCoordMap {F : IntermediateField (rationalBase k t) Ω}
    {L : IntermediateField (rationalBase k s) Ω} (hFL : ∀ x ∈ F, x ∈ L)
    (hts : IsIntegral (polynomialBase k s) t) (a : coordRing t F) : coordRing s L := by
  let x : Ω := (a : F)
  have hx : x ∈ L := hFL x (a : F).2
  have ha : IsIntegral (polynomialBase k t) x := isIntegral_of_mem_coordRing t (L := F) a
  have hi : IsIntegral (polynomialBase k s) x :=
    isIntegral_polynomialBase_trans (k := k) (s := t) (t := s) hts ha
  exact ⟨⟨x, hx⟩, mem_coordRing_of_isIntegral s (L := L) (x := x) hx hi⟩

private theorem coordRingVal_changeParameterCoordMap
    {F : IntermediateField (rationalBase k t) Ω} {L : IntermediateField (rationalBase k s) Ω}
    (hFL : ∀ x ∈ F, x ∈ L) (hts : IsIntegral (polynomialBase k s) t) (a : coordRing t F) :
    coordRingVal s (B := L) (changeParameterCoordMap hFL hts a) = coordRingVal t (B := F) a := rfl

private def changeParameterCoordHom {F : IntermediateField (rationalBase k t) Ω}
    {L : IntermediateField (rationalBase k s) Ω} (hFL : ∀ x ∈ F, x ∈ L)
    (hts : IsIntegral (polynomialBase k s) t) : coordRing t F →+* coordRing s L where
  toFun := changeParameterCoordMap hFL hts
  map_one' := by
    apply coordRingVal_injective s (B := L)
    simp only [coordRingVal_changeParameterCoordMap, map_one]
  map_mul' a b := by
    apply coordRingVal_injective s (B := L)
    simp only [coordRingVal_changeParameterCoordMap, map_mul]
  map_zero' := by
    apply coordRingVal_injective s (B := L)
    simp only [coordRingVal_changeParameterCoordMap, map_zero]
  map_add' a b := by
    apply coordRingVal_injective s (B := L)
    simp only [coordRingVal_changeParameterCoordMap, map_add]

private theorem coordRingVal_changeParameterCoordHom
    {F : IntermediateField (rationalBase k t) Ω} {L : IntermediateField (rationalBase k s) Ω}
    (hFL : ∀ x ∈ F, x ∈ L) (hts : IsIntegral (polynomialBase k s) t) (a : coordRing t F) :
    coordRingVal s (B := L) (changeParameterCoordHom hFL hts a) = coordRingVal t (B := F) a :=
  coordRingVal_changeParameterCoordMap hFL hts a

private theorem changeParameterCoordHom_comp {F : IntermediateField (rationalBase k t) Ω}
    {L : IntermediateField (rationalBase k s) Ω} (hFL : ∀ x ∈ F, x ∈ L) (hLF : ∀ x ∈ L, x ∈ F)
    (hts : IsIntegral (polynomialBase k s) t) (hst : IsIntegral (polynomialBase k t) s) :
    (changeParameterCoordHom hLF hst).comp (changeParameterCoordHom hFL hts) = RingHom.id _ := by
  apply RingHom.ext
  intro a
  apply coordRingVal_injective t (B := F)
  simp only [RingHom.comp_apply, RingHom.id_apply, coordRingVal_changeParameterCoordHom]

private def changeParameterCoordEquivOfInclusions {F : IntermediateField (rationalBase k t) Ω}
    {L : IntermediateField (rationalBase k s) Ω} (hFL : ∀ x ∈ F, x ∈ L) (hLF : ∀ x ∈ L, x ∈ F)
    (hts : IsIntegral (polynomialBase k s) t) (hst : IsIntegral (polynomialBase k t) s) :
    coordRing t F ≃ₐ[k] coordRing s L := by
  let e := RingEquiv.ofRingHom (changeParameterCoordHom hFL hts) (changeParameterCoordHom hLF hst)
    (changeParameterCoordHom_comp hLF hFL hst hts) (changeParameterCoordHom_comp hFL hLF hts hst)
  refine AlgEquiv.ofRingEquiv (f := e) fun c => coordRingVal_injective s (B := L) ?_
  change coordRingVal s (B := L) (changeParameterCoordHom hFL hts (algebraMap k _ c)) =
    coordRingVal s (B := L) (algebraMap k _ c)
  rw [coordRingVal_changeParameterCoordHom] <;> rfl

private theorem coordRingVal_changeParameterCoordEquivOfInclusions
    {F : IntermediateField (rationalBase k t) Ω} {L : IntermediateField (rationalBase k s) Ω}
    (hFL : ∀ x ∈ F, x ∈ L) (hLF : ∀ x ∈ L, x ∈ F)
    (hts : IsIntegral (polynomialBase k s) t) (hst : IsIntegral (polynomialBase k t) s)
    (a : coordRing t F) :
    coordRingVal s (B := L) (changeParameterCoordEquivOfInclusions hFL hLF hts hst a) =
      coordRingVal t (B := F) a :=
  coordRingVal_changeParameterCoordHom hFL hts a

/-- With integrality in both directions, the two coordinate rings have the same elements in Ω. -/
def changeParameterCoordEquiv {F : IntermediateField (rationalBase k t) Ω} (hs : s ∈ F)
    (hst : IsIntegral (polynomialBase k t) s) (hts : IsIntegral (polynomialBase k s) t) :
    coordRing t F ≃ₐ[k] coordRing s (changeParameterField F hs) :=
  changeParameterCoordEquivOfInclusions (F := F) (L := changeParameterField F hs)
    (fun x hx => (mem_changeParameterField hs x).mpr hx)
    (fun x hx => (mem_changeParameterField hs x).mp hx) hts hst

@[simp] theorem coordRingVal_changeParameterCoordEquiv
    {F : IntermediateField (rationalBase k t) Ω} (hs : s ∈ F)
    (hst : IsIntegral (polynomialBase k t) s) (hts : IsIntegral (polynomialBase k s) t)
    (a : coordRing t F) :
    coordRingVal s (B := changeParameterField F hs) (changeParameterCoordEquiv hs hst hts a) =
      coordRingVal t (B := F) a :=
  coordRingVal_changeParameterCoordEquivOfInclusions (F := F) (L := changeParameterField F hs)
    (fun x hx => (mem_changeParameterField hs x).mpr hx)
    (fun x hx => (mem_changeParameterField hs x).mp hx) hts hst a

@[simp] theorem coordRingVal_changeParameterCoordEquiv_symm
    {F : IntermediateField (rationalBase k t) Ω} (hs : s ∈ F)
    (hst : IsIntegral (polynomialBase k t) s) (hts : IsIntegral (polynomialBase k s) t)
    (a : coordRing s (changeParameterField F hs)) :
    coordRingVal t (B := F) ((changeParameterCoordEquiv hs hst hts).symm a) =
      coordRingVal s (B := changeParameterField F hs) a := by
  have h := coordRingVal_changeParameterCoordEquiv hs hst hts
    ((changeParameterCoordEquiv hs hst hts).symm a)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

private lemma isIntegral_rationalBase_trans {s' t' x : Ω} (hts : IsIntegral (rationalBase k s') t')
    (hx : IsIntegral (rationalBase k t') x) : IsIntegral (rationalBase k s') x := by
  let R : IntermediateField (rationalBase k s') Ω := IntermediateField.adjoin (rationalBase k s') {t'}
  haveI : FiniteDimensional (rationalBase k s') R := IntermediateField.adjoin.finiteDimensional hts
  have hle : ∀ z ∈ rationalBase k t', z ∈ R := by
    let R' : IntermediateField k Ω := R.restrictScalars k
    have : rationalBase k t' ≤ R' := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        IntermediateField.mem_restrictScalars]
      exact IntermediateField.mem_adjoin_simple_self _ t'
    exact fun z hz => this hz
  let ι : rationalBase k t' →+* R :=
    { toFun := fun a => ⟨a, hle a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  have hxR : IsIntegral R x := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map ι, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpx
  exact isIntegral_trans x hxR

/-- The field stays finite over the new rational base. -/
theorem finiteDimensional_changeParameter [CharZero k]
    {F : IntermediateField (rationalBase k t) Ω} {hs : s ∈ F} (hts : IsIntegral (polynomialBase k s) t)
    [FiniteDimensional (rationalBase k t) F] : FiniteDimensional (rationalBase k s) (changeParameterField F hs) := by
  haveI : CharZero (rationalBase k t) := charZero_of_injective_algebraMap (algebraMap k (rationalBase k t)).injective
  haveI : Algebra.IsSeparable (rationalBase k t) F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (rationalBase k t) F
  have htK : IsIntegral (rationalBase k s) t := hts.tower_top
  have hαK : IsIntegral (rationalBase k s) (α : Ω) := isIntegral_rationalBase_trans htK
    ((IsIntegral.of_finite (rationalBase k t) α).map (IsScalarTower.toAlgHom (rationalBase k t) F Ω))
  let S : Set Ω := {t, (α : Ω)}
  haveI : FiniteDimensional (rationalBase k s) (IntermediateField.adjoin (rationalBase k s) S) :=
    IntermediateField.finiteDimensional_adjoin_pair htK hαK
  have hle : changeParameterField F hs ≤ IntermediateField.adjoin (rationalBase k s) S := by
    intro x hx
    rw [mem_changeParameterField] at hx
    have h1 : (⟨x, hx⟩ : F) ∈ (rationalBase k t)⟮α⟯ := by
      rw [hα]
      exact IntermediateField.mem_top
    have h2 : x ∈ ((rationalBase k t)⟮α⟯).map F.val := ⟨_, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    let T : IntermediateField (rationalBase k t) Ω :=
      (IntermediateField.adjoin (rationalBase k s) S).toSubfield.toIntermediateField (fun c => by
        have : rationalBase k t ≤ (IntermediateField.adjoin (rationalBase k s) S).restrictScalars k := by
          rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
            IntermediateField.mem_restrictScalars]
          exact IntermediateField.subset_adjoin _ _ (Or.inl rfl)
        exact this c.2)
    have h3 : (rationalBase k t)⟮(F.val α)⟯ ≤ T := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin (rationalBase k s) S (Or.inr rfl)
    exact h3 h2
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

/-- **Exchange**: if `s` is transcendental over `k` and algebraic over `k[t]`, then `t` is
algebraic over `k[s]`. -/
theorem isAlgebraic_parameter_exchange (hs : Transcendental k s) (hst : IsAlgebraic (polynomialBase k t) s) :
    IsAlgebraic (polynomialBase k s) t := by
  by_contra h
  have h' : Transcendental (Algebra.adjoin k (Set.range fun _ : Unit => s)) t := by
    rw [Set.range_const]; exact h
  have hx : AlgebraicIndependent k (fun _ : Unit => s) :=
    (algebraicIndependent_unique_type_iff).mpr hs
  have hy := (hx.option_iff_transcendental t).mpr h'
  let e : Option Unit → Option Unit := fun o => o.elim (some ()) (fun _ => none)
  have he : Function.Injective e := by
    intro a b hab
    rcases a with _ | ⟨⟨⟩⟩ <;> rcases b with _ | ⟨⟨⟩⟩ <;> simp_all [e]
  have hz := hy.comp e he
  have hz' : AlgebraicIndependent k (fun o : Option Unit => o.elim s (fun _ : Unit => t)) := by
    convert hz using 1
    funext o
    rcases o with _ | ⟨⟨⟩⟩ <;> rfl
  have ht : AlgebraicIndependent k (fun _ : Unit => t) := by
    have := hz'.comp (fun u : Unit => some u) (Option.some_injective _)
    exact this
  have := (ht.option_iff_transcendental s).mp hz'
  rw [Set.range_const] at this
  exact this hst

/-- Changing the parameter of a compositum. -/
theorem adjoin_parameter_le {u v : Ω} {S : Set Ω}
    (hu : u ∈ IntermediateField.adjoin (rationalBase k v) S) {x : Ω}
    (hx : x ∈ IntermediateField.adjoin (rationalBase k u) S) : x ∈ IntermediateField.adjoin (rationalBase k v) S := by
  rw [← IntermediateField.mem_restrictScalars k, IntermediateField.restrictScalars_adjoin] at hx ⊢
  refine (IntermediateField.adjoin_le_iff.mpr ?_) hx
  rintro z (hz | hz)
  · have : rationalBase k u ≤ IntermediateField.adjoin k ((rationalBase k v : Set Ω) ∪ S) := by
      rw [IntermediateField.adjoin_simple_le_iff, ← IntermediateField.restrictScalars_adjoin,
        IntermediateField.mem_restrictScalars]
      exact hu
    exact this hz
  · exact IntermediateField.subset_adjoin _ _ (Or.inr hz)

/-- Identify the two polynomial lines by sending their variables to one another. -/
def changeParameterLineEquiv (ht : Transcendental k t) (hs : Transcendental k s) :
    coordRing t (⊥ : IntermediateField (rationalBase k t) Ω) ≃ₐ[k]
      coordRing s (⊥ : IntermediateField (rationalBase k s) Ω) :=
  (constantExtensionLineEquiv ht).symm.trans (constantExtensionLineEquiv hs)

@[simp] theorem changeParameterLineEquiv_apply (ht : Transcendental k t) (hs : Transcendental k s)
    (p : k[X]) : changeParameterLineEquiv ht hs (constantExtensionLineEquiv ht p) =
      constantExtensionLineEquiv hs p := by
  simp [changeParameterLineEquiv]

theorem parameterLineAlgHom_ext {B : Type u} [CommRing B] [Algebra k B] (ht : Transcendental k t)
    {f g : coordRing t (⊥ : IntermediateField (rationalBase k t) Ω) →ₐ[k] B}
    (h : f (constantExtensionLineEquiv ht X) = g (constantExtensionLineEquiv ht X)) : f = g := by
  have heq : f.comp (constantExtensionLineEquiv ht).toAlgHom =
      g.comp (constantExtensionLineEquiv ht).toAlgHom := Polynomial.algHom_ext h
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := (constantExtensionLineEquiv ht).surjective x
  exact DFunLike.congr_fun heq p

/-- Interpret an algebra map from the polynomial line as evaluation at its coordinate. -/
theorem coordRingVal_parameterAlgHom {F : IntermediateField (rationalBase k t) Ω}
    (ht : Transcendental k t)
    (f : coordRing t (⊥ : IntermediateField (rationalBase k t) Ω) →ₐ[k] coordRing t F)
    (p : k[X]) : coordRingVal t (f (constantExtensionLineEquiv ht p)) =
      aeval (coordRingVal t (f (constantExtensionLineEquiv ht X))) p := by
  letI : IsScalarTower k (coordRing t F) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let fΩ := (IsScalarTower.toAlgHom k (coordRing t F) Ω).comp
    (f.comp (constantExtensionLineEquiv ht).toAlgHom)
  have heq : fΩ = aeval (fΩ X) := Polynomial.algHom_ext (by rw [aeval_X])
  exact DFunLike.congr_fun heq p

/-- Integrality of the map from the line implies integrality of the old parameter over k[s]. -/
theorem isIntegral_old_parameter {F : IntermediateField (rationalBase k t) Ω}
    (ht : Transcendental k t)
    (f : coordRing t (⊥ : IntermediateField (rationalBase k t) Ω) →ₐ[k] coordRing t F)
    (hf : f.toRingHom.IsIntegral) :
    IsIntegral (polynomialBase k (coordRingVal t (f (constantExtensionLineEquiv ht X)))) t := by
  set s := coordRingVal t (f (constantExtensionLineEquiv ht X))
  let φ : coordRing t (⊥ : IntermediateField (rationalBase k t) Ω) →+* polynomialBase k s :=
    ((coordRingVal t).comp f.toRingHom).codRestrict (polynomialBase k s).toSubring (fun a => by
      obtain ⟨p, rfl⟩ := (constantExtensionLineEquiv ht).surjective a
      change coordRingVal t (f (constantExtensionLineEquiv ht p)) ∈ polynomialBase k s
      rw [coordRingVal_parameterAlgHom]
      exact Polynomial.aeval_mem_adjoin_singleton k s)
  let tF := ringMap (bot_le : (⊥ : IntermediateField (rationalBase k t) Ω) ≤ F)
    (constantExtensionLineEquiv ht X)
  obtain ⟨p, hp, hpt⟩ := hf tF
  refine ⟨p.map φ, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have htF : coordRingVal t tF = t :=
    (coe_constantExtensionLineEquiv ht X).trans (aeval_X t)
  have heval := Polynomial.hom_eval₂ p f.toRingHom (coordRingVal t) tF
  rw [hpt, map_zero, htF] at heval
  exact heval.symm

variable {F : IntermediateField (rationalBase k t) Ω}
  (ht : Transcendental k t) (hs : Transcendental k s) (hsF : s ∈ F)
  (hst : IsIntegral (polynomialBase k t) s) (hts : IsIntegral (polynomialBase k s) t)

/-- Map the variable of the old line to the new parameter in the normalization ring. -/
def parameterMap : coordRing t (⊥ : IntermediateField (rationalBase k t) Ω) →ₐ[k] coordRing t F :=
  (changeParameterCoordEquiv hsF hst hts).symm.toAlgHom.comp
    ((ringMap (bot_le : (⊥ : IntermediateField (rationalBase k s) Ω) ≤ changeParameterField F hsF)).comp
      (changeParameterLineEquiv ht hs).toAlgHom)

private theorem coordRingVal_ringMap {L L' : IntermediateField (rationalBase k t) Ω}
    (h : L ≤ L') (a : coordRing t L) :
    coordRingVal t (B := L') (ringMap h a) = coordRingVal t (B := L) a :=
  coe_ringMap h a

theorem parameterMap_coordRingVal (p : k[X]) :
    coordRingVal t (parameterMap ht hs hsF hst hts (constantExtensionLineEquiv ht p)) =
      aeval s p := by
  unfold parameterMap
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, coordRingVal_changeParameterCoordEquiv_symm,
    changeParameterLineEquiv_apply, coordRingVal_ringMap]
  exact coe_constantExtensionLineEquiv hs p

theorem parameterMap_injective : Function.Injective (parameterMap ht hs hsF hst hts) :=
  (changeParameterCoordEquiv hsF hst hts).symm.injective.comp
    ((ringMap_injective _).comp (changeParameterLineEquiv ht hs).injective)

theorem parameterMap_isIntegral : (parameterMap ht hs hsF hst hts).toRingHom.IsIntegral := by
  let e := (changeParameterLineEquiv ht hs).toRingEquiv
  let g := (changeParameterCoordEquiv hsF hst hts).symm.toRingEquiv
  let hle : (⊥ : IntermediateField (rationalBase k s) Ω) ≤ changeParameterField F hsF := bot_le
  let f := (ringMap hle).toRingHom
  change (g.toRingHom.comp (f.comp e.toRingHom)).IsIntegral
  exact RingHom.IsIntegral.trans (f.comp e.toRingHom) g.toRingHom
    (RingHom.IsIntegral.trans e.toRingHom f (RingHom.isIntegral_of_surjective _ e.surjective)
      (ringMap_isIntegral hle))
    (RingHom.isIntegral_of_surjective _ g.surjective)

private theorem changeParameter_comap_symm {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (w : Ideal B) : (w.comap e.toRingHom).comap e.symm.toRingHom = w := by
  ext x
  change e (e.symm x) ∈ w ↔ x ∈ w
  rw [RingEquiv.apply_symm_apply]

theorem parameterMap_ramification_iff [CharZero k] [FiniteDimensional (rationalBase k t) F]
    (m : Ideal (coordRing t (⊥ : IntermediateField (rationalBase k t) Ω)) → ℕ) :
    (∀ w : Ideal (coordRing t F), w.IsMaximal →
      (letI := (parameterMap ht hs hsF hst hts).toRingHom.toAlgebra;
        w.ramificationIdx (coordRing t (⊥ : IntermediateField (rationalBase k t) Ω))) =
          m (w.comap (parameterMap ht hs hsF hst hts))) ↔
    (∀ w : Ideal (coordRing s (changeParameterField F hsF)), w.IsMaximal →
      ramificationIndex (bot_le : (⊥ : IntermediateField (rationalBase k s) Ω) ≤
        changeParameterField F hsF) w =
        m ((w.comap (ringMap (bot_le : (⊥ : IntermediateField (rationalBase k s) Ω) ≤
          changeParameterField F hsF))).comap (changeParameterLineEquiv ht hs).toRingEquiv.toRingHom)) := by
  letI : FiniteDimensional (rationalBase k s) (changeParameterField F hsF) :=
    finiteDimensional_changeParameter (hs := hsF) hts
  letI : CharZero (rationalBase k s) :=
    charZero_of_injective_algebraMap (algebraMap k (rationalBase k s)).injective
  letI : Algebra.IsSeparable (rationalBase k s) (changeParameterField F hsF) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI := dedekindRing s hs (changeParameterField F hsF)
  letI := dedekindRing s hs (⊥ : IntermediateField (rationalBase k s) Ω)
  let e := (changeParameterLineEquiv ht hs).toRingEquiv
  let β := (changeParameterCoordEquiv hsF hst hts).toRingEquiv
  let hle : (⊥ : IntermediateField (rationalBase k s) Ω) ≤ changeParameterField F hsF := bot_le
  have he (w : Ideal (coordRing t F)) (hw : w.IsMaximal) :
      (letI := (parameterMap ht hs hsF hst hts).toRingHom.toAlgebra;
        w.ramificationIdx (coordRing t (⊥ : IntermediateField (rationalBase k t) Ω))) =
      ramificationIndex hle (w.comap β.symm.toRingHom) := by
    letI : w.IsPrime := hw.isPrime
    letI : (w.comap β.symm.toRingHom).IsPrime := Ideal.comap_isPrime _ _
    change (letI := (β.symm.toRingHom.comp ((ringMap hle).toRingHom.comp e.toRingHom)).toAlgebra;
      w.ramificationIdx _) = _
    exact (ramificationIdx_comp_equiv ((ringMap hle).toRingHom.comp e.toRingHom) β.symm w).trans
      (ramificationIdx_equiv_comp e (ringMap hle).toRingHom (ringMap_injective hle)
        (w.comap β.symm.toRingHom))
  have hc (w : Ideal (coordRing t F)) :
      (((w.comap β.symm.toRingHom).comap (ringMap hle)).comap e.toRingHom) =
        w.comap (parameterMap ht hs hsF hst hts) := by
    ext x
    exact Iff.rfl
  constructor
  · intro h w hw
    letI : w.IsMaximal := hw
    let wₜ := w.comap β.toRingHom
    have hwₜ : wₜ.IsMaximal := Ideal.comap_isMaximal_of_surjective _ β.surjective
    have hₜ := h wₜ hwₜ
    rw [he wₜ hwₜ, ← hc wₜ] at hₜ
    simpa only [wₜ, changeParameter_comap_symm] using hₜ
  · intro h w hw
    letI : w.IsMaximal := hw
    have hₛ := h (w.comap β.symm.toRingHom)
      (Ideal.comap_isMaximal_of_surjective _ β.symm.surjective)
    rw [he w hw]
    exact hₛ.trans (congrArg m (hc w))

end

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
