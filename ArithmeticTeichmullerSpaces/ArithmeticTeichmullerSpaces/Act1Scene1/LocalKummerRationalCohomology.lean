import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCyclotomicCharacter

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-RATIONAL-COHOMOLOGY
source: Q_p(1) coefficients before the Bloch--Kato comparison, Joshi III (3214--3236).
fidelity: realizes the rational Tate representation on the usual topological
field Q_p using the character derived from the actual Tate group. The integral
coefficient map is injective, continuous and equivariant, and its image spans.
Actual continuous cocycles give standard rational H1 classes, invariant under
coboundaries. This does not prove H^1_e membership or a BK logarithm formula.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.Rational
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]

def coefficientMap : Additive (cyclotomicTateGroup p Ω) →+ ℚ_[p] :=
  PadicInt.Coe.ringHom.toAddMonoidHom.comp
    (TateBasis.equiv (p := p) (Ω := Ω)).symm.toLinearEquiv.toAddMonoidHom

theorem coefficientMap_injective : Function.Injective (coefficientMap (Ω := Ω) p) :=
  fun _ _ h => (TateBasis.equiv (p := p) (Ω := Ω)).symm.injective (Subtype.coe_injective h)

theorem continuous_coefficientMap : Continuous (coefficientMap (Ω := Ω) p) :=
  continuous_subtype_val.comp (TateBasis.equiv (p := p) (Ω := Ω)).symm.continuous

theorem coefficientMap_smul (r : ℤ_[p]) (x : Additive (cyclotomicTateGroup p Ω)) :
    coefficientMap p (r • x) = (r : ℚ_[p]) * coefficientMap p x := by
  change ((TateBasis.equiv (p := p) (Ω := Ω)).symm (r • x) : ℚ_[p]) =
    (r : ℚ_[p]) * ((TateBasis.equiv (p := p) (Ω := Ω)).symm x : ℚ_[p])
  rw [map_smul, smul_eq_mul, PadicInt.coe_mul]

theorem coefficientMap_basis (r : ℤ_[p]) :
    coefficientMap p (TateBasis.equiv (p := p) (Ω := Ω) r) = (r : ℚ_[p]) :=
  congrArg (fun z : ℤ_[p] => (z : ℚ_[p]))
    ((TateBasis.equiv (p := p) (Ω := Ω)).symm_apply_apply r)

theorem exists_smul_coefficientMap (q : ℚ_[p]) :
    ∃ (a : ℚ_[p]) (x : Additive (cyclotomicTateGroup p Ω)), a • coefficientMap p x = q := by
  refine ⟨q, TateBasis.equiv (p := p) (Ω := Ω) 1, ?_⟩
  rw [coefficientMap_basis, PadicInt.coe_one, smul_eq_mul, mul_one]

def representation : ContRepresentation ℚ_[p] (Ω ≃ₐ[K] Ω) ℚ_[p] where
  toMonoidHom.toFun σ :=
    ContinuousLinearMap.toSpanSingleton ℚ_[p] (Cyclotomic.coefficient p σ : ℚ_[p])
  toMonoidHom.map_one' := by
    apply ContinuousLinearMap.ext
    intro q
    change q * (Cyclotomic.coefficient (K := K) (Ω := Ω) p 1 : ℚ_[p]) = q
    rw [Cyclotomic.coefficient_one, PadicInt.coe_one, mul_one]
  toMonoidHom.map_mul' σ τ := by
    apply ContinuousLinearMap.ext
    intro q
    change q * (Cyclotomic.coefficient p (σ * τ) : ℚ_[p]) =
      (q * (Cyclotomic.coefficient p τ : ℚ_[p])) * (Cyclotomic.coefficient p σ : ℚ_[p])
    rw [Cyclotomic.coefficient_mul, PadicInt.coe_mul]
    ac_rfl

theorem representation_apply (σ : Ω ≃ₐ[K] Ω) (q : ℚ_[p]) :
    representation p σ q = (Cyclotomic.character p σ : ℤ_[p]) * (q : ℚ_[p]) :=
  mul_comm _ _

theorem continuous_action :
    Continuous (fun z : (Ω ≃ₐ[K] Ω) × ℚ_[p] => representation p z.1 z.2) := by
  exact continuous_snd.mul
    (continuous_subtype_val.comp ((Cyclotomic.continuous_coefficient p).comp continuous_fst))

theorem coefficientMap_equivariant (σ : Ω ≃ₐ[K] Ω)
    (x : Additive (cyclotomicTateGroup p Ω)) :
    coefficientMap p (padicTateRepresentation p σ x) = representation p σ (coefficientMap p x) := by
  change ((TateBasis.equiv (p := p) (Ω := Ω)).symm
      (padicTateRepresentation p σ x) : ℚ_[p]) =
    ((TateBasis.equiv (p := p) (Ω := Ω)).symm x : ℚ_[p]) *
      (Cyclotomic.coefficient p σ : ℚ_[p])
  rw [Cyclotomic.coordinate_action, PadicInt.coe_mul, mul_comm]

/- The standard cochain complex requires the coefficient space to live in
the Galois group's universe. ULift carries the transported p-adic topology. -/
def liftedRepresentation : ContRepresentation ℚ_[p] (Ω ≃ₐ[K] Ω) (ULift.{v} ℚ_[p]) where
  toMonoidHom.toFun σ :=
    (ContinuousLinearEquiv.ulift : ULift.{v} ℚ_[p] ≃L[ℚ_[p]] ℚ_[p]).symm.toContinuousLinearMap ∘L
      representation p σ ∘L ContinuousLinearEquiv.ulift.toContinuousLinearMap
  toMonoidHom.map_one' := by
    apply ContinuousLinearMap.ext
    intro q
    apply ULift.ext
    change representation (K := K) (Ω := Ω) p 1 q.down = q.down
    rw [map_one]
    rfl
  toMonoidHom.map_mul' σ τ := by
    apply ContinuousLinearMap.ext
    intro q
    apply ULift.ext
    change representation p (σ * τ) q.down = representation p σ (representation p τ q.down)
    rw [map_mul]
    rfl

theorem liftedRepresentation_down (σ : Ω ≃ₐ[K] Ω) (q : ULift.{v} ℚ_[p]) :
    (liftedRepresentation p σ q).down = representation p σ q.down := rfl

theorem continuous_liftedAction :
    Continuous (fun z : (Ω ≃ₐ[K] Ω) × ULift.{v} ℚ_[p] => liftedRepresentation p z.1 z.2) := by
  change Continuous (fun z : (Ω ≃ₐ[K] Ω) × ULift.{v} ℚ_[p] =>
    ULift.up (z.2.down * (Cyclotomic.coefficient p z.1 : ℚ_[p])))
  have hc : Continuous (fun z : (Ω ≃ₐ[K] Ω) × ULift.{v} ℚ_[p] =>
      (Cyclotomic.coefficient p z.1 : ℚ_[p])) :=
    continuous_subtype_val.comp
      ((Cyclotomic.continuous_coefficient (K := K) (Ω := Ω) p).comp continuous_fst)
  have hd : Continuous (fun z : (Ω ≃ₐ[K] Ω) × ULift.{v} ℚ_[p] => z.2.down) :=
    continuous_uliftDown.comp continuous_snd
  exact continuous_uliftUp.comp (hd.mul hc)

def topRep : TopRep.{v} ℚ_[p] (Ω ≃ₐ[K] Ω) :=
  TopRep.of (liftedRepresentation (K := K) (Ω := Ω) p)

def cocycle (f : continuousCocycles (K := K) (Ω := Ω) p) :
    C((Ω ≃ₐ[K] Ω), topRep (K := K) (Ω := Ω) p) :=
  ⟨fun σ => ULift.up (coefficientMap p (Additive.ofMul (f.1 σ))),
    (ContinuousLinearEquiv.ulift : ULift.{v} ℚ_[p] ≃L[ℚ_[p]] ℚ_[p]).symm.continuous.comp
      ((continuous_coefficientMap p).comp (continuous_ofMul.comp f.1.continuous))⟩

theorem cocycle_law (f : continuousCocycles (K := K) (Ω := Ω) p) (σ τ : Ω ≃ₐ[K] Ω) :
    cocycle p f (σ * τ) = (topRep p).ρ σ (cocycle p f τ) + cocycle p f σ := by
  apply ULift.ext
  change coefficientMap p (Additive.ofMul (f.1 (σ * τ))) =
    representation p σ (coefficientMap p (Additive.ofMul (f.1 τ))) +
      coefficientMap p (Additive.ofMul (f.1 σ))
  calc
    _ = coefficientMap p (padicTateRepresentation p σ (Additive.ofMul (f.1 τ)) +
        Additive.ofMul (f.1 σ)) :=
      congrArg (coefficientMap (Ω := Ω) p) (congrArg Additive.ofMul (f.2 σ τ))
    _ = _ := by rw [map_add, coefficientMap_equivariant]

def classOfCocycle (f : continuousCocycles (K := K) (Ω := Ω) p) :
    continuousCohomology 1 (topRep (K := K) (Ω := Ω) p) :=
  ContinuousH1Homogeneous.classOf _ (cocycle p f) (cocycle_law p f)

theorem classOfCocycle_eq (f g : continuousCocycles (K := K) (Ω := Ω) p)
    (hfg : groupCohomology.IsMulCoboundary₁ (fun σ => g.1 σ / f.1 σ)) :
    classOfCocycle p f = classOfCocycle p g := by
  obtain ⟨t, ht⟩ := hfg
  apply ContinuousH1Homogeneous.classOf_eq_of_coboundary _ _ _
    (cocycle_law p f) (cocycle_law p g) (ULift.up (coefficientMap p (Additive.ofMul t)))
  · change Continuous (fun σ : Ω ≃ₐ[K] Ω =>
      ULift.up (coefficientMap p (Additive.ofMul t) * (Cyclotomic.coefficient p σ : ℚ_[p])))
    have hc : Continuous (fun σ : Ω ≃ₐ[K] Ω => (Cyclotomic.coefficient p σ : ℚ_[p])) :=
      continuous_subtype_val.comp (Cyclotomic.continuous_coefficient (K := K) (Ω := Ω) p)
    exact continuous_uliftUp.comp (continuous_const.mul hc)
  · intro σ
    apply ULift.ext
    have h : Additive.ofMul (g.1 σ) - Additive.ofMul (f.1 σ) =
        padicTateRepresentation p σ (Additive.ofMul t) - Additive.ofMul t :=
      congrArg Additive.ofMul (ht σ).symm
    change coefficientMap p (Additive.ofMul (g.1 σ)) - coefficientMap p (Additive.ofMul (f.1 σ)) =
      representation p σ (coefficientMap p (Additive.ofMul t)) - coefficientMap p (Additive.ofMul t)
    calc
      _ = coefficientMap p (Additive.ofMul (g.1 σ) - Additive.ofMul (f.1 σ)) :=
        (map_sub (coefficientMap p) _ _).symm
      _ = coefficientMap p (padicTateRepresentation p σ (Additive.ofMul t) - Additive.ofMul t) :=
        congrArg (coefficientMap (Ω := Ω) p) h
      _ = _ := by rw [map_sub, coefficientMap_equivariant]

def toH1 : continuousH1 (K := K) (Ω := Ω) p →
    continuousCohomology 1 (topRep (K := K) (Ω := Ω) p) :=
  Quotient.lift (classOfCocycle p) (fun f g h => classOfCocycle_eq p f g h)

theorem toH1_class (f : continuousCocycles (K := K) (Ω := Ω) p) :
    toH1 p (continuousH1Class f) = classOfCocycle p f := rfl

end
end JoshiTeich.Act1Scene1.LocalKummer.Rational
