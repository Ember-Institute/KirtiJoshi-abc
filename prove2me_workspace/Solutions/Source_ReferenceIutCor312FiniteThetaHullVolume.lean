import Solutions.Source_ReferenceIutConcreteLocalFinitePrincipalVolume
import Solutions.Source_ReferenceIutConcreteLocalTheory
import Solutions.Source_ReferenceIutConcreteLocalEstimate

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField
open scoped BigOperators Pointwise
open JoshiTeich.Act1Scene1.IutFiniteWeightedAveraging (sum_bound_eval)

universe u v

private theorem log_norm_pow_div_localDeg {K : Type*} [Field K] [NumberField K]
    (p : Nat.Primes) (w : FinitePlace K) (hp : residueChar w = (p : ℕ))
    (x : completionAt K w) (m : ℕ) :
    Real.log ‖x ^ m‖ / localDeg K w =
      -(m : ℝ) * ordp K w x * Real.log (p : ℕ) := by
  have hlog : Real.log (p : ℕ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  have hnorm :
      -ordp K w x * Real.log (p : ℕ) = Real.log ‖x‖ / localDeg K w := by
    rw [ordp, hp, neg_div, neg_neg, ← div_div, div_mul_cancel₀ _ hlog]
  calc
    _ = (m : ℝ) * (Real.log ‖x‖ / localDeg K w) := by
      rw [norm_pow, Real.log_pow, mul_div_assoc]
    _ = _ := by rw [← hnorm, ← mul_assoc, mul_neg, neg_mul (m : ℝ) (ordp K w x)]

private theorem sum_prod_tuple_mul_coord {ι E : Type*} [Fintype ι] [Fintype E]
    [Fintype (ι → E)] (weight : E → ℝ) (hweight : ∑ e, weight e = 1)
    (f : E → ℝ) (label : ι) :
    ∑ c : ι → E, (∏ j, weight (c j)) * f (c label) = ∑ e, weight e * f e := by
  have h := sum_bound_eval weight hweight (fun e => 1 - f e) (fun _ => 0) 1 1 0 label
  simp only [Finset.sum_const_zero, add_zero, mul_one, mul_zero, neg_mul, one_mul,
    neg_sub, sub_add_cancel] at h
  simp_rw [mul_sub, mul_one] at h
  simpa only [Finset.sum_sub_distrib, hweight, neg_sub, sub_add_cancel] using h

private theorem sum_weighted_log_degree {E : Type*} [Fintype E] (weight order : E → ℝ)
    (J L d q : ℝ) (hd : d ≠ 0) (hq : q = d * L * ∑ v, weight v * order v) :
    (∑ v, weight v * (-J * order v * L)) = -J * (q / d) := by
  rw [hq, mul_assoc d L, mul_div_cancel_left₀ _ hd, ← mul_assoc (-J) L,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

-- State the bridge once at an arbitrary tuple, before specializing to the torsion field.
private def HasFinitePrincipalLogVolume {K : Type u} [Field K] [NumberField K]
    (LT : LocalTheory.{u, v} K) : Prop :=
  ∀ {ι : Type} [Fintype ι] (p : Nat.Primes) (t : ι → Place K),
    (∀ j, LocalConstruct.IsOver K p (t j)) →
    ∀ (label : ι) (w : FinitePlace K) (hw : t label = Place.finite w)
      (x : completionAt K w), x ≠ 0 →
      LT.componentVol (.finite p) t
        (LT.incl p t label w hw x • LT.integral (.finite p) t) =
        Real.log ‖x‖ / localDeg K w

private theorem concreteLocalTheory_hasFinitePrincipalLogVolume
    {K : Type u} [field : Field K] [numberField : NumberField K] :
    HasFinitePrincipalLogVolume (LocalConstruct.concreteLocalTheory (K := K)) := by
  intro ι inst p t ht label w hw x hx
  exact @LocalConstruct.finiteComponentVol_incl_smul_integral K field numberField
    ι inst p t ht label w hw x hx

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

private noncomputable abbrev concreteTheory (D : InitialThetaData AG TG) :
    LocalTheory.{u, u} D.Kt :=
  LocalConstruct.concreteLocalTheory (K := D.Kt)

variable {D : InitialThetaData AG TG}

local notation "𝓛" => concreteTheory D

/-- The finite theta component is the principal region scaled by the
distinguished q-root power. -/
theorem thetaComponent_finite_eq_scaled (TL : ThetaLocalData D 𝓛)
    (n : ℕ) (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → (𝓛).Fiber (.finite p)) :
    TL.thetaComponent n i (.finite p) c = (𝓛).scaled (.finite p) c (TL.scaleElt n i p c) := by
  let label := distinguished n i
  let w := (𝓛).fiberPlace (c label)
  let x : completionAt D.Kt w := TL.qroot w ^ ((i.1 + 1) ^ 2)
  have hw : (𝓛).tuple (.finite p) c label = Place.finite w :=
    (𝓛).fiberPlace_spec (c label)
  have hx : x ≠ 0 := pow_ne_zero _ (TL.qroot_ne_zero w)
  exact LocalConstruct.finiteIndAut_iUnion_incl_smul_integral p ((𝓛).tuple (.finite p) c)
    ((𝓛).tuple_isOver p c) label w hw x hx

private abbrev FiniteThetaHullIsScaled {LT : LocalTheory.{u, v} D.Kt}
    (T : ThetaLocalData D LT) (i : Fin ((D.ℓ - 1) / 2)) (p : Nat.Primes) : Prop :=
    let R : RHSData.{u, v} D := T.rhsData
    (R.thetaHull i).region (.finite p) =
      (R.container.packet i (.finite p)).scaledIntegral (T.scaleElt _ i p)

private theorem thetaHull_region_finite_of_component_eq {LT : LocalTheory.{u, v} D.Kt}
    (T : ThetaLocalData D LT) (i : Fin ((D.ℓ - 1) / 2)) (p : Nat.Primes)
    (hcomponent : ∀ c : TowerArithmetic.Lab (D := D) i → LT.Fiber (.finite p),
      T.thetaComponent _ i (.finite p) c = LT.scaled (.finite p) c (T.scaleElt _ i p c)) :
    FiniteThetaHullIsScaled (LT := LT) T i p := by
  let R : RHSData.{u, v} D := T.rhsData
  let capsule : Fin R.container.proc.length := i
  let q := RationalPlace.finite p
  let packet := LT.packet (TowerArithmetic.Lab (D := D) i) q
  let a : packet.Total := T.scaleElt _ i p
  have hpilot : (R.thetaPilot capsule).region q = packet.scaledIntegral a := by
    change packet.productRegion (fun c => T.thetaComponent _ i q c) =
      packet.productRegion (fun c => LT.scaled q c (T.scaleElt _ i p c))
    exact congrArg packet.productRegion (funext hcomponent)
  have hscaled : packet.scaledIntegral a ∈ (R.hull.system capsule q).HullRegions := by
    change packet.IsHullRegion (packet.scaledIntegral a)
    exact ⟨a, T.isUnit_scaleElt _ i p, rfl⟩
  have hmem : (R.thetaPilot capsule).region q ∈ (R.hull.system capsule q).HullRegions :=
    hpilot.symm ▸ hscaled
  change (R.hull.system capsule q).hull ((R.thetaPilot capsule).region q) =
    packet.scaledIntegral a
  exact ((R.hull.system capsule q).hull_eq_self
    (R.thetaPilot_hullAdmissible capsule q) hmem).trans hpilot

/-- The holomorphic hull fixes the product of the finite principal regions. -/
theorem thetaHull_region_finite (TL : ThetaLocalData D 𝓛)
    (i : Fin ((D.ℓ - 1) / 2)) (p : Nat.Primes) :
    FiniteThetaHullIsScaled (LT := 𝓛) TL i p :=
  thetaHull_region_finite_of_component_eq TL i p (thetaComponent_finite_eq_scaled TL _ i p)

private theorem packetVol_thetaHull_finite_eq_sum {LT : LocalTheory.{u, v} D.Kt}
    (T : ThetaLocalData D LT) (i : Fin ((D.ℓ - 1) / 2)) (p : Nat.Primes)
    (hhull : FiniteThetaHullIsScaled (LT := LT) T i p) :
    let R : RHSData.{u, v} D := T.rhsData
    R.vol.packetVol i (.finite p) ((R.thetaHull i).region (.finite p)) =
      ∑ c : TowerArithmetic.Lab (D := D) i → LT.Fiber (.finite p),
        (∏ j, LT.weight (.finite p) (c j)) *
          LT.componentVol (.finite p) (LT.tuple (.finite p) c)
            (LT.scaled (.finite p) c (T.scaleElt _ i p c)) := by
  let R : RHSData.{u, v} D := T.rhsData
  let capsule : Fin R.container.proc.length := i
  let q := RationalPlace.finite p
  let a : (LT.packet (TowerArithmetic.Lab (D := D) i) q).Total := T.scaleElt _ i p
  calc
    _ = R.vol.packetVol capsule q ((R.container.packet capsule q).scaledIntegral a) :=
      congrArg (R.vol.packetVol capsule q) hhull
    _ = _ := TowerArithmetic.packetVol_scaledIntegral' (D := D) (LT := LT) i q a

private theorem componentVol_finite_scaled_of_principal
    {LT : LocalTheory.{u, v} D.Kt} (T : ThetaLocalData D LT)
    (hvolume : HasFinitePrincipalLogVolume LT) (n : ℕ) (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber (.finite p)) :
    let w := LT.fiberPlace (c (distinguished n i))
    LT.componentVol (.finite p) (LT.tuple (.finite p) c)
        (LT.scaled (.finite p) c (T.scaleElt n i p c)) =
      -(((i.1 + 1 : ℕ) : ℝ) ^ 2) * ordp D.Kt w (T.qroot w) * Real.log (p : ℕ) := by
  let label := distinguished n i
  let t := LT.tuple (.finite p) c
  let w := LT.fiberPlace (c label)
  let x : completionAt D.Kt w := T.qroot w ^ ((i.1 + 1) ^ 2)
  have hw : t label = Place.finite w := LT.fiberPlace_spec (c label)
  have ht : ∀ j, LocalConstruct.IsOver D.Kt p (t j) := LT.tuple_isOver p c
  have hx : x ≠ 0 := pow_ne_zero _ (T.qroot_ne_zero w)
  have hnorm : LT.componentVol (.finite p) t
      (LT.scaled (.finite p) c (T.scaleElt n i p c)) =
        Real.log ‖x‖ / localDeg D.Kt w :=
    @hvolume _ inferInstance p t ht label w hw x hx
  have hp : residueChar w = (p : ℕ) := LT.residueChar_fiberPlace (c label)
  let j : ℕ := i.1 + 1
  let order : ℝ := ordp D.Kt w (T.qroot w)
  let logP : ℝ := Real.log (p : ℕ)
  have horder : Real.log ‖x‖ / localDeg D.Kt w =
      -(((j ^ 2 : ℕ) : ℝ)) * order * logP :=
    log_norm_pow_div_localDeg (K := D.Kt) p w hp (T.qroot w) (j ^ 2)
  have hcast : ((j ^ 2 : ℕ) : ℝ) = (j : ℝ) ^ 2 := Nat.cast_pow j 2
  exact hnorm.trans (horder.trans (congrArg (fun z : ℝ => -z * order * logP) hcast))

private abbrev FiniteThetaHullPacketVolume {LT : LocalTheory.{u, v} D.Kt}
    (T : ThetaLocalData D LT) (QI : QPilotInputs D)
    (i : Fin ((D.ℓ - 1) / 2)) (p : Nat.Primes) : Prop :=
    let R : RHSData.{u, v} D := T.rhsData
    R.vol.packetVol i (.finite p) ((R.thetaHull i).region (.finite p)) =
      -(((i.1 + 1 : ℕ) : ℝ) ^ 2) *
        ((concreteVariantData D LT T QI).logQAt p / (2 * (D.ℓ : ℝ)))

private theorem packetVol_finite_thetaHull_of_principal_volume
    {LT : LocalTheory.{u, v} D.Kt} (T : ThetaLocalData D LT) (QI : QPilotInputs D)
    (i : Fin ((D.ℓ - 1) / 2)) (p : Nat.Primes)
    (hhull : FiniteThetaHullIsScaled (LT := LT) T i p)
    (hvolume : HasFinitePrincipalLogVolume LT) :
    FiniteThetaHullPacketVolume (LT := LT) T QI i p := by
  let q := RationalPlace.finite p
  let label : TowerArithmetic.Lab (D := D) i := distinguished _ i
  let weight (w : LT.Fiber q) : ℝ := LT.weight q w
  let order (w : LT.Fiber q) : ℝ := ordp D.Kt (LT.fiberPlace w) (T.qroot (LT.fiberPlace w))
  let J : ℝ := ((i.1 + 1 : ℕ) : ℝ) ^ 2
  let L : ℝ := Real.log (p : ℕ)
  let d : ℝ := 2 * (D.ℓ : ℝ)
  let logQ : ℝ := (concreteVariantData D LT T QI).logQAt p
  let f (w : LT.Fiber q) : ℝ := -J * order w * L
  let vol (c : TowerArithmetic.Lab (D := D) i → LT.Fiber q) : ℝ :=
    LT.componentVol q (LT.tuple q c) (LT.scaled q c (T.scaleElt _ i p c))
  have hpoint (c : TowerArithmetic.Lab (D := D) i → LT.Fiber q) : vol c = f (c label) :=
    componentVol_finite_scaled_of_principal T hvolume _ i p c
  have hsum :
      (∑ c : TowerArithmetic.Lab (D := D) i → LT.Fiber q, (∏ j, weight (c j)) * vol c) =
        ∑ c : TowerArithmetic.Lab (D := D) i → LT.Fiber q, (∏ j, weight (c j)) * f (c label) :=
    Finset.sum_congr rfl fun c _ =>
      congrArg (fun z : ℝ => (∏ j, weight (c j)) * z) (hpoint c)
  have hweight : ∑ w : LT.Fiber q, weight w = 1 := LT.weight_sum_one q
  have havg :
      (∑ c : TowerArithmetic.Lab (D := D) i → LT.Fiber q, (∏ j, weight (c j)) * f (c label)) =
        ∑ w : LT.Fiber q, weight w * f w :=
    sum_prod_tuple_mul_coord (ι := TowerArithmetic.Lab (D := D) i) (E := LT.Fiber q)
      weight hweight f label
  have hℓNat : D.ℓ ≠ 0 := D.prime.ℓ_prime.ne_zero
  have hd : d ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hℓNat)
  have hq : logQ = d * L * ∑ w : LT.Fiber q, weight w * order w :=
    TowerArithmetic.logQAt_eq (LT := LT) (TL := T) (QI := QI) p
  have hscaled : (∑ w : LT.Fiber q, weight w * f w) = -J * (logQ / d) :=
    sum_weighted_log_degree weight order J L d logQ hd hq
  exact (packetVol_thetaHull_finite_eq_sum (LT := LT) T i p hhull).trans
    (hsum.trans (havg.trans hscaled))

/-- The finite theta hull has packet log-volume equal to the negative
q-pilot contribution divided by twice the prime and scaled by the label square. -/
theorem packetVol_finite_thetaHull (TL : ThetaLocalData D 𝓛) (QI : QPilotInputs D)
    (i : Fin ((D.ℓ - 1) / 2)) (p : Nat.Primes) :
    FiniteThetaHullPacketVolume (LT := 𝓛) TL QI i p := by
  have hullRegion : FiniteThetaHullIsScaled (LT := 𝓛) TL i p :=
    thetaHull_region_finite (AG := AG) (TG := TG) (D := D) TL i p
  have principalVolume : HasFinitePrincipalLogVolume 𝓛 :=
    concreteLocalTheory_hasFinitePrincipalLogVolume (K := D.Kt)
  exact packetVol_finite_thetaHull_of_principal_volume
    (AG := AG) (TG := TG) (D := D) (LT := 𝓛) TL QI i p hullRegion principalVolume

end AbcAdaptation.Reference.Iut.ThetaLocalData
