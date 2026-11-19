import Solutions.Source_ReferenceIutConcreteThetaRegion
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField
open scoped BigOperators Pointwise

universe u v

noncomputable section

private theorem iUnion_image_singleton_id {A : Type*} (U : Set A) :
    (⋃ f ∈ ({id} : Set (A → A)), f '' U) = U := by
  ext x
  constructor
  · intro hx
    obtain ⟨f, hf, y, hy, rfl⟩ := Set.mem_iUnion₂.mp hx
    have h := Set.mem_singleton_iff.mp hf
    subst f
    exact hy
  · intro hx
    exact Set.mem_iUnion₂.mpr ⟨id, Set.mem_singleton _, x, hx, rfl⟩

namespace LocalTheory

variable {K : Type u} [Field K] [NumberField K] (LT : LocalTheory.{u, v} K)

private def radialBall {ι : Type} [Fintype ι] (r : ℝ) (c : ι → Place K) :
    Set (LT.Tensor .infinite c) :=
  algebraMap ℝ (LT.Tensor .infinite c) r • LT.integral .infinite c

private lemma radialBall_admissible {ι : Type} [Fintype ι] (r : ℝ) (hr : 0 < r)
    (c : ι → Place K) : LT.radialBall r c ∈ LT.admissible .infinite c :=
  LT.smul_integral_admissible .infinite c _
    ((isUnit_iff_ne_zero.mpr hr.ne').map (algebraMap ℝ (LT.Tensor .infinite c)))

private def radialLogShell (r : ℝ) {ι : Type} [Fintype ι] :
    ∀ (q : RationalPlace) (c : ι → Place K), Set (LT.Tensor q c)
  | .finite p, c => LT.logShell (.finite p) c
  | .infinite, c => LT.radialBall r c

private def radialIndAut {ι : Type} [Fintype ι] :
    ∀ (q : RationalPlace) (c : ι → Place K), Set (LT.Tensor q c → LT.Tensor q c)
  | .finite p, c => LT.indAut (.finite p) c
  | .infinite, _ => {id}

/-- The local theory with archimedean log-shell a radial ball of radius `r`. -/
def withArchimedeanRadius (r : ℝ) (hr : 0 < r) (hr₁ : r ≤ 1) : LocalTheory.{u, v} K :=
  { LT with
    logShell := LT.radialLogShell r
    logShell_relCompact := by
      intro ι _ q c
      cases q with
      | finite p => exact LT.logShell_relCompact (.finite p) c
      | infinite =>
        exact LT.admissible_relCompact .infinite c _ (LT.radialBall_admissible r hr c)
    integral_subset_logShell := LT.integral_subset_logShell
    logShell_eq_integral := LT.logShell_eq_integral
    indAut := LT.radialIndAut
    id_mem_indAut := by
      intro ι _ q c
      cases q with
      | finite p => exact LT.id_mem_indAut (.finite p) c
      | infinite => exact Set.mem_singleton _
    indAut_logShell := by
      intro ι _ q c f hf
      cases q with
      | finite p => exact LT.indAut_logShell (.finite p) c f hf
      | infinite =>
        change f ∈ ({id} : Set (LT.Tensor .infinite c → LT.Tensor .infinite c)) at hf
        have h := Set.mem_singleton_iff.mp hf
        subst f
        change id '' LT.radialBall r c ⊆ LT.radialBall r c
        rw [Set.image_id]
    theta_admissible := by
      intro ι _ q c s hs
      cases q with
      | finite p => exact LT.theta_admissible (.finite p) c s hs
      | infinite =>
        change (⋃ f ∈ ({id} : Set (LT.Tensor .infinite c → LT.Tensor .infinite c)),
          f '' (s • LT.integral .infinite c)) ∈ LT.admissible .infinite c
        rw [iUnion_image_singleton_id]
        exact LT.smul_integral_admissible .infinite c s hs
    thetaShell_admissible := by
      intro ι _ q c
      cases q with
      | finite p => exact LT.thetaShell_admissible (.finite p) c
      | infinite =>
        change (⋃ f ∈ ({id} : Set (LT.Tensor .infinite c → LT.Tensor .infinite c)),
          f '' LT.radialBall r c) ∈ LT.admissible .infinite c
        rw [iUnion_image_singleton_id]
        exact LT.radialBall_admissible r hr c
    prop14_iii := LT.prop14_iii
    prop14_iv := LT.prop14_iv
    prop15 := by
      intro ι _ c f hf
      change f ∈ ({id} : Set (LT.Tensor .infinite c → LT.Tensor .infinite c)) at hf
      have h := Set.mem_singleton_iff.mp hf
      subst f
      change id '' LT.radialBall r c ⊆ LT.radialBall (Real.pi ^ Fintype.card ι) c
      rw [Set.image_id]
      have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
      exact LT.smul_integral_infinite_mono c r _ hr (hr₁.trans (one_le_pow₀ hpi))
  }

end LocalTheory

namespace ThetaLocalData

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}
variable (TL : ThetaLocalData D LT) (r : ℝ) (hr : 0 < r) (hr₁ : r ≤ 1)

/-- The q-root data on the local theory with the radial archimedean log-shell. -/
def withArchimedeanRadius : ThetaLocalData D (LT.withArchimedeanRadius r hr hr₁) where
  badChars := TL.badChars
  qroot := TL.qroot
  qroot_ne_zero := TL.qroot_ne_zero
  ordp_qroot_nonneg := TL.ordp_qroot_nonneg
  qroot_eq_one := TL.qroot_eq_one
  embedF := TL.embedF
  qroot_pow := TL.qroot_pow
  ordp_qroot := TL.ordp_qroot
  residueChar_mem := TL.residueChar_mem
  bad_residueChar_mem := TL.bad_residueChar_mem
  badChars_prime := TL.badChars_prime
  sum_weight_ordp_qroot p bad hbad := by
    let T := LT.withArchimedeanRadius r hr hr₁
    let e := (T.fiberFiniteEquiv p).trans (LT.fiberFiniteEquiv p).symm
    let f (w : T.Fiber (.finite p)) : ℝ :=
      T.weight (.finite p) w * ordp D.Kt (T.fiberPlace w) (TL.qroot (T.fiberPlace w))
    let g (w : LT.Fiber (.finite p)) : ℝ :=
      LT.weight (.finite p) w * ordp D.Kt (LT.fiberPlace w) (TL.qroot (LT.fiberPlace w))
    have hweight (A : LocalTheory.{u, v} D.Kt) (w : A.Fiber (.finite p)) :
        A.weight (.finite p) w = placeWeight D.Kt (A.fiberPlace w) := by
      simp only [LocalTheory.weight, A.fiberPlace_spec w]
      rfl
    have hsum : (∑ w ∈ @Finset.univ _ (T.fiberFintype (.finite p)), f w) =
        ∑ w ∈ @Finset.univ _ (LT.fiberFintype (.finite p)), g w := by
      refine Finset.sum_equiv e (fun _ => by simp only [Finset.mem_univ]) ?_
      intro w _
      have hplace : LT.fiberPlace (e w) = T.fiberPlace w :=
        congrArg Subtype.val ((LT.fiberFiniteEquiv p).apply_symm_apply (T.fiberFiniteEquiv p w))
      dsimp only [f, g]
      rw [hweight T w, hweight LT (e w), hplace]
    exact hsum.trans (TL.sum_weight_ordp_qroot p bad hbad)

private lemma sum_prod_tuple_eq_one {ι A : Type*} [Fintype ι] [Fintype A]
    (w : A → ℝ) (hw : ∑ a, w a = 1) [inst : Fintype (ι → A)] :
    ∑ c : ι → A, ∏ j, w (c j) = 1 := by
  classical
  rw [Subsingleton.elim inst Pi.instFintype, ← Fintype.prod_sum (fun _ : ι => w), hw]
  simp

private lemma sum_univ_eq {C : Type*} (f : C → ℝ) (F G : Fintype C) :
    Finset.sum (@Finset.univ C F) f = Finset.sum (@Finset.univ C G) f :=
  congrArg (fun inst : Fintype C => Finset.sum (@Finset.univ C inst) f) (Subsingleton.elim F G)

private lemma sum_tuple_weights (R : RHSData.{u, v} D) (i : Fin R.container.proc.length)
    (q : RationalPlace) :
    (∑ c : R.container.Components i q, ∏ j, R.vol.weight q (c j)) = 1 :=
  @sum_prod_tuple_eq_one (R.container.proc.capsule i).LabelType (R.container.Fiber q)
    inferInstance inferInstance (R.vol.weight q) (R.vol.weight_sum_one q)
    (inferInstanceAs (Fintype (R.container.Components i q)))

private theorem packetVol_infinite_withArchimedeanRadius (i : Fin ((D.ℓ - 1) / 2)) :
    let R := (TL.withArchimedeanRadius r hr hr₁).rhsData
    R.vol.packetVol i .infinite ((R.thetaHull i).region .infinite) = Real.log r := by
  let n := (D.ℓ - 1) / 2
  let T := LT.withArchimedeanRadius r hr hr₁
  let TLr := TL.withArchimedeanRadius r hr hr₁
  let R := TLr.rhsData
  let capsule : Fin R.container.proc.length := i
  let labels := ((Procession.standard n).capsule i).LabelType
  let ball (c : R.container.Components capsule .infinite) := T.radialBall r (T.tuple .infinite c)
  have hcomp (c : R.container.Components capsule .infinite) :
      TLr.thetaComponent n i .infinite c = ball c := iUnion_image_singleton_id _
  have hPilot : (R.thetaPilot capsule).region .infinite =
      (R.container.packet capsule .infinite).productRegion ball := by
    change (R.container.packet capsule .infinite).productRegion
      (fun c => TLr.thetaComponent n i .infinite c) = _
    rw [funext hcomp]
  have hmem : (R.thetaPilot capsule).region .infinite ∈
      (R.hull.system capsule .infinite).HullRegions := by
    change (R.thetaPilot capsule).region .infinite ∈ T.hullRegions labels .infinite
    exact ⟨fun _ => r, fun _ => hr, hPilot⟩
  have hHull : (R.thetaHull capsule).region .infinite = (R.thetaPilot capsule).region .infinite :=
    (R.hull.system capsule .infinite).hull_eq_self
      (R.thetaPilot_hullAdmissible capsule .infinite) hmem
  have hnonempty (c : R.container.Components capsule .infinite) : (ball c).Nonempty :=
    T.admissible_nonempty .infinite _ _ (T.radialBall_admissible r hr _)
  have hvol (c : R.container.Components capsule .infinite) :
      R.vol.componentVol capsule .infinite c (ball c) = Real.log r :=
    T.componentVol_arch_scale _ r hr
  change R.vol.packetVol capsule .infinite ((R.thetaHull capsule).region .infinite) = Real.log r
  calc
    _ = R.vol.packetVol capsule .infinite ((R.container.packet capsule .infinite).productRegion ball) :=
      congrArg (R.vol.packetVol capsule .infinite) (hHull.trans hPilot)
    _ = ∑ c : R.container.Components capsule .infinite,
        (∏ j, R.vol.weight .infinite (c j)) * R.vol.componentVol capsule .infinite c (ball c) :=
      R.vol.packetVol_product capsule .infinite ball hnonempty
    _ = (∑ c : R.container.Components capsule .infinite,
        ∏ j, R.vol.weight .infinite (c j)) * Real.log r := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => congrArg ((∏ j, R.vol.weight .infinite (c j)) * ·) (hvol c)
    _ = _ := (congrArg (· * Real.log r) (sum_tuple_weights R capsule .infinite)).trans (one_mul _)

private theorem packetVol_finite_withArchimedeanRadius (i : Fin ((D.ℓ - 1) / 2))
    (p : Nat.Primes) :
    let R := (TL.withArchimedeanRadius r hr hr₁).rhsData
    R.vol.packetVol i (.finite p) ((R.thetaHull i).region (.finite p)) =
      TL.rhsData.vol.packetVol i (.finite p) ((TL.rhsData.thetaHull i).region (.finite p)) := by
  let n := (D.ℓ - 1) / 2
  let q := RationalPlace.finite p
  let T := LT.withArchimedeanRadius r hr hr₁
  let TLr := TL.withArchimedeanRadius r hr hr₁
  let R := TLr.rhsData
  let R₀ := TL.rhsData
  let capsule : Fin R.container.proc.length := i
  let oldCapsule : Fin R₀.container.proc.length := i
  let labels := ((Procession.standard n).capsule i).LabelType
  let U := (R.thetaPilot capsule).region q
  let U₀ := (R₀.thetaPilot oldCapsule).region q
  let H := R.hull.system capsule q
  let H₀ := R₀.hull.system oldCapsule q
  have hComponent (c : labels → LT.Fiber q) :
      TLr.thetaComponent n i q c = TL.thetaComponent n i q c := by
    let j := distinguished n i
    let scale (w : {w : FinitePlace D.Kt // LT.tuple q c j = Place.finite w}) :
        LT.Tensor q (LT.tuple q c) :=
      LT.incl p (LT.tuple q c) j w.1 w.2 (TL.qroot w.1 ^ (i.1 + 1) ^ 2)
    have hw : T.fiberPlace (p := p) (c j) = LT.fiberPlace (p := p) (c j) :=
      Sum.inl.inj ((T.fiberPlace_spec (p := p) (c j)).symm.trans
        (LT.fiberPlace_spec (p := p) (c j)))
    have hScale : TLr.scaleElt n i p c = TL.scaleElt n i p c := by
      let w₁ : {w : FinitePlace D.Kt // LT.tuple q c j = Place.finite w} :=
        ⟨T.fiberPlace (c j), T.fiberPlace_spec (c j)⟩
      let w₀ : {w : FinitePlace D.Kt // LT.tuple q c j = Place.finite w} :=
        ⟨LT.fiberPlace (c j), LT.fiberPlace_spec (c j)⟩
      change scale w₁ = scale w₀
      exact congrArg scale (Subtype.ext hw)
    exact congrArg (fun s : LT.Tensor q (LT.tuple q c) =>
      ⋃ φ ∈ LT.indAut q (LT.tuple q c), φ '' (s • LT.integral q (LT.tuple q c))) hScale
  have hPilot : U = U₀ := by
    change (LT.packet labels q).productRegion (fun c => TLr.thetaComponent n i q c) =
      (LT.packet labels q).productRegion (fun c => TL.thetaComponent n i q c)
    exact congrArg (LT.packet labels q).productRegion (funext hComponent)
  have hClass : H.HullRegions = H₀.HullRegions := rfl
  have hLeast := H.isLeastHullRegion_hull U (R.thetaPilot_hullAdmissible capsule q)
  have hOldLeast := H₀.isLeastHullRegion_hull U₀ (R₀.thetaPilot_hullAdmissible oldCapsule q)
  have hHull : (R.thetaHull capsule).region q = (R₀.thetaHull oldCapsule).region q := by
    change H.hull U = H₀.hull U₀
    exact Set.Subset.antisymm
      (hLeast.2.2 _ (hClass.symm ▸ hOldLeast.1) (fun _ hx => hOldLeast.2.1 (hPilot ▸ hx)))
      (hOldLeast.2.2 _ (hClass ▸ hLeast.1) (fun _ hx => hLeast.2.1 (hPilot.symm ▸ hx)))
  have hPacketVol (V : Set (LT.packet labels q).Total) :
      R.vol.packetVol capsule q V = R₀.vol.packetVol oldCapsule q V := by
    let f (c : labels → LT.Fiber q) : ℝ :=
      LT.tupleWeight q c * LT.componentVol q (LT.tuple q c) (LT.proj q c V)
    exact sum_univ_eq f
      (LargeVolumeContainerData.instFintypeComponents R.container capsule q)
      (LargeVolumeContainerData.instFintypeComponents R₀.container oldCapsule q)
  change R.vol.packetVol capsule q ((R.thetaHull capsule).region q) =
    R₀.vol.packetVol oldCapsule q ((R₀.thetaHull oldCapsule).region q)
  exact (congrArg (R.vol.packetVol capsule q) hHull).trans (hPacketVol _)

private theorem globalVol_withArchimedeanRadius (i : Fin ((D.ℓ - 1) / 2)) :
    let R := (TL.withArchimedeanRadius r hr hr₁).rhsData
    let R₁ := (TL.withArchimedeanRadius 1 one_pos le_rfl).rhsData
    R.vol.globalVol (R.thetaHull i) = R₁.vol.globalVol (R₁.thetaHull i) + Real.log r := by
  let R := (TL.withArchimedeanRadius r hr hr₁).rhsData
  let R₁ := (TL.withArchimedeanRadius 1 one_pos le_rfl).rhsData
  let capsule : Fin R.container.proc.length := i
  let unitCapsule : Fin R₁.container.proc.length := i
  let f (q : RationalPlace) := R₁.vol.packetVol unitCapsule q ((R₁.thetaHull unitCapsule).region q)
  let g (q : RationalPlace) := if q = .infinite then Real.log r else 0
  let support : Finset RationalPlace := {.infinite}
  have hf : (Function.support f).Finite := by
    refine (R₁.thetaHull unitCapsule).finiteSupport.subset fun q hq heq => hq ?_
    exact (congrArg (R₁.vol.packetVol unitCapsule q) heq).trans
      (R₁.vol.packetVol_integral unitCapsule q)
  have hg : Function.support g ⊆ ↑support := by
    intro q hq
    by_contra hmem
    have hne : q ≠ .infinite := by simpa [support] using hmem
    exact hq (if_neg hne)
  change (∑ᶠ q, R.vol.packetVol capsule q ((R.thetaHull capsule).region q)) =
    (∑ᶠ q, f q) + Real.log r
  calc
    _ = ∑ᶠ q, (f q + g q) := by
      refine finsum_congr fun q => ?_
      cases q with
      | finite p =>
        change _ = R₁.vol.packetVol unitCapsule (.finite p)
          ((R₁.thetaHull unitCapsule).region (.finite p)) + g (.finite p)
        rw [show g (.finite p) = 0 by simp [g], add_zero]
        exact (TL.packetVol_finite_withArchimedeanRadius r hr hr₁ i p).trans
          (TL.packetVol_finite_withArchimedeanRadius 1 one_pos le_rfl i p).symm
      | infinite =>
        change _ = R₁.vol.packetVol unitCapsule .infinite
          ((R₁.thetaHull unitCapsule).region .infinite) + g .infinite
        calc
          _ = Real.log r := TL.packetVol_infinite_withArchimedeanRadius r hr hr₁ i
          _ = _ := by
            have hunit : R₁.vol.packetVol unitCapsule .infinite
                ((R₁.thetaHull unitCapsule).region .infinite) = Real.log 1 :=
              TL.packetVol_infinite_withArchimedeanRadius 1 one_pos le_rfl i
            rw [hunit, Real.log_one, zero_add]
            simp [g]
    _ = _ := by
      rw [finsum_add_distrib hf (support.finite_toSet.subset hg),
        finsum_eq_sum_of_support_subset g hg]
      simp [g, support]

/-- The right-hand side varies by `log r` relative to the unit-radius archimedean shell. -/
theorem rhs_withArchimedeanRadius :
    (TL.withArchimedeanRadius r hr hr₁).rhsData.rhs =
      (TL.withArchimedeanRadius 1 one_pos le_rfl).rhsData.rhs + Real.log r := by
  let n := (D.ℓ - 1) / 2
  let R := (TL.withArchimedeanRadius r hr hr₁).rhsData
  let R₁ := (TL.withArchimedeanRadius 1 one_pos le_rfl).rhsData
  have hnNat : 0 < n := by
    have h5 : 5 ≤ D.ℓ := D.prime.five_le
    dsimp only [n]
    omega
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnNat.ne'
  let f (i : Fin n) : ℝ :=
    let capsule : Fin R.container.proc.length := i
    R.vol.globalVol (R.thetaHull capsule)
  let g (i : Fin n) : ℝ :=
    let capsule : Fin R₁.container.proc.length := i
    R₁.vol.globalVol (R₁.thetaHull capsule)
  change (∑ i : Fin n, f i) / (n : ℝ) = (∑ i : Fin n, g i) / (n : ℝ) + Real.log r
  have hglob (i : Fin n) : f i = g i + Real.log r := TL.globalVol_withArchimedeanRadius r hr hr₁ i
  simp_rw [hglob, Finset.sum_add_distrib]
  have hconst : (∑ _ : Fin n, Real.log r) = (n : ℝ) * Real.log r := by
    simp [nsmul_eq_mul]
  rw [hconst, add_div, mul_comm (n : ℝ) (Real.log r), mul_div_cancel_right₀ _ hn]

variable (QI : QPilotInputs D)

include TL in
/-- Any instance of the local inputs yields, on the same initial datum, an instance
where the concrete Corollary 3.12 inequality fails. -/
theorem exists_not_corollary312Variant :
    ∃ (T : LocalTheory.{u, v} D.Kt) (U : ThetaLocalData D T),
      ¬ Corollary312Variant (concreteVariantData D T U QI) := by
  let rhs₁ := (TL.withArchimedeanRadius 1 one_pos le_rfl).rhsData.rhs
  let y := min 0 (QI.qPilot.lhs - rhs₁ - 1)
  let r := Real.exp y
  have hr : 0 < r := Real.exp_pos y
  have hr₁ : r ≤ 1 := Real.exp_le_one_iff.mpr (min_le_left _ _)
  refine ⟨LT.withArchimedeanRadius r hr hr₁, TL.withArchimedeanRadius r hr hr₁, ?_⟩
  change ¬ QI.qPilot.lhs ≤ (TL.withArchimedeanRadius r hr hr₁).rhsData.rhs
  rw [TL.rhs_withArchimedeanRadius r hr hr₁]
  change ¬ QI.qPilot.lhs ≤ rhs₁ + Real.log (Real.exp y)
  rw [Real.log_exp]
  exact not_le.mpr (by linarith [show y ≤ QI.qPilot.lhs - rhs₁ - 1 from min_le_right _ _])

include TL QI in
/-- An inhabited instance refutes the universal Corollary 3.12 premise over
`InitialThetaData`, `LocalTheory`, `ThetaLocalData`, and `QPilotInputs`. -/
theorem not_forall_corollary312Variant :
    ¬ (∀ (D' : InitialThetaData AG TG) (T : LocalTheory.{u, v} D'.Kt)
      (U : ThetaLocalData D' T) (Q : QPilotInputs D'),
      Corollary312Variant (concreteVariantData D' T U Q)) := by
  intro h312
  obtain ⟨T, U, hU⟩ := TL.exists_not_corollary312Variant QI
  exact hU (h312 D T U QI)

end ThetaLocalData
end
end AbcAdaptation.Reference.Iut
