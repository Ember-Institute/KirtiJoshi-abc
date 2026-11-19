import Solutions.Source_ReferenceIutConcreteLocalTheory
import Solutions.Source_ReferenceIutConcreteThetaRegion

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open scoped BigOperators Pointwise
open LocalConstruct

universe u

private theorem sum_product_weights {ι A : Type*} [Fintype ι] [Fintype A]
    (w : A → ℝ) (hw : ∑ a, w a = 1) [inst : Fintype (ι → A)] :
    (∑ c : ι → A, ∏ j, w (c j)) = 1 := by
  classical
  rw [Subsingleton.elim inst Pi.instFintype, ← Fintype.prod_sum (fun _ : ι => w), hw]
  simp

private theorem sum_packet_weights {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
    {D : InitialThetaData AG TG} (R : RHSData.{u, u} D)
    (i : Fin R.container.proc.length) (q : RationalPlace) :
    (∑ c : R.container.Components i q, ∏ j, R.vol.weight q (c j)) = 1 :=
  @sum_product_weights (R.container.proc.capsule i).LabelType (R.container.Fiber q)
    inferInstance inferInstance (R.vol.weight q) (R.vol.weight_sum_one q)
    (inferInstanceAs (Fintype (R.container.Components i q)))

/-- For the concrete local theory used in P7, each infinite packet of the theta hull
is the product of the log-shells. Its log-volume is the label count times `log π`. -/
theorem ThetaLocalData.packetVol_thetaHull_infinite
    {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG} {D : InitialThetaData AG TG}
    (TL : ThetaLocalData D (concreteLocalTheory (K := D.Kt))) (i : Fin ((D.ℓ - 1) / 2)) :
    let R := TL.rhsData
    R.vol.packetVol i .infinite ((R.thetaHull i).region .infinite) =
      (Fintype.card ((Procession.standard ((D.ℓ - 1) / 2)).capsule i).LabelType : ℝ) *
        Real.log Real.pi := by
  let LT := concreteLocalTheory (K := D.Kt)
  let R := TL.rhsData
  let capsule : Fin R.container.proc.length := i
  let labels := (R.container.proc.capsule capsule).LabelType
  let shell (c : R.container.Components capsule .infinite) :=
    archLogShell (LT.tuple .infinite c)
  have hcomponent (c : R.container.Components capsule .infinite) :
      TL.thetaComponent ((D.ℓ - 1) / 2) i .infinite c = shell c := by
    apply (TL.thetaComponent_subset_logShell _ i .infinite c).antisymm
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨id, LT.id_mem_indAut _ _, x, hx, rfl⟩
  have hPilot : (R.thetaPilot capsule).region .infinite =
      (R.container.packet capsule .infinite).productRegion shell := by
    change (R.container.packet capsule .infinite).productRegion
      (fun c => TL.thetaComponent _ i .infinite c) = _
    rw [funext hcomponent]
  have hmem : (R.thetaPilot capsule).region .infinite ∈
      (R.hull.system capsule .infinite).HullRegions := by
    change (R.thetaPilot capsule).region .infinite ∈ LT.hullRegions labels .infinite
    refine ⟨fun _ => Real.pi ^ Fintype.card labels, fun _ => pow_pos Real.pi_pos _, ?_⟩
    rw [hPilot]
    exact congrArg ((R.container.packet capsule .infinite).productRegion)
      (funext fun c => archLogShell_eq_smul_archIntegral (LT.tuple .infinite c))
  have hHull : (R.thetaHull capsule).region .infinite =
      (R.thetaPilot capsule).region .infinite :=
    (R.hull.system capsule .infinite).hull_eq_self
      (R.thetaPilot_hullAdmissible capsule .infinite) hmem
  have hnonempty (c : R.container.Components capsule .infinite) : (shell c).Nonempty :=
    LT.admissible_nonempty .infinite _ _ ((hcomponent c) ▸ TL.thetaComponent_admissible _ i .infinite c)
  have hvolume (c : R.container.Components capsule .infinite) :
      R.vol.componentVol capsule .infinite c (shell c) =
        (Fintype.card labels : ℝ) * Real.log Real.pi :=
    archComponentVol_archLogShell (LT.tuple .infinite c)
  change R.vol.packetVol capsule .infinite ((R.thetaHull capsule).region .infinite) =
    (Fintype.card labels : ℝ) * Real.log Real.pi
  rw [hHull, hPilot, R.vol.packetVol_product capsule .infinite shell hnonempty]
  simp only [hvolume, ← Finset.sum_mul, sum_packet_weights R capsule .infinite, one_mul]

end AbcAdaptation.Reference.Iut
