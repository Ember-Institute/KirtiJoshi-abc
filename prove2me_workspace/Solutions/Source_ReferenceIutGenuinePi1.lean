/-
Sources:
* lana-agents/pi1, ca7def953193f861a462aa0831eec8f0a31ff69f,
  Pi1/Orbicurve/GaloisPi1.lean (totallyDisconnectedSpace_of_isClosed, pi1).
* lana-agents/iut, 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8,
  Iut/Anabelian/Genuine/Theory.lean (pi1C, pi1MapC, isOpenEmbedding_pi1MapC)
  and Iut/Anabelian/GenuineEtale.lean (genuinePi1Cover and its properties).
The characteristic-zero branch uses the proved Scene1 inertia quotient. The
positive-characteristic branch uses the one-element group, as in the source.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineInertiaQuotient
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Model
import Mathlib.Algebra.Group.PUnit
import Mathlib.Topology.Algebra.ClopenNhdofOne

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open JoshiTeich.ReferenceIut.Anabelian (Orbicurve)
open JoshiTeich.ReferenceIut.Anabelian.Genuine
open scoped Classical Pointwise Topology

universe u

noncomputable section

private theorem quotient_totallyDisconnectedSpace {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, ?_⟩
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  by_contra hne
  have hg : g ∉ N := fun h => hne ((QuotientGroup.eq_one_iff g).mpr h)
  have hg' : g ∉ sInf {U : Subgroup G | IsOpen (U : Set G) ∧ N ≤ U} := by
    rw [← ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G) ⟨N, hN⟩]
    exact hg
  rw [Subgroup.mem_sInf] at hg'
  push Not at hg'
  obtain ⟨U, ⟨hUOpen, hNU⟩, hgU⟩ := hg'
  let V : Subgroup (G ⧸ N) := U.map (QuotientGroup.mk' N)
  have hVOpen : IsOpen (V : Set (G ⧸ N)) := by
    simp only [V, Subgroup.coe_map, QuotientGroup.coe_mk']
    exact QuotientGroup.isOpenMap_coe _ hUOpen
  have hVClopen : IsClopen (V : Set (G ⧸ N)) :=
    ⟨Subgroup.isClosed_of_isOpen V hVOpen, hVOpen⟩
  obtain ⟨v, hv, hvg⟩ :=
    hVClopen.connectedComponent_subset (show (1 : G ⧸ N) ∈ V from V.one_mem) hx
  apply hgU
  have hdiff : v⁻¹ * g ∈ N := by
    rw [← QuotientGroup.eq]
    exact hvg
  simpa using U.mul_mem hv (hNU hdiff)

/-- The actual characteristic-zero inertia quotient with its profinite topology. -/
def profiniteInertiaQuotient {k : Type u} [Field k] [CharZero k] (X : Orbicurve k) :
    ProfiniteGrp.{u} := by
  let H := Hgp X.E X.level X.M X.pm
  let N := inertiaKernel X.E X.level X.M X.pm
  haveI : CompactSpace H :=
    isCompact_iff_compactSpace.mp (isClosed_Hgp X.E X.level X.M X.pm).isCompact
  have hN : IsClosed (N : Set H) :=
    (isClosed_valuationInertiaSubgroup X.E).preimage continuous_subtype_val
  haveI : TotallyDisconnectedSpace (H ⧸ N) := quotient_totallyDisconnectedSpace N hN
  exact ProfiniteGrp.of (H ⧸ N)

private def profiniteInertiaCover {k : Type u} [Field k] [CharZero k] {X Y : Orbicurve k}
    (c : Orbicurve.Cover X Y) :
    { f : profiniteInertiaQuotient X →ₜ* profiniteInertiaQuotient Y //
      Topology.IsOpenEmbedding f } := by
  cases X with | @mk E hE ℓ M pm =>
  cases Y with | @mk E' hE' ℓ' M' pm' =>
  obtain ⟨h, n, hn, hmul, hM, hpm⟩ := c
  change E = E' at h
  subst h
  exact ⟨⟨inertiaQuotientMap E hn hmul hM hpm,
      inertiaQuotientMap_continuous E hn hmul hM hpm⟩,
    inertiaQuotientMap_isOpenEmbedding E hn hmul hM hpm⟩

private structure OrbicurvePi1 (k : Type u) [Field k] where
  group : Orbicurve k → ProfiniteGrp.{u}
  cover : {X Y : Orbicurve k} → Orbicurve.Cover X Y → (group X →ₜ* group Y)
  cover_isOpenEmbedding : ∀ {X Y : Orbicurve k} (c : Orbicurve.Cover X Y),
    Topology.IsOpenEmbedding (cover c)

private def orbicurvePi1 {k : Type u} [Field k] : OrbicurvePi1 k :=
  if hk : CharZero k then
    letI : CharZero k := hk
    { group := profiniteInertiaQuotient
      cover := fun c => (profiniteInertiaCover c).1
      cover_isOpenEmbedding := fun c => (profiniteInertiaCover c).2 }
  else
    let G := ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (PUnit : Type u))
    { group := fun _ => G
      cover := fun _ => ContinuousMonoidHom.id G
      cover_isOpenEmbedding := fun _ => Topology.IsOpenEmbedding.id }

/-- The étale fundamental group assigned to a model orbicurve. -/
def genuinePi1 {k : Type u} [Field k] (X : Orbicurve k) : ProfiniteGrp.{u} :=
  (orbicurvePi1 (k := k)).group X

/-- The homomorphism of the specified fundamental groups induced by a model cover. -/
def genuinePi1Cover {k : Type u} [Field k] {X Y : Orbicurve k} (c : Orbicurve.Cover X Y) :
    genuinePi1 X →* genuinePi1 Y :=
  ((orbicurvePi1 (k := k)).cover c).toMonoidHom

theorem genuinePi1Cover_continuous {k : Type u} [Field k] {X Y : Orbicurve k}
    (c : Orbicurve.Cover X Y) : Continuous (genuinePi1Cover c) :=
  ((orbicurvePi1 (k := k)).cover c).continuous_toFun

theorem genuinePi1Cover_isOpenEmbedding {k : Type u} [Field k] {X Y : Orbicurve k}
    (c : Orbicurve.Cover X Y) : Topology.IsOpenEmbedding (genuinePi1Cover c) :=
  (orbicurvePi1 (k := k)).cover_isOpenEmbedding c

end

end AbcAdaptation.Reference.Iut.Anabelian
