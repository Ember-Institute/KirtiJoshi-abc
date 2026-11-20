/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original paths OrbicurveCores/S1/Defs.lean, lines 67–72, and
OrbicurveCores/S1/OrbLift.lean, lines 186–329.
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiOrbifoldLocalLift
import Solutions.Source_ReferenceIutCanLiftConvexCoveringLift
import Solutions.Source_ReferenceIutCanLiftCoveringSections
import Mathlib.Analysis.Complex.Convex

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

open Complex Filter Function Metric Set
open scoped Topology

/-- **Orbifold lifting** from the upper half-plane: a holomorphic `f` on `ℍ` whose local
ramification matches the signature of an orbifold covering `p` lifts through `p`. -/
def OrbLiftStatement : Prop :=
  ∀ (p f : ℂ → ℂ) (Y : Set ℂ) (e : ℂ → ℕ), (∀ w, 0 < e w) → IsOrbCover p Y e →
    DifferentiableOn ℂ f upper → (∀ z ∈ upper, HasLocalForm f z (e (f z))) →
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h upper ∧ MapsTo h upper Y ∧ ∀ z ∈ upper, p (h z) = f z

variable {p f : ℂ → ℂ} {Y : Set ℂ} {e : ℂ → ℕ}

/-- Local germs: near every point of `ℍ` there is a local lift, and every germ over a small ball
is the jet of a holomorphic lift on the whole ball. -/
private theorem local_germs (he : ∀ w, 0 < e w) (hp : IsOrbCover p Y e)
    (hf : ∀ z ∈ upper, HasLocalForm f z (e (f z))) {z₀ : ℂ} (hz₀ : z₀ ∈ upper) :
    ∃ r > (0 : ℝ), ball z₀ r ⊆ upper ∧
      (∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball z₀ r) ∧ ∀ z ∈ ball z₀ r, jet H z ∈ germs p f Y) ∧
      ∀ q ∈ germs p f Y, q.1 ∈ ball z₀ r → ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball z₀ r) ∧
        (∀ z ∈ ball z₀ r, jet H z ∈ germs p f Y) ∧ q = jet H q.1 := by
  obtain ⟨r, hr, hsub, ι, U, K, H, ⟨i₀⟩, hK1, -, -, hd, hv, hcl, -⟩ := orbifoldLocalLiftData he hp hf hz₀
  have hS : ∀ i, ∀ ζ ∈ K, ∀ z ∈ ball z₀ r, jet (H i ζ) z ∈ germs p f Y := fun i ζ hζ z hz ↦
    ⟨hsub hz, H i ζ, isLocLift_of isOpen_ball (hd i ζ hζ)
      (fun x hx ↦ ⟨(hv i ζ hζ x hx).2.1, (hv i ζ hζ x hx).2.2⟩) hz, rfl⟩
  refine ⟨r, hr, hsub, ⟨H i₀ 1, hd i₀ 1 hK1, hS i₀ 1 hK1⟩, ?_⟩
  rintro q ⟨-, h, hh, hq⟩ hqb
  obtain ⟨i, ζ, hζ, hhe⟩ := hcl q.1 hqb h hh
  exact ⟨H i ζ, hd i ζ hζ, hS i ζ hζ, hq.symm.trans (jet_congr hhe)⟩

/-- A holomorphic family of germs over an open set gives a continuous section of `germs`. -/
private theorem exists_section {S : Set (ℂ × ℂ × ℂ)} {V : Set ℂ} {H : ℂ → ℂ}
    (hd : DifferentiableOn ℂ H V) (hV : IsOpen V) (hS : ∀ z ∈ V, jet H z ∈ S) (q : S)
    (hq : q.1.1 ∈ V) (hqH : q.1 = jet H q.1.1) :
    ∃ s : ℂ → S, ContinuousOn s V ∧ (∀ z ∈ V, (s z).1 = jet H z) ∧ s q.1.1 = q := by
  classical
  refine ⟨fun z ↦ if hz : z ∈ V then ⟨jet H z, hS z hz⟩ else q, ?_, fun z hz ↦ by simp [hz],
    Subtype.ext (by simp [hq, hqH.symm])⟩
  rw [continuousOn_iff_continuous_domRestrict]
  have : V.domRestrict (fun z ↦ if hz : z ∈ V then (⟨jet H z, hS z hz⟩ : S) else q) =
      fun z : V ↦ ⟨jet H z, hS z z.2⟩ := funext fun z ↦ dif_pos z.2
  rw [this]
  exact ((continuousOn_iff_continuous_domRestrict).mp (continuousOn_jet hd hV)).subtype_mk _

/-- The projection of `germs` to `ℍ` is locally injective. -/
private theorem germs_locallyInjective (he : ∀ w, 0 < e w) (hp : IsOrbCover p Y e)
    (hf : ∀ z ∈ upper, HasLocalForm f z (e (f z))) (q : germs p f Y) :
    ∃ W ∈ 𝓝 q, InjOn (fun q : germs p f Y ↦ q.1.1) W := by
  obtain ⟨hz₀, h₀, hh₀, hq⟩ := q.2
  set z₀ := q.1.1
  obtain ⟨r, hr, -, ι, U, K, H, -, -, hdisj, hUo, hd, hv, hcl, hsep⟩ := orbifoldLocalLiftData he hp hf hz₀
  obtain ⟨i, ζ, hζ, hhe⟩ := hcl z₀ (mem_ball_self hr) h₀ hh₀
  have hqj : q.1 = jet (H i ζ) z₀ := hq.symm.trans (jet_congr hhe)
  have hπ : Continuous fun q : germs p f Y ↦ q.1.1 := continuous_fst.comp continuous_subtype_val
  have hbq : ∀ᶠ q' in 𝓝 q, q'.1.1 ∈ ball z₀ r :=
    hπ.continuousAt.eventually_mem (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hjc : ∀ ζ' ∈ K, ContinuousAt (fun q' : germs p f Y ↦ jet (H i ζ') q'.1.1) q := fun ζ' hζ' ↦
    ContinuousAt.comp (g := jet (H i ζ')) (f := fun q' : germs p f Y ↦ q'.1.1)
      ((continuousOn_jet (hd i ζ' hζ') isOpen_ball).continuousAt
        (isOpen_ball.mem_nhds (mem_ball_self hr))) hπ.continuousAt
  have hne : ∀ ζ' ∈ K, ∀ᶠ q' in 𝓝 q, ζ' ≠ ζ → q'.1 ≠ jet (H i ζ') q'.1.1 := by
    intro ζ' hζ'
    by_cases h : ζ' = ζ
    · exact Eventually.of_forall fun _ h' ↦ (h' h).elim
    · have hq' : q.1 ≠ jet (H i ζ') q.1.1 := by
        rw [hqj]
        intro heq
        exact hsep i ζ hζ ζ' hζ' (Ne.symm h) (congrArg (fun x ↦ x.2.2) heq)
      exact ((continuous_subtype_val.continuousAt.ne_iff_eventually_ne (hjc ζ' hζ')).mp
        hq').mono fun _ hx _ ↦ hx
  have hU : ∀ᶠ q' in 𝓝 q, q'.1.2.1 ∈ U i := by
    have : q.1.2.1 ∈ U i := by rw [hqj]; exact (hv i ζ hζ z₀ (mem_ball_self hr)).1
    exact ((continuous_fst.comp (continuous_snd.comp continuous_subtype_val)).continuousAt
      (x := q)).eventually_mem ((hUo i).mem_nhds this)
  refine ⟨_, hbq.and (hU.and ((Filter.eventually_all_finset K).2 hne)), ?_⟩
  -- every germ in the neighbourhood is the jet of `H i ζ`
  have key : ∀ q' : germs p f Y, q'.1.1 ∈ ball z₀ r → q'.1.2.1 ∈ U i →
      (∀ ζ' ∈ K, ζ' ≠ ζ → q'.1 ≠ jet (H i ζ') q'.1.1) → q'.1 = jet (H i ζ) q'.1.1 := by
    intro q' hb hUi hne'
    obtain ⟨-, h', hh', hq'⟩ := q'.2
    obtain ⟨i', ζ', hζ', hhe'⟩ := hcl _ hb h' hh'
    have hj : q'.1 = jet (H i' ζ') q'.1.1 := hq'.symm.trans (jet_congr hhe')
    have hii : i' = i := by
      by_contra hii
      have h1 : q'.1.2.1 ∈ U i' := by rw [hj]; exact (hv i' ζ' hζ' _ hb).1
      exact Set.disjoint_left.mp (hdisj hii) h1 hUi
    subst hii
    by_contra hζζ
    exact hne' ζ' hζ' (fun h ↦ hζζ (h ▸ hj)) hj
  rintro q₁ ⟨hb₁, hU₁, hn₁⟩ q₂ ⟨hb₂, hU₂, hn₂⟩ h12
  apply Subtype.ext
  rw [key q₁ hb₁ hU₁ hn₁, key q₂ hb₂ hU₂ hn₂]
  exact congrArg (jet (H i ζ)) h12

/-- The germs of local lifts form a covering of `ℍ`. -/
private theorem germs_isCoveringMapOn (he : ∀ w, 0 < e w) (hp : IsOrbCover p Y e)
    (hf : ∀ z ∈ upper, HasLocalForm f z (e (f z))) :
    IsCoveringMapOn (fun q : germs p f Y ↦ q.1.1) upper := by
  have hπ : Continuous fun q : germs p f Y ↦ q.1.1 := continuous_fst.comp continuous_subtype_val
  have hpre : (fun q : germs p f Y ↦ q.1.1) ⁻¹' upper = univ :=
    eq_univ_of_forall fun q ↦ q.2.1
  refine isCoveringMapOn_of_sections (by rw [hpre]; exact isOpen_univ)
    hπ.continuousOn (fun q _ ↦ germs_locallyInjective he hp hf q) fun x hx ↦ ?_
  obtain ⟨r, hr, hsub, -, hloc⟩ := local_germs he hp hf hx
  refine ⟨ball x r, isOpen_ball, mem_ball_self hr, hsub, (convex_ball x r).isPreconnected,
    fun q hq ↦ ?_⟩
  obtain ⟨H, hd, hS, hqH⟩ := hloc q.1 q.2 hq
  obtain ⟨s, hs, hsH, hsq⟩ := exists_section hd isOpen_ball hS q hq hqH
  exact ⟨s, hs, fun z hz ↦ by rw [hsH z hz]; rfl, hsq⟩

/-- **Orbifold lifting** from the upper half-plane. -/
theorem orbLiftStatement : OrbLiftStatement := by
  intro p f Y e he hp _ hf
  have hcov := germs_isCoveringMapOn he hp hf
  have hI : I ∈ upper := by simp [upper]
  obtain ⟨r₀, hr₀, -, ⟨H₀, -, hS₀⟩, -⟩ := local_germs he hp hf hI
  obtain ⟨σ, hσc, hσ, -⟩ := hcov.exists_lift_of_convex (convex_halfSpace_im_gt 0)
    (g := fun z ↦ z) continuousOn_id (fun _ hz ↦ hz) hI
    (e₀ := ⟨jet H₀ I, hS₀ I (mem_ball_self hr₀)⟩) rfl
  refine ⟨fun z ↦ (σ z).1.2.1, ?_, ?_, ?_⟩
  rotate_left
  · intro z hz
    obtain ⟨-, h₀, hl, hj⟩ := (σ z).2
    rw [hσ z hz] at hl hj
    have : (σ z).1.2.1 = h₀ z := (congrArg (fun q : ℂ × ℂ × ℂ ↦ q.2.1) hj).symm
    change (σ z).1.2.1 ∈ Y
    rw [this]
    exact hl.self_of_nhds.2.1
  · intro z hz
    obtain ⟨-, h₀, hl, hj⟩ := (σ z).2
    rw [hσ z hz] at hl hj
    have : (σ z).1.2.1 = h₀ z := (congrArg (fun q : ℂ × ℂ × ℂ ↦ q.2.1) hj).symm
    change p (σ z).1.2.1 = f z
    rw [this]
    exact hl.self_of_nhds.2.2
  intro z hz
  obtain ⟨r, hr, -, -, hloc⟩ := local_germs he hp hf hz
  have hzb : (σ z).1.1 ∈ ball z r := by rw [hσ z hz]; exact mem_ball_self hr
  obtain ⟨H, hd, hS, hqH⟩ := hloc (σ z).1 (σ z).2 hzb
  obtain ⟨s, hs, hsH, hsq⟩ := exists_section hd isOpen_ball hS (σ z) hzb hqH
  rw [hσ z hz] at hsq
  obtain ⟨W, hW, hWinj⟩ := germs_locallyInjective he hp hf (σ z)
  have hσz : ContinuousAt σ z := hσc.continuousAt (isOpen_upper.mem_nhds hz)
  have hsz : ContinuousAt s z := hs.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have h1 : ∀ᶠ x in 𝓝 z, σ x ∈ W := hσz.preimage_mem_nhds hW
  have h2 : ∀ᶠ x in 𝓝 z, s x ∈ W := hsz.preimage_mem_nhds (by rw [hsq]; exact hW)
  have heq : (fun x ↦ (σ x).1.2.1) =ᶠ[𝓝 z] H := by
    filter_upwards [h1, h2, isOpen_upper.mem_nhds hz, isOpen_ball.mem_nhds (mem_ball_self hr)]
      with x hx1 hx2 hxu hxb
    have hσs : σ x = s x := hWinj hx1 hx2 (by
      change (σ x).1.1 = (s x).1.1
      rw [hσ x hxu, hsH x hxb]
      rfl)
    rw [hσs, hsH x hxb]
    rfl
  exact ((hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).congr_of_eventuallyEq
    heq).differentiableWithinAt

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
