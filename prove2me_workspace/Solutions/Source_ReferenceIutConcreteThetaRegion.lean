/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/ThetaRegion.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_Statement
import Solutions.Source_ReferenceIutConcreteContainer
import Solutions.Source_ReferenceIutQPilot

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

universe u v

open NumberField
open scoped BigOperators Pointwise

namespace LocalTheory

variable {K : Type u} [Field K] [NumberField K] (LT : LocalTheory.{u, v} K)

/-- The theta-pilot component at the archimedean place: the union of the images of the
tensor product of the log-shells under the indeterminacy automorphisms. -/
noncomputable def thetaInfinite (n : ℕ) (i : Fin n)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber .infinite) :
    Set (LT.Tensor .infinite (LT.tuple .infinite c)) :=
  ⋃ φ ∈ LT.indAut .infinite (LT.tuple .infinite c),
    φ '' LT.logShell .infinite (LT.tuple .infinite c)

end LocalTheory

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG)

/-- The `ℓ`-torsion field of the Θ-data, as a type. -/
abbrev InitialThetaData.Kt : Type u := ↥D.prime.torsionField

/-- **The local theta data**: the `2ℓ`-th roots `q_v = q^{1/2ℓ}` of the Tate parameters at
the places of `K` over the bad places of `F` (IUT I, Example 3.2(iv)), with the
comparison map of completions `F_w → K_v`. Delegated: the existence of the roots follows
from the rationality of the `2ℓ`-torsion of the Tate curve over `K_v` (taxis #13/#36,
`lana-agents/tate-curves-theta`). The places whose residue characteristic is not in the
finite set `badChars` (the residue characteristics of the bad places) carry `q_v = 1`. -/
structure ThetaLocalData (LT : LocalTheory.{u, v} D.Kt) where
  /-- The residue characteristics of the bad places. -/
  badChars : Finset ℕ
  /-- The `2ℓ`-th root of the Tate parameter at `v` (`1` away from the bad places). -/
  qroot : ∀ v : FinitePlace D.Kt, completionAt D.Kt v
  /-- `q_v ≠ 0`. -/
  qroot_ne_zero : ∀ v, qroot v ≠ 0
  /-- `ord_p(q_v) ≥ 0`. -/
  ordp_qroot_nonneg : ∀ v, 0 ≤ ordp D.Kt v (qroot v)
  /-- Away from the bad residue characteristics, `q_v = 1`. -/
  qroot_eq_one : ∀ v, residueChar v ∉ badChars → qroot v = 1
  /-- The comparison map of completions `F_w → K_v` for `v ∣ w`. -/
  embedF : ∀ (v : FinitePlace D.Kt) (w : FinitePlace D.F),
    FinitePlace.LiesOver v w → localCompletion w →+* completionAt D.Kt v
  /-- `q_v^{2ℓ}` is the Tate parameter of `E` at `w` (IUT I, Example 3.2(iv)). -/
  qroot_pow : ∀ (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : FinitePlace.LiesOver v w) (hw : w ∈ badPlacesOver D.F D.E D.VBad),
    qroot v ^ (2 * D.ℓ) = embedF v w h ((D.prime.tate w hw).q : localCompletion w)
  /-- `ord_p(q_v) = ord_w(q_w)/(2ℓ·e_w)`: the normalized order of the root, from the
  integer order of the Tate parameter (taxis #37) and the ramification index of `w`. -/
  ordp_qroot : ∀ (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (_ : FinitePlace.LiesOver v w) (hw : w ∈ badPlacesOver D.F D.E D.VBad),
    ordp D.Kt v (qroot v) = (D.prime.qOrder w hw : ℝ) / (2 * D.ℓ * ramIdx D.F w)
  /-- The bad places of `K` have residue characteristic in `badChars`. -/
  residueChar_mem : ∀ (v : FinitePlace D.Kt) (w : FinitePlace D.F),
    FinitePlace.LiesOver v w → w ∈ badPlacesOver D.F D.E D.VBad →
    residueChar v ∈ badChars
  /-- The bad places of `F` have residue characteristic in `badChars`. -/
  bad_residueChar_mem : ∀ w ∈ badPlacesOver D.F D.E D.VBad, residueChar w ∈ badChars
  /-- The bad residue characteristics are prime. -/
  badChars_prime : ∀ p ∈ badChars, p.Prime
  /-- **Base-change invariance of the `q`-degree** at each prime `p`: the weighted sum
  over the places `v ∣ p` of `K` of `[K_v : ℚ_p]/[K : ℚ]·ord_p(q_v)` equals
  `(1/2ℓ)·∑_{w ∣ p, w bad} (f_w/[F : ℚ])·ord_w(q_w)` (from `∑_{v ∣ w} e_v f_v = [K : F]·e_w f_w`
  and `ord_p(q_v) = ord_w(q_w)/(2ℓ e_w)`). -/
  sum_weight_ordp_qroot : ∀ (p : Nat.Primes) (bad : Finset (FinitePlace D.F))
    (hbad : ↑bad = badPlacesOver D.F D.E D.VBad),
    ∑ v : LT.Fiber (.finite p), LT.weight (.finite p) v * ordp D.Kt (LT.fiberPlace v)
        (qroot (LT.fiberPlace v)) =
      (∑ w ∈ bad.attach.filter (fun w => residueChar w.1 = p),
        (inertDeg D.F w.1 : ℝ) / Module.finrank ℚ D.F *
          (D.prime.qOrder w.1 (hbad ▸ Finset.mem_coe.mpr w.2) : ℝ)) / (2 * D.ℓ)

variable (LT : LocalTheory.{u, v} D.Kt) (TL : ThetaLocalData D LT)


namespace ThetaLocalData

variable {D LT}
variable (n : ℕ)

/-- The distinguished label `j = i + 1` of the capsule `S_{j+1} = {0, …, i+1}` of the
standard procession. -/
def distinguished (i : Fin n) : ((Procession.standard n).capsule i).LabelType :=
  ⟨i.1 + 1, by simp [Procession.standard, procLabels]⟩

/-- The scaling element `q_{v_j}^{j²}` of a tuple at a finite place, in the `j`-th tensor
factor. -/
noncomputable def scaleElt (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber (.finite p)) :
    LT.Tensor (.finite p) (LT.tuple _ c) :=
  LT.incl p (LT.tuple _ c) (distinguished n i) (LT.fiberPlace (c (distinguished n i)))
    (LT.fiberPlace_spec _) (TL.qroot (LT.fiberPlace (c (distinguished n i))) ^ (i.1 + 1) ^ 2)

lemma isUnit_scaleElt (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber (.finite p)) :
    IsUnit (TL.scaleElt n i p c) :=
  LT.isUnit_incl p _ _ _ _ _ (pow_ne_zero _ (TL.qroot_ne_zero _))

/-- `ord_p` of the scaling element's root: `j²·ord_p(q_{v_j}) ≥ 0`. -/
lemma ordp_pow_nonneg (v : FinitePlace D.Kt) (m : ℕ) :
    0 ≤ ordp D.Kt v (TL.qroot v ^ m) := by
  induction m with
  | zero => simp [ordp, norm_one]
  | succ k ih =>
    rw [pow_succ, LT.ordp_mul v _ _ (pow_ne_zero _ (TL.qroot_ne_zero v)) (TL.qroot_ne_zero v)]
    linarith [TL.ordp_qroot_nonneg v]

/-- The theta-pilot component at a finite place: the union of the images of
`q_{v_j}^{j²}·(R_I)^∼` under the indeterminacy automorphisms. -/
noncomputable def thetaFinite (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber (.finite p)) :
    Set (LT.Tensor (.finite p) (LT.tuple _ c)) :=
  ⋃ φ ∈ LT.indAut (.finite p) (LT.tuple _ c),
    φ '' (TL.scaleElt n i p c • LT.integral (.finite p) (LT.tuple _ c))

/-- The theta-pilot component at any rational place. -/
noncomputable def thetaComponent (i : Fin n) (vQ : RationalPlace)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber vQ) :
    Set (LT.Tensor vQ (LT.tuple vQ c)) :=
  match vQ, c with
  | .finite p, c => TL.thetaFinite n i p c
  | .infinite, c => LT.thetaInfinite n i c

/-- Each theta-pilot component is admissible for the hull. -/
lemma thetaComponent_admissible (i : Fin n) (vQ : RationalPlace)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber vQ) :
    TL.thetaComponent n i vQ c ∈ LT.admissible vQ (LT.tuple _ c) := by
  rcases vQ with p | _
  · exact LT.theta_admissible _ _ _ (TL.isUnit_scaleElt n i p c)
  · exact LT.thetaShell_admissible _ _

/-- Each theta-pilot component lies in the log-shell. -/
lemma thetaComponent_subset_logShell (i : Fin n) (vQ : RationalPlace)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber vQ) :
    TL.thetaComponent n i vQ c ⊆ LT.logShell vQ (LT.tuple _ c) := by
  rcases vQ with p | _
  · intro x hx
    change x ∈ ⋃ φ ∈ LT.indAut (.finite p) (LT.tuple _ c),
      φ '' (TL.scaleElt n i p c • LT.integral (.finite p) (LT.tuple _ c)) at hx
    obtain ⟨φ, hφ, hx⟩ := Set.mem_iUnion₂.mp hx
    refine LT.indAut_logShell _ _ φ hφ (Set.image_mono ?_ hx)
    exact (LT.smul_integral_subset p _ _ _ _ _ (pow_ne_zero _ (TL.qroot_ne_zero _))
      (TL.ordp_pow_nonneg _ _)).trans (LT.integral_subset_logShell p _)
  · intro x hx
    change x ∈ ⋃ φ ∈ LT.indAut .infinite (LT.tuple .infinite c),
      φ '' LT.logShell .infinite (LT.tuple .infinite c) at hx
    obtain ⟨φ, hφ, hx⟩ := Set.mem_iUnion₂.mp hx
    exact LT.indAut_logShell _ _ φ hφ hx

/-- Away from the bad residue characteristics, the theta-pilot component is the integral
structure (the indeterminacy automorphisms preserve the maximal order at every prime). -/
lemma thetaComponent_eq_integral (i : Fin n) (p : Nat.Primes)
    (c : ((Procession.standard n).capsule i).LabelType → LT.Fiber (.finite p))
    (hbad : (p : ℕ) ∉ TL.badChars) :
    TL.thetaComponent n i (.finite p) c = LT.integral (.finite p) (LT.tuple _ c) := by
  have hscale : TL.scaleElt n i p c = 1 := by
    unfold scaleElt
    rw [TL.qroot_eq_one _ (by rw [LT.residueChar_fiberPlace]; exact hbad), one_pow, map_one]
  apply Set.Subset.antisymm
  · intro x hx
    change x ∈ ⋃ φ ∈ LT.indAut (.finite p) (LT.tuple _ c),
      φ '' (TL.scaleElt n i p c • LT.integral (.finite p) (LT.tuple _ c)) at hx
    obtain ⟨φ, hφ, hx⟩ := Set.mem_iUnion₂.mp hx
    rw [hscale, one_smul] at hx
    exact LT.prop14_iv p _ φ hφ hx
  · intro x hx
    change x ∈ ⋃ φ ∈ LT.indAut (.finite p) (LT.tuple _ c),
      φ '' (TL.scaleElt n i p c • LT.integral (.finite p) (LT.tuple _ c))
    exact Set.mem_iUnion₂.mpr ⟨id, LT.id_mem_indAut _ _, by
      rw [hscale, one_smul]; exact ⟨x, hx, rfl⟩⟩

/-- **The concrete theta-pilot region** of the container at capsule `i`. -/
noncomputable def thetaPilot (i : Fin (LT.container n).proc.length) :
    (LT.container n).AdmissibleRegion i where
  region vQ := (LT.packet _ vQ).productRegion fun c => TL.thetaComponent n i vQ c
  finiteSupport := by
    change Fin n at i
    have hfin : (({RationalPlace.infinite} ∪ {RationalPlace.finite ⟨2, Nat.prime_two⟩} ∪
        ((fun w => LT.toRational (Place.finite w)) '' {w | ramIdx D.Kt w ≠ 1}) ∪
        ((fun q : ℕ => if h : q.Prime then RationalPlace.finite ⟨q, h⟩ else .infinite) ''
          ↑TL.badChars) : Set RationalPlace)).Finite :=
      (((Set.finite_singleton _).union (Set.finite_singleton _)).union
        (LT.ramified_finite.image _)).union (TL.badChars.finite_toSet.image _)
    refine hfin.subset fun vQ hvQ => ?_
    by_contra hmem
    apply hvQ
    rcases vQ with p | _
    · have hbad : (p : ℕ) ∉ TL.badChars := by
        intro hb
        apply hmem
        refine Or.inr ⟨p, hb, ?_⟩
        simp only [dif_pos p.2] <;> rfl
      change (LT.packet _ _).productRegion _ = (LT.packet _ _).integralRegion
      ext x
      change (∀ c, x c ∈ TL.thetaComponent n i (.finite p) c) ↔
        ∀ c, x c ∈ LT.integral (.finite p) (LT.tuple (.finite p) c)
      refine forall_congr' fun c => ?_
      rw [TL.thetaComponent_eq_integral n i p c hbad]
    · exact absurd (Or.inl (Or.inl (Or.inl rfl))) hmem

/-- **The concrete right-hand-side data** of the Corollary 3.12 variant (taxis #35). -/
noncomputable def rhsData : RHSData.{u, v} D where
  container := LT.container ((D.ℓ - 1) / 2)
  proc_standard := rfl
  toRational_finite _ := rfl
  toRational_infinite _ := rfl
  vol := LT.vol _
  hull := LT.hull _
  thetaPilot := TL.thetaPilot _
  thetaPilot_hullAdmissible i vQ :=
    ⟨fun c => TL.thetaComponent _ i vQ c, fun c => TL.thetaComponent_admissible _ i vQ c, rfl⟩
  thetaPilot_le_shell i vQ _ hx c :=
    TL.thetaComponent_subset_logShell _ i vQ c (hx c)

end ThetaLocalData

/-- **The concrete Corollary 3.12 variant data**: initial Θ-data with the concrete
`q`-pilot data and the concrete right-hand side. -/
noncomputable def concreteVariantData (QI : QPilotInputs D) :
    Corollary312VariantData.{u, v} AG TG where
  data := D
  qPilot := QI.qPilot
  rhsData := TL.rhsData

end AbcAdaptation.Reference.Iut
