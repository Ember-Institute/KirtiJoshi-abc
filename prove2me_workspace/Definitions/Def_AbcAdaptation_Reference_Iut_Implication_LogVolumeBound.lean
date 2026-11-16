/-
Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.
Original source path: Iut/Implication/LogVolumeBound.lean
Original authors: The iut contributors
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original license: Apache-2.0; the original copyright and license notice is retained below.
Effective compiler source override: accepted graph ci-012771-ee109b3e; upstream source differs from the compiler input.
Effective source SHA256: 90867d7f5b3181149c51c489d84e34533be3db266683533b3423fbbb20801342
Exact upstream/effective patch SHA256: c8072adc10654c50b180e7e94dca5883794b81ae2daaa9501b7272e34c6bb52b
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_Container
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ContainerHull
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_HolomorphicHull
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_LogVolume
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_PacketPresentation
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_Procession
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_RationalPlace
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_RightHandSide
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_Statement
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_AdmissiblePrime
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Basic
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_LocalConditions
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Orbicurve
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Places
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Invariants
import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.IntermediateField.Basic

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

/-!
# The log-volume upper bound (IUT IV, Theorem 1.10, Steps (iv)–(vii))

The right-hand side `−|log(Θ)|` of the Corollary 3.12 variant is the
procession-normalized log-volume of the holomorphic hull of the theta-pilot region
(`RHSData.rhs`, taxis #35). Steps (iv)–(vii) of the proof of IUT IV, Theorem 1.10 bound
this quantity from above, one rational place `v_ℚ` and one capsule `S_{j+1}` at a time:

* at a distinguished nonarchimedean `v_ℚ` (Step (v)), the union of the possible images
  of the theta-pilot is contained in a hull region `p^{⌊λ − d_I − a_I⌋ − b_I}·(R_I)^∼`
  (Proposition 1.4(iii)), whose log-volume is at most
  `(j+1)·log(d^K_{v_ℚ}) − (j²/2ℓ)·log(q_{v_ℚ}) + log(s^ℚ_{v_ℚ}) + 4(j+1)·l*_mod·log(s^≤_{v_ℚ})`
  after the weighted average of Proposition 1.7;
* at a non-distinguished nonarchimedean `v_ℚ` (Step (vi)), the container is the
  holomorphic integral structure itself, of log-volume `0` (Proposition 1.4(iv));
* at the archimedean place (Step (vii)), the container `π^{j+1}·B_I` has log-volume at
  most `(j+1)·log π` (Proposition 1.5(iii),(iv)).

## What is proved here and what is assumed

The local-field content — the existence of the containing hull regions and the bounds
on their log-volumes, i.e. IUT IV, Propositions 1.4 and 1.5 applied to the theta-pilot
images, together with the weighted average of Proposition 1.7 — is the explicit
certificate `LocalEstimate` (taxis #4, #278: it requires the `p`-adic log-shell theory
that this repository does not yet have). It also records monotonicity of the packet
log-volume between hull regions, a standard law of Haar measure deliberately left out of
the log-volume interface of taxis #44 (which records no law for zero or infinite
volumes); it is stated here only for hull regions, where it is meaningful.

What is *proved* is the passage from these local containments to the bound on
`RHSData.rhs`: the hull of the theta-pilot region is contained in every hull region
containing the theta-pilot region (minimality, taxis #45), the log-volume is bounded by
monotonicity, the sum over rational places is finitely supported (the container's
admissibility condition, taxis #43), and the procession average is the plain average
over capsules (taxis #44). This is `LocalEstimate.rhs_le`.
-/

namespace Iut

universe u v

open NumberField

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

namespace Theorem110Invariants

variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)

/-- The Step (v) upper bound for the packet log-volume of the container of theta-pilot
images at a distinguished prime `p`, for a capsule of cardinality `n = j + 1`:
`n·log(d^K_p) − ((n−1)²/2ℓ)·log(q_p) + log p + 4·n·l*_mod·ι_p`. -/
noncomputable def capsuleBound (n : ℕ) (p : ℕ) : ℝ :=
  n * inv.logDK p - ((n : ℝ) - 1) ^ 2 / (2 * X.ℓ) * X.logQAt p + Real.log p +
    4 * n * inv.lmod * inv.ι p

/-- **The local estimates of Steps (iv)–(vii)** as an explicit certificate: for every
capsule `i` and rational place `v_ℚ`, a hull region `cont i v_ℚ` containing the
theta-pilot region, equal to the holomorphic integral structure away from the
distinguished primes, with the log-volume bounds of Propositions 1.4(iii),(iv) and
1.5(iii),(iv); and monotonicity of the packet log-volume between hull regions. -/
structure LocalEstimate : Type (max u v) where
  /-- The containing hull region at capsule `i` and rational place `v_ℚ`
  (`p^{⌊λ − d_I − a_I⌋ − b_I}·(R_I)^∼`, resp. `(R_I)^∼`, resp. `π^{j+1}·B_I`). -/
  cont : ∀ (i : Fin X.rhsData.container.proc.length) (vQ : RationalPlace),
    Set (X.rhsData.container.packet i vQ).Total
  /-- Each container belongs to the class of hull regions of the hull system (a region
  `a·O` with all components of `a` units; at `∞` a real radial scaling of `B_I`). -/
  cont_mem_hullRegions : ∀ i vQ, cont i vQ ∈ (X.rhsData.hull.system i vQ).HullRegions
  /-- The theta-pilot region (the union of the images under (Ind1)–(Ind3)) is contained
  in the container: the inclusions `φ(p^λ·(R_I)^∼) ⊆ …` of Proposition 1.4(iii),(iv)
  and `⊗ m_i ∈ π^{|I|}·B_I` of Proposition 1.5(iv). -/
  thetaPilot_subset : ∀ i vQ, (X.rhsData.thetaPilot i).region vQ ⊆ cont i vQ
  /-- Away from the distinguished primes the container is the holomorphic integral
  structure (Proposition 1.4(iv): `φ((R_I)^∼) ⊆ (R_I)^∼`). -/
  cont_eq_integral : ∀ i (p : Nat.Primes), (p : ℕ) ∉ inv.dst →
    cont i (.finite p) = (X.rhsData.container.packet i (.finite p)).integralRegion
  /-- Step (v): at a distinguished prime the packet log-volume of the container is
  bounded by `capsuleBound` (Proposition 1.4(iii), (R4), and the weighted average of
  Proposition 1.7). -/
  vol_finite : ∀ i (p : Nat.Primes), (p : ℕ) ∈ inv.dst →
    X.rhsData.vol.packetVol i (.finite p) (cont i (.finite p)) ≤
      inv.capsuleBound (X.rhsData.container.proc.capsule i).card p
  /-- Step (vii): at the archimedean place the packet log-volume of the container is at
  most `(j+1)·log π` (Proposition 1.5(iii),(iv) and the normalization `μ(B_I) = 0`). -/
  vol_infinite : ∀ i,
    X.rhsData.vol.packetVol i .infinite (cont i .infinite) ≤
      (X.rhsData.container.proc.capsule i).card * Real.log Real.pi
  /-- Monotonicity of the packet log-volume between hull regions (a law of Haar
  measure for regions of finite nonzero volume). -/
  packetVol_mono : ∀ i vQ (U V : Set (X.rhsData.container.packet i vQ).Total),
    (X.rhsData.container.packet i vQ).IsHullRegion U →
    (X.rhsData.container.packet i vQ).IsHullRegion V → U ⊆ V →
    X.rhsData.vol.packetVol i vQ U ≤ X.rhsData.vol.packetVol i vQ V

namespace LocalEstimate

variable (est : inv.LocalEstimate)

/-- The pointwise upper bound function on rational places, for a capsule of
cardinality `n`: `capsuleBound n p` at a distinguished prime `p`, `0` at the other
primes, `n·log π` at the archimedean place. -/
noncomputable def placeBound (n : ℕ) : RationalPlace → ℝ
  | .finite p => if (p : ℕ) ∈ inv.dst then inv.capsuleBound n p else 0
  | .infinite => n * Real.log Real.pi

/-- The finite set of rational places carrying the distinguished primes. -/
noncomputable def dstPlaces : Finset RationalPlace :=
  inv.dst.attach.image fun p => RationalPlace.finite ⟨p.1, inv.dst_prime p.1 p.2⟩

attribute [local simp] dstPlaces.eq_1 placeBound.eq_1 placeBound.eq_2

variable {inv}

include est

end LocalEstimate

end Theorem110Invariants

end Iut

end AbcAdaptation.Reference
