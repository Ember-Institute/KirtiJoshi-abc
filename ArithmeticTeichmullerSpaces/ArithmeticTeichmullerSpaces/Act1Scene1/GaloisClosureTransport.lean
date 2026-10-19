import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
source-id: JT-SCENE1-GALOIS-CLOSURE-TRANSPORT
source: Joshi I ss:distinct-kummer-theories and pr:galois-cohomology-and-teich
(1588--1632), with the preferred algebraic closure retained.
fidelity: a K-algebra equivalence of two extension fields produces the actual
Krull-topological conjugation equivalence of their Galois groups. Continuity
is proved from finite intermediate-field neighborhoods; no topological
marking is assumed. This covers closure change over a fixed K, not all
anabelomorphisms or holomorphoid marking producers. Original proofs.
-/
namespace JoshiTeich.Act1Scene1.GaloisClosureTransport
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω Ξ : Type v} [Field Ω] [Field Ξ]
variable [Algebra K Ω] [Algebra K Ξ]
variable (e : Ω ≃ₐ[K] Ξ)

theorem autCongr_continuous : Continuous (AlgEquiv.autCongr e) := by
  apply continuous_of_continuousAt_one (AlgEquiv.autCongr e).toMonoidHom
  change Filter.Tendsto (AlgEquiv.autCongr e) (𝓝 1) (𝓝 ((AlgEquiv.autCongr e) 1))
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ξ U).mp hU
  let F := E.map e.symm.toAlgHom
  have : FiniteDimensional K E := hE
  have : FiniteDimensional K F := LinearEquiv.finiteDimensional
    (IntermediateField.equivMap E e.symm.toAlgHom).toLinearEquiv
  apply Filter.mem_of_superset
    ((krullTopology_mem_nhds_one_iff K Ω _).mpr ⟨F, inferInstance, Set.Subset.rfl⟩)
  intro σ hσ
  apply hEU
  apply (IntermediateField.mem_fixingSubgroup_iff E (AlgEquiv.autCongr e σ)).mpr
  intro x hx
  change e (σ (e.symm x)) = x
  have hfix := (IntermediateField.mem_fixingSubgroup_iff F σ).mp hσ (e.symm x)
    (show e.symm x ∈ F from ⟨x, hx, rfl⟩)
  rw [hfix, e.apply_symm_apply]

def groupIso : (Ξ ≃ₐ[K] Ξ) ≃ₜ* (Ω ≃ₐ[K] Ω) where
  toMulEquiv := AlgEquiv.autCongr e.symm
  continuous_toFun := autCongr_continuous e.symm
  continuous_invFun := autCongr_continuous e

theorem groupIso_apply (σ : Ξ ≃ₐ[K] Ξ) (x : Ω) :
    groupIso e σ x = e.symm (σ (e x)) := rfl

theorem intertwine (σ : Ξ ≃ₐ[K] Ξ) (x : Ω) : e (groupIso e σ x) = σ (e x) :=
  e.apply_symm_apply _

end
end JoshiTeich.Act1Scene1.GaloisClosureTransport
