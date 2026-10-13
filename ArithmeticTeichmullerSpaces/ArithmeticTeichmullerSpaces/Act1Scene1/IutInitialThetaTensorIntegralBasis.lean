import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTensorIndex
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIntegralBasis

/-!
source-id: JT-SCENE1-INITIAL-THETA-TENSOR-INTEGRAL-BASIS
fidelity: derives finite generation, freeness, full rational span, lattice
structure and a finite integral basis of the actual q-root logarithm tensor
region. Its integral rank equals the product of the actual local factor
dimensions. The same basis extends to the rational tensor space and its
integral span recovers the region. Tensor index evaluation, weighted volume
and hull remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTensorWitness

open JoshiTeich.Prologue NumberField
open scoped BigOperators

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι]
variable (c : ι → (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset)
variable (hc : ∀ i, Arithmetic.residueChar (c i).1 = p)

local instance regionTensorScalarTower :
    IsScalarTower ℤ_[p] ℚ_[p] (packet D p c hc).Tensor := by
  constructor
  intro r s x
  change ((r : ℚ_[p]) * s) • x = (r : ℚ_[p]) • (s • x)
  rw [mul_smul]

theorem region_module_finite : Module.Finite ℤ_[p] (region D p c hc) := by
  let P := packet D p c hc
  rw [region_eq_ballLattice]
  exact LocalCompletion.Packet.bounded_module_finite P _
    (LocalCompletion.Packet.unitLattice_isBounded P |>.subset
      (LocalCompletion.Packet.lattice_mono P (fun i => Metric.closedBall_subset_closedBall
        ((IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one D (c i)).le))))

theorem region_module_free : Module.Free ℤ_[p] (region D p c hc) := by
  let P := packet D p c hc
  let L := region D p c hc
  letI : Module.Finite ℤ_[p] L := region_module_finite D p c hc
  letI : Module.IsTorsionFree ℤ_[p] P.Tensor :=
    LocalCompletion.Packet.tensorIntegralTorsionFree P
  exact Module.free_of_finite_type_torsion_free'

theorem region_span_eq_top :
    Submodule.span ℚ_[p] (region D p c hc : Set (packet D p c hc).Tensor) = ⊤ := by
  let P := packet D p c hc
  rw [region_eq_ballLattice]
  apply LocalCompletion.Packet.lattice_balls_span_eq_top P
  intro i
  exact norm_pos_iff.mpr
    ((IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot_ne_zero (c i))

theorem region_isLattice :
    @Submodule.IsLattice ℤ_[p] _ ℚ_[p] _ _ (packet D p c hc).Tensor _
      (inferInstance : Module ℤ_[p] (packet D p c hc).Tensor)
      (inferInstance : Module ℚ_[p] (packet D p c hc).Tensor)
      (regionTensorScalarTower (D := D) (p := p) (c := c) (hc := hc))
      (regionTensorScalarTower (D := D) (p := p) (c := c) (hc := hc))
      (region D p c hc) := by
  let P := packet D p c hc
  rw [region_eq_ballLattice]
  apply LocalCompletion.Packet.lattice_balls_isLattice P
  · intro i
    exact norm_pos_iff.mpr
      ((IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot_ne_zero (c i))
  · intro i
    exact (IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one D (c i)).le

noncomputable def regionFreeBasis := by
  letI : Module.Free ℤ_[p] (region D p c hc) := region_module_free D p c hc
  exact Module.Free.chooseBasis ℤ_[p] (region D p c hc)

noncomputable def regionFinBasis := by
  letI : Module.Free ℤ_[p] (region D p c hc) := region_module_free D p c hc
  letI : Module.Finite ℤ_[p] (region D p c hc) := region_module_finite D p c hc
  exact Module.finBasis ℤ_[p] (region D p c hc)

theorem region_finrank_eq_tensor_finrank :
    Module.finrank ℤ_[p] (region D p c hc) =
      Module.finrank ℚ_[p] (packet D p c hc).Tensor := by
  let P := packet D p c hc
  letI (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
    LocalCompletion.padicAlgebra (P.residueChar_eq i)
  letI (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
    LocalCompletion.finite_padicAlgebra (P.residueChar_eq i)
  letI : Module ℤ_[p] P.Tensor :=
    Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])
  letI : Module.Finite ℤ_[p] (region D p c hc) := region_module_finite D p c hc
  letI : IsScalarTower ℤ_[p] ℚ_[p] (packet D p c hc).Tensor :=
    regionTensorScalarTower (D := D) (p := p) (c := c) (hc := hc)
  have hRank :
      Module.rank ℤ_[p] (region D p c hc) =
        Module.rank ℚ_[p] P.Tensor :=
    @Submodule.IsLattice.rank' ℤ_[p] _ ℚ_[p] _ _ P.Tensor _
      (inferInstance : Module ℚ_[p] P.Tensor)
      (inferInstance : Module ℤ_[p] P.Tensor)
      (regionTensorScalarTower (D := D) (p := p) (c := c) (hc := hc))
      (inferInstance : IsDomain ℤ_[p])
      (inferInstance : IsPrincipalIdealRing ℤ_[p])
      (inferInstance : IsFractionRing ℤ_[p] ℚ_[p])
      (region D p c hc) (region_isLattice D p c hc)
  apply Module.finrank_eq_of_rank_eq
  exact hRank.trans (Module.finrank_eq_rank (R := ℚ_[p]) (M := P.Tensor)).symm

/-- The actual integral region has the product of the local factor dimensions as its rank. -/
theorem region_finrank_eq_factor_prod :
    Module.finrank ℤ_[p] (region D p c hc) =
      ∏ i, @Module.finrank ℚ_[p] ((packet D p c hc).Factor i) _ _
        (LocalCompletion.padicAlgebra ((packet D p c hc).residueChar_eq i)).toModule := by
  rw [region_finrank_eq_tensor_finrank]
  exact LocalCompletion.Packet.tensor_finrank_eq_factor_prod (packet D p c hc)

/-- Extend the actual integral basis, with the same vectors, to the rational tensor space. -/
noncomputable def regionRationalBasis :
    Module.Basis (Fin (Module.finrank ℤ_[p] (region D p c hc)))
      ℚ_[p] (packet D p c hc).Tensor :=
  @Module.Basis.extendOfIsLattice ℤ_[p] _ ℚ_[p] _ _ (packet D p c hc).Tensor _
    (inferInstance : Module ℚ_[p] (packet D p c hc).Tensor)
    (inferInstance : Module ℤ_[p] (packet D p c hc).Tensor)
    (regionTensorScalarTower (D := D) (p := p) (c := c) (hc := hc))
    (inferInstance : IsFractionRing ℤ_[p] ℚ_[p]) _
    (region D p c hc) (region_isLattice D p c hc) (regionFinBasis D p c hc)

set_option backward.isDefEq.respectTransparency false in
theorem regionRationalBasis_apply (k : Fin (Module.finrank ℤ_[p] (region D p c hc))) :
    regionRationalBasis D p c hc k =
      (regionFinBasis D p c hc k : (packet D p c hc).Tensor) := by
  simp only [regionRationalBasis, Module.Basis.extendOfIsLattice, Module.Basis.mk_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The extended basis still generates exactly the original integral region over `ℤ_p`. -/
theorem regionRationalBasis_integral_span :
    Submodule.span ℤ_[p] (Set.range (regionRationalBasis D p c hc)) = region D p c hc := by
  have hvec : regionRationalBasis D p c hc =
      (region D p c hc).subtype ∘ (regionFinBasis D p c hc) := by
    funext k
    exact regionRationalBasis_apply D p c hc k
  rw [hvec, Set.range_comp, ← Submodule.map_span,
    (regionFinBasis D p c hc).span_eq, Submodule.map_top, Submodule.range_subtype]

end
end JoshiTeich.Act1Scene1.InitialThetaTensorWitness
