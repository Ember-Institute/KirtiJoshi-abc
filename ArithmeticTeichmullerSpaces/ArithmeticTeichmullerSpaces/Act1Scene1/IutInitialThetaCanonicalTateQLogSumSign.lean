import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalRawTargetAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRootProductContracting

/-!
source-id: JT-SCENE1-CANONICAL-TATE-QLOGSUM-SIGN
source: the canonical Tate q-log sum/reference degree identity and the actual
reference `absLogQ` positivity theorem.
fidelity: proves strict positivity of the raw target qLogSum for any supplied
canonical Tate-compatible Scene1 bundle. This freezes the raw sign under
explicit compatibility conditions; it does not settle the paper literal sign
or identify the target with paper thetaVolume.
boundary: Scene1/Derived. Original proof; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
universe u
noncomputable section

theorem canonicalTateScene1Data_qLogSum_pos
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (base : Corollary312Scene1Data (K := D.F) (O := O) p)
    (hEll : base.target.ell = D.prime.ℓ)
    (hTate : base.target.scene1.data.link.tate =
      iutInitialThetaTateParameterData D) :
    0 < Corollary312Data.qLogSum p base.target := by
  rw [canonicalTateScene1Data_qLogSum_eq_degree_mul_reference p D base hEll hTate]
  have hDegree : (0 : ℝ) < Module.finrank ℚ D.F := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ D.F)
  exact mul_pos hDegree (iutInitialThetaReferenceAbsLogQ_pos D)

end
end JoshiTeich.Act1Scene1
