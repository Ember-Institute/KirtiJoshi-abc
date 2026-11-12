import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationTensorField
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange

/-!
source-id: JT-SCENE1-NORMALIZATION-TENSOR-INJECTIVE
source: IUT I Definition 3.1(d), the Cartesian covering diagram;
Mathlib linear disjointness, flatness over Dedekind domains and localization
base change for tensor products.
fidelity: linearly disjoint actual function fields give an injective map
from their normalization-ring tensor product into a common normalization.
The polynomial base is a Dedekind domain, so its torsion-free normalization
rings embed into the field tensor product. Localization identifies the two
field tensor products, and linear disjointness makes multiplication injective.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived. This proves tensor injectivity, not normality of
the tensor product or an orbicurve Cartesian comparison.
-/

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open scoped Classical TensorProduct IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
variable {F Z N : IntermediateField (rationalBase k t) Ω}

set_option maxHeartbeats 1000000 in
private theorem normalizationTensorAmbientMap_comp
    (hF : F ≤ N) (hZ : Z ≤ N) :
    let A := polynomialBase k t
    let K := rationalBase k t
    let j : (coordRing t F ⊗[A] coordRing t Z) →ₗ[A] (F ⊗[A] Z) :=
      TensorProduct.map (coordRing t F).val.toLinearMap (coordRing t Z).val.toLinearMap
    let e : (F ⊗[K] Z) ≃ₗ[K] (F ⊗[A] Z) :=
      IsLocalization.moduleTensorEquiv (nonZeroDivisors A) K F Z
    let m := F.toSubalgebra.mulMap Z.toSubalgebra
    (normalizationTensorAmbientMap hF hZ).toLinearMap =
      (m.toLinearMap.restrictScalars A).comp
        ((e.symm.toLinearMap.restrictScalars A).comp j) := by
  ext a b
  rfl

theorem normalizationTensorAmbientMap_injective_of_linearDisjoint
    (ht : Transcendental k t) (hF : F ≤ N) (hZ : Z ≤ N)
    (hLD : F.LinearDisjoint Z) :
    Function.Injective (normalizationTensorAmbientMap hF hZ) := by
  let A := polynomialBase k t
  let K := rationalBase k t
  haveI : IsDedekindDomain A := dedekindBase t ht
  let j : (coordRing t F ⊗[A] coordRing t Z) →ₗ[A] (F ⊗[A] Z) :=
    TensorProduct.map (coordRing t F).val.toLinearMap (coordRing t Z).val.toLinearMap
  have hj : Function.Injective j :=
    TensorProduct.map_injective_of_flat_flat
      (coordRing t F).val.toLinearMap (coordRing t Z).val.toLinearMap
      Subtype.val_injective Subtype.val_injective
  let e : (F ⊗[K] Z) ≃ₗ[K] (F ⊗[A] Z) :=
    IsLocalization.moduleTensorEquiv (nonZeroDivisors A) K F Z
  let m := F.toSubalgebra.mulMap Z.toSubalgebra
  have hm : Function.Injective m :=
    Subalgebra.linearDisjoint_iff_injective.mp (IntermediateField.linearDisjoint_iff'.mp hLD)
  have hcomp := normalizationTensorAmbientMap_comp hF hZ
  change Function.Injective (normalizationTensorAmbientMap hF hZ).toLinearMap
  rw [hcomp]
  exact hm.comp (e.symm.injective.comp hj)

theorem normalizationTensorMap_injective_of_linearDisjoint
    (ht : Transcendental k t) (hF : F ≤ N) (hZ : Z ≤ N)
    (hLD : F.LinearDisjoint Z) :
    Function.Injective (normalizationTensorMap hF hZ) := by
  intro a b hab
  apply normalizationTensorAmbientMap_injective_of_linearDisjoint ht hF hZ hLD
  exact congrArg (fun x : coordRing t N => ((x : N) : Ω)) hab

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
