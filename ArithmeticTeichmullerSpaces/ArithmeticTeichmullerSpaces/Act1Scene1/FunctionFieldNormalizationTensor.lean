import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationFinite
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.GoingUp

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Mathlib tensor products, integrality in towers
and integral closures in the actual ambient function field.
fidelity: constructs the tensor map from two actual normalization rings into
a common normalization. The upper ring is finite over the tensor source and
is its integral closure in the specified common field. Tensor injectivity and
an orbicurve cartesian square are not assumed.
boundary: Scene1/Derived. These are ordinary coordinate-algebra comparisons.
-/

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open scoped Classical TensorProduct IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
variable {F Z N : IntermediateField (rationalBase k t) Ω}

def coordRingBaseAlgebra (L : IntermediateField (rationalBase k t) Ω) :
    Algebra (polynomialBase k t) (coordRing t L) :=
  (coordRing t L).algebra

def ringMapOverBase (h : F ≤ N) : coordRing t F →ₐ[polynomialBase k t] coordRing t N :=
  { (ringMap h).toRingHom with commutes' := fun _ => rfl }

def normalizationTensorMap (hF : F ≤ N) (hZ : Z ≤ N) :
    (coordRing t F ⊗[polynomialBase k t] coordRing t Z) →ₐ[polynomialBase k t] coordRing t N :=
  Algebra.TensorProduct.lift (ringMapOverBase hF) (ringMapOverBase hZ)
    (fun _ _ => Commute.all _ _)

theorem normalizationTensorMap_tmul (hF : F ≤ N) (hZ : Z ≤ N)
    (a : coordRing t F) (b : coordRing t Z) :
    normalizationTensorMap hF hZ (a ⊗ₜ b) = ringMap hF a * ringMap hZ b := rfl

def normalizationTensorFieldMap (hF : F ≤ N) (hZ : Z ≤ N) :
    (coordRing t F ⊗[polynomialBase k t] coordRing t Z) →ₐ[polynomialBase k t] N :=
  (IsScalarTower.toAlgHom (polynomialBase k t) (coordRing t N) N).comp
    (normalizationTensorMap hF hZ)

theorem normalizationTensor_integral :
    Algebra.IsIntegral (polynomialBase k t)
      (coordRing t F ⊗[polynomialBase k t] coordRing t Z) := by
  let a : Algebra (coordRing t F) (coordRing t F ⊗[polynomialBase k t] coordRing t Z) :=
    Algebra.TensorProduct.leftAlgebra (R := polynomialBase k t) (S := coordRing t F)
      (A := coordRing t F) (B := coordRing t Z)
  let : SMul (coordRing t F) (coordRing t F ⊗[polynomialBase k t] coordRing t Z) := a.toSMul
  let : Module (coordRing t F) (coordRing t F ⊗[polynomialBase k t] coordRing t Z) := a.toModule
  let : Algebra (coordRing t F) (coordRing t F ⊗[polynomialBase k t] coordRing t Z) := a
  have : IsScalarTower (polynomialBase k t) (coordRing t F)
      (coordRing t F ⊗[polynomialBase k t] coordRing t Z) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral (coordRing t F) (coordRing t F ⊗[polynomialBase k t] coordRing t Z) :=
    Algebra.IsIntegral.tensorProduct (polynomialBase k t) (coordRing t F) (coordRing t Z)
  exact Algebra.IsIntegral.trans (coordRing t F)

theorem normalizationTensor_isIntegralClosure (hF : F ≤ N) (hZ : Z ≤ N) :
    letI := (normalizationTensorFieldMap hF hZ).toRingHom.toAlgebra
    IsIntegralClosure (coordRing t N)
      (coordRing t F ⊗[polynomialBase k t] coordRing t Z) N := by
  let T := coordRing t F ⊗[polynomialBase k t] coordRing t Z
  let f := normalizationTensorFieldMap hF hZ
  let : Algebra T N := f.toRingHom.toAlgebra
  have : IsScalarTower (polynomialBase k t) T N :=
    IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  have : Algebra.IsIntegral (polynomialBase k t) T := normalizationTensor_integral
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  constructor
  · intro hx
    exact (IsIntegralClosure.isIntegral_iff (A := coordRing t N) (R := polynomialBase k t)).mp
      (isIntegral_trans (R := polynomialBase k t) x hx)
  · rintro ⟨y, rfl⟩
    exact ((integralClosure.isIntegral (R := polynomialBase k t) (A := N) y).algebraMap).tower_top

theorem normalizationTensorMap_finite [FiniteDimensional (rationalBase k t) N]
    [Algebra.IsSeparable (rationalBase k t) N]
    (ht : Transcendental k t) (hF : F ≤ N) (hZ : Z ≤ N) :
    RingHom.Finite (A := coordRing t F ⊗[polynomialBase k t] coordRing t Z)
      (B := coordRing t N) (normalizationTensorMap hF hZ).toRingHom := by
  let T := coordRing t F ⊗[polynomialBase k t] coordRing t Z
  let f := normalizationTensorMap hF hZ
  let : Algebra T (coordRing t N) := f.toRingHom.toAlgebra
  have : IsScalarTower (polynomialBase k t) T (coordRing t N) :=
    IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  have := finiteRing t ht N
  exact Module.Finite.of_restrictScalars_finite (polynomialBase k t) T (coordRing t N)

theorem quotientLift_range_eq {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) :
    (Ideal.Quotient.lift (RingHom.ker f) f (fun _ h => h)).range = f.range := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨b, Ideal.Quotient.lift_mk (RingHom.ker f) f (fun _ h => h)⟩
  · rintro x ⟨b, rfl⟩
    exact ⟨Ideal.Quotient.mk (RingHom.ker f) b,
      Ideal.Quotient.lift_mk (RingHom.ker f) f (fun _ h => h)⟩

theorem quotientLift_range_eq_of_ker_eq {R S T : Type*} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : R →+* T) (hker : RingHom.ker f = RingHom.ker g) :
    (Ideal.Quotient.lift (RingHom.ker f) g (fun x hx => by
      apply RingHom.mem_ker.mp
      rw [← hker]
      exact hx)).range = g.range := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨b, Ideal.Quotient.lift_mk (RingHom.ker f) g (fun x hx => by
      apply RingHom.mem_ker.mp
      rw [← hker]
      exact hx)⟩
  · rintro x ⟨b, rfl⟩
    exact ⟨Ideal.Quotient.mk (RingHom.ker f) b,
      Ideal.Quotient.lift_mk (RingHom.ker f) g (fun x hx => by
        apply RingHom.mem_ker.mp
        rw [← hker]
        exact hx)⟩

theorem quotientLift_injective_of_ker_eq {R S T : Type*} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : R →+* T) (hker : RingHom.ker f = RingHom.ker g) :
    Function.Injective (Ideal.Quotient.lift (RingHom.ker f) g (fun x hx => by
      apply RingHom.mem_ker.mp
      rw [← hker]
      exact hx)) :=
  RingHom.lift_injective_of_ker_le_ideal
    (I := RingHom.ker f)
    (fun x hx => by
      apply RingHom.mem_ker.mp
      rw [← hker]
      exact hx)
    (by rw [hker])

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
