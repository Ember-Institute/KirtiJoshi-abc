import ArithmeticTeichmullerSpaces.Act1Scene1.GaloisClosureTransport
import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Transport
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerPadicCohomology

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-CLOSURE-TRANSPORT
source: Joshi I ss:distinct-kummer-theories/pr:galois-cohomology-and-teich
(1588--1632); Joshi III compatible-root Kummer classes (3190--3208).
fidelity: maps original roots of unity coordinatewise along a K-algebra
field equivalence. This gives an equivariant continuous Z_p-linear Tate
isomorphism and original standard integral H1 equivalence. Transport of
any root tower is a root tower of the same base element, and the transported
Kummer class equals its independently chosen target-root-tower class.
No supplied group/twist marking, basis alignment, H1_e/BK or log law.
This covers preferred-closure changes over one field, not arbitrary
anabelomorphic fields or admissible holomorphoid production. Original proofs.
-/
namespace JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω Ξ : Type v} [Field Ω] [Field Ξ]
variable [Algebra K Ω] [Algebra K Ξ]
variable (e : Ω ≃ₐ[K] Ξ) (p : ℕ) [Fact p.Prime]

def tateMap : cyclotomicTateGroup p Ω →* cyclotomicTateGroup p Ξ where
  toFun x := ⟨fun n => Units.map e.toMonoidHom (x.1 n), by
    constructor
    · intro n; change Units.map e.toMonoidHom (x.1 n) ^ (p ^ n) = 1
      rw [← map_pow, x.2.1 n, map_one]
    · intro n; change Units.map e.toMonoidHom (x.1 (n+1)) ^ p = _
      rw [← map_pow, x.2.2 n]⟩
  map_one' := by apply Subtype.ext; funext n; exact map_one _
  map_mul' x y := by apply Subtype.ext; funext n; exact map_mul _ _ _

omit [Fact p.Prime] in
theorem tateMap_apply (x : cyclotomicTateGroup p Ω) (n : ℕ) :
    ((tateMap e p x).1 n : Ξ) = e (x.1 n) := rfl

omit [Fact p.Prime] in
theorem tateMap_symm (x : cyclotomicTateGroup p Ω) : tateMap e.symm p (tateMap e p x) = x := by
  apply Subtype.ext
  funext n
  apply Units.ext
  exact e.symm_apply_apply _

theorem tateMap_padicPower (r : ℤ_[p]) (x : cyclotomicTateGroup p Ω) :
    tateMap e p (padicPower r x) = padicPower r (tateMap e p x) := by
  apply Subtype.ext
  funext n
  exact map_pow (Units.map e.toMonoidHom) _ _

omit [Fact p.Prime] in
theorem tateMap_continuous : Continuous (tateMap e p) := by
  apply (continuous_tate_iff_level_locallyConstant _).mpr
  intro n
  have h := (continuous_tate_iff_level_locallyConstant
    (fun x : cyclotomicTateGroup p Ω => x)).mp continuous_id n
  exact h.comp (Units.map e.toMonoidHom)

def tateEquiv : Additive (cyclotomicTateGroup p Ω) ≃L[ℤ_[p]]
    Additive (cyclotomicTateGroup p Ξ) where
  toFun x := Additive.ofMul (tateMap e p x.toMul)
  invFun x := Additive.ofMul (tateMap e.symm p x.toMul)
  left_inv x := congrArg Additive.ofMul (tateMap_symm e p x.toMul)
  right_inv x := congrArg Additive.ofMul (tateMap_symm e.symm p x.toMul)
  map_add' x y := congrArg Additive.ofMul (map_mul (tateMap e p) x.toMul y.toMul)
  map_smul' r x := congrArg Additive.ofMul (tateMap_padicPower e p r x.toMul)
  continuous_toFun := continuous_ofMul.comp ((tateMap_continuous e p).comp continuous_toMul)
  continuous_invFun := continuous_ofMul.comp ((tateMap_continuous e.symm p).comp continuous_toMul)

variable [Algebra.IsIntegral K Ω] [Algebra.IsIntegral K Ξ]

theorem tateEquiv_equivariant (σ : Ξ ≃ₐ[K] Ξ) (x : Additive (cyclotomicTateGroup p Ω)) :
    tateEquiv e p (padicTateRepresentation p (GaloisClosureTransport.groupIso e σ) x) =
      padicTateRepresentation p σ (tateEquiv e p x) := by
  apply congrArg Additive.ofMul
  apply Subtype.ext
  funext n
  apply Units.ext
  exact GaloisClosureTransport.intertwine e σ _

def marking : ContinuousH1Transport.Marking
    (padicTateTopRep (K := K) (Ω := Ω) p) (padicTateTopRep (K := K) (Ω := Ξ) p) where
  groupIso := GaloisClosureTransport.groupIso e
  coefficientIso := tateEquiv e p
  equivariant := tateEquiv_equivariant e p

def h1Equiv : continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p) ≃L[ℤ_[p]]
    continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ξ) p) := (marking e p).h1Equiv

variable {p}

def mapRootTower {a : K} (T : RootTower (Ω := Ω) p a) : RootTower (Ω := Ξ) p a where
  root n := e (T.root n)
  root_zero := by rw [T.root_zero, e.commutes]
  root_succ n := by rw [← map_pow, T.root_succ]

omit [Algebra.IsIntegral K Ω] [Algebra.IsIntegral K Ξ] in
theorem mapRootTower_cocycle {a : K} (T : RootTower (Ω := Ω) p a)
    (ha : a ≠ 0) (σ : Ξ ≃ₐ[K] Ξ) :
    (mapRootTower e T).kummerCocycle (Fact.out : p.Prime).pos ha σ =
      tateMap e p (T.kummerCocycle (Fact.out : p.Prime).pos ha
        (GaloisClosureTransport.groupIso e σ)) := by
  apply Subtype.ext
  funext n
  apply Units.ext
  change σ (e (T.root n)) / e (T.root n) =
    e ((GaloisClosureTransport.groupIso e σ) (T.root n) / T.root n)
  rw [map_div₀, GaloisClosureTransport.intertwine]

theorem h1Equiv_rootTower {a : K} (T : RootTower (Ω := Ω) p a) (ha : a ≠ 0) :
    h1Equiv e p (padicClassOfCocycle p (T.continuousCocycleValue (Fact.out : p.Prime).pos ha)) =
      padicClassOfCocycle p
        ((mapRootTower e T).continuousCocycleValue (Fact.out : p.Prime).pos ha) := by
  change (marking e p).h1Equiv (ContinuousH1Homogeneous.classOf _ _ _) = _
  rw [(marking e p).h1Equiv_classOf]
  unfold padicClassOfCocycle
  congr 1
  ext σ
  exact congrArg Additive.ofMul (mapRootTower_cocycle e T ha σ).symm

variable [IsAlgClosed Ξ]

theorem h1Equiv_kummerClass {a : K} (T : RootTower (Ω := Ω) p a) (ha : a ≠ 0) :
    h1Equiv e p (toPadicH1 p (T.kummerClass (Fact.out : p.Prime).pos ha)) =
      toPadicH1 p ((rootTower (Ω := Ξ) p (Fact.out : p.Prime).pos a).kummerClass
        (Fact.out : p.Prime).pos ha) := by
  change h1Equiv e p (padicClassOfCocycle p _) = _
  rw [h1Equiv_rootTower]
  exact congrArg (toPadicH1 (K := K) (Ω := Ξ) p)
    ((mapRootTower e T).kummerClass_eq (rootTower p (Fact.out : p.Prime).pos a)
      (Fact.out : p.Prime).pos ha)

end
end JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport
