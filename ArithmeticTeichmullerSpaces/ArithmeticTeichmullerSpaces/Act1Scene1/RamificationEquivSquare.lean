import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Mathlib ideal transport and the comparison
between ideal-power and local-length definitions of ramification index.
fidelity: a commuting square of ring isomorphisms preserves ramification
indices over a nonzero extended ideal in Dedekind target rings.
boundary: Scene1/Derived. The arithmetic consumer supplies the original
coordinate-normalization square and proves all nonvanishing hypotheses.
-/

namespace JoshiTeich.Act1Scene1.RamificationEquivSquare

noncomputable section
variable {R S R' S' : Type*} [CommRing R] [CommRing S]
  [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R' S']
variable (eR : R ≃+* R') (eS : S ≃+* S')
variable (hsq : ∀ a, eS (algebraMap R S a) = algebraMap R' S' (eR a))
include hsq

theorem mem_under_iff (p : Ideal R') (q : Ideal S') [q.LiesOver p] (a : R) :
    a ∈ (q.comap eS).under R ↔ eR a ∈ p := by
  change eS (algebraMap R S a) ∈ q ↔ eR a ∈ p
  exact (Iff.of_eq (congrArg (fun z => z ∈ q) (hsq a))).trans
    (Ideal.mem_of_liesOver q p (eR a)).symm

theorem map_extended_ideal (p : Ideal R') :
    ((p.comap eR).map (algebraMap R S)).map eS = p.map (algebraMap R' S') := by
  have h : eS.toRingHom.comp (algebraMap R S) =
      (algebraMap R' S').comp eR.toRingHom := RingHom.ext hsq
  change ((p.comap eR.toRingHom).map (algebraMap R S)).map eS.toRingHom = _
  rw [Ideal.map_map, h, ← Ideal.map_map,
    Ideal.map_comap_of_surjective eR.toRingHom eR.surjective]

theorem powerIndex_eq (p : Ideal R') (q : Ideal S') :
    (p.comap eR).ramificationIdx' (q.comap eS) = p.ramificationIdx' q := by
  unfold Ideal.ramificationIdx'
  congr 1
  ext n
  change (p.comap eR).map (algebraMap R S) ≤ (q.comap eS) ^ n ↔
    p.map (algebraMap R' S') ≤ q ^ n
  rw [← eS.idealComapOrderIso.symm.le_iff_le]
  change ((p.comap eR).map (algebraMap R S)).map eS ≤ ((q.comap eS) ^ n).map eS ↔ _
  rw [map_extended_ideal eR eS hsq, Ideal.map_pow,
    Ideal.map_comap_of_surjective _ eS.surjective]

theorem ramificationIdx_eq [IsDedekindDomain S] [IsDedekindDomain S']
    (p : Ideal R') (q : Ideal S') [q.IsPrime] [q.LiesOver p]
    (hp : p.map (algebraMap R' S') ≠ ⊥) :
    (q.comap eS).ramificationIdx R = q.ramificationIdx R' := by
  have : (q.comap eS).LiesOver (p.comap eR) := ⟨by
    ext a
    change eR a ∈ p ↔ eS (algebraMap R S a) ∈ q
    rw [hsq]
    exact Ideal.mem_of_liesOver q p (eR a)⟩
  have hp₀ : (p.comap eR).map (algebraMap R S) ≠ ⊥ := by
    intro h
    apply hp
    rw [← map_extended_ideal eR eS hsq p, h, Ideal.map_bot]
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx' (p.comap eR) (q.comap eS) hp₀,
    ← Ideal.ramificationIdx'_eq_ramificationIdx' p q hp]
  exact powerIndex_eq eR eS hsq p q

end
end JoshiTeich.Act1Scene1.RamificationEquivSquare
