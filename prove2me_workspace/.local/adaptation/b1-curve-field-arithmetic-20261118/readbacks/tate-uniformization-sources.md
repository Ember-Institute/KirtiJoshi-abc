# Tate uniformization proof sources

The Tate proofs use `lana-agents/tate-curves-theta` at `ca6c2279d3cea0690cdb01328e727118d5485d68`. The project lock pins Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474` and Lean to `v4.33.1`. The local migration patch changes the proof of `toAnalyticQuotient_q_mul` in `TateCurve/Quotient.lean`. [Project lock](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/migration/environment.lock.json) · [Migration patch](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/migration/patches/tate-curves-theta-lean433.patch)

| Prove2Me declaration | Upstream declaration in `TateCurvesTheta.TateParameter` | Proof and hypotheses |
| --- | --- | --- |
| `tatePoint_equation` | `tatePoint_mem'` in `TatePointOnCurve.lean`, Christian Merten, `441eaa7e0c4b8be6e147ecedd9b06bb5e004b302` | The Weierstrass defect vanishes off the orbit of `q`. The theorem uses `(12 : k) ≠ 0`. [Point equation](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta/TateCurvesTheta/TateCurve/TatePointOnCurve.lean:334) |
| `tatePoint_mul` | `tatePoint_mul` in `GroupLaw.lean`, Christian Merten, `6e48c9c31299a995332539768711796b40d1894a` | The orbit cases use periodicity and inversion. The general case uses a translating unit and the secant law. The theorem uses `TameResidueChar k` and classical decidable equality. [Group law](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta/TateCurvesTheta/TateCurve/GroupLaw.lean:242) |
| `tatePoint_surjective` | `tatePoint_surjective` in `TateUniformization.lean`, Christian Merten, `6e48c9c31299a995332539768711796b40d1894a` | The proof separates affine points by `‖x‖ < 1`, `‖x‖ = 1`, and `1 < ‖x‖`. The theorem uses `TameResidueChar k`. [Surjectivity](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta/TateCurvesTheta/TateCurve/TateUniformization.lean:55) |

The bridge builds an upstream `TateParameter` from the Prove2Me parameter's `q` and `norm_lt_one`. The Weierstrass coefficients and coordinate series have the same definitions. The two point maps use the same orbit test, and Lean identifies their nonsingularity proofs by proof irrelevance. The `h2` and `h12` arguments match the two fields of `TameResidueChar`. [Point-law bridge](../../../../Solutions/Source_ReferenceIutTateUniformizationLaws.lean#L29) · [Tame residue characteristic](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta/TateCurvesTheta/TateCurve/A6Series.lean:71)

`TateParameterUniformization.ofTateParameter` gives all three laws to `ofTatePoint`. `prime_dvd_ramificationIdx_from_source` passes this uniformization to `tateStructureOfBadPlace`. [Provider](../../../../Solutions/Source_ReferenceIutTateUniformizationLaws.lean#L67) · [Ramification proof](../../../../Solutions/Source_SL2ImageLocalTate.lean#L81)

## Compiled imports

The bridge imports `TateCurvesTheta.TateCurve.TateUniformization` and `Solutions.Source_ReferenceIutTateUniformization`. The Tate import reaches all three proofs. Include the following directory in the Prove2Me `LEAN_PATH` for the cached import.

```text
/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta/.lake/build/lib/lean
```

The Tate source import closure has 51 modules. All 51 have `.olean` files whose headers identify Lean `4.33.1`, build `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The three root artifacts contain the declaration names. MCP-CI job `ci-020624-9ee61ed1` compiled the bridge successfully. [Build receipt](../receipts/local-tate-ci-020624-9ee61ed1-result.json)

The entries below give the exact Tate import edges. Each module name has the prefix `TateCurvesTheta.`. The `TatePointOnCurve` closure has 27 modules. The `GroupLaw` closure has 47 modules and includes `TatePointOnCurve`. The `TateUniformization` closure includes both.

```text
Analysis.MaxTerm
Analysis.Strassmann -> Analysis.MaxTerm, Analysis.UltrametricSum
Analysis.StrassmannSphere -> Analysis.MaxTerm, Analysis.UltrametricSum, Analysis.Strassmann
Analysis.UltrametricSum
AnalyticQuotient
Arithmetic.DivisorConvolution
QParameter.BaseChange -> QParameter.Basic
QParameter.Basic
TateCurve.A6Series -> TateCurve.Weierstrass
TateCurve.AbelStep -> TateCurve.DefectCoeffBaseChange, Theta.PuncturedProduct, Theta.WeightSpace
TateCurve.AdditionLaw -> TateCurve.CoordinateInversion, TateCurve.PointMap, TateCurve.TatePointOnCurve
TateCurve.CoordinateAnnulusLaurent -> TateCurve.CoordinateExpansion
TateCurve.CoordinateAnnulusLaurentY -> TateCurve.CoordinateExpansion
TateCurve.CoordinateExpansion -> TateCurve.Parametrization
TateCurve.CoordinateInversion -> TateCurve.EisensteinKernels, TateCurve.Parametrization
TateCurve.DefectAnnulusLaurent -> TateCurve.CoordinateAnnulusLaurent, TateCurve.CoordinateAnnulusLaurentY, TateCurve.WeierstrassIdentity, Theta.ThetaProdGlobalLaurent
TateCurve.DefectCoeffBaseChange -> QParameter.BaseChange, TateCurve.TatePointOnCurve
TateCurve.DefectVanishing -> TateCurve.EisensteinKernels, TateCurve.WeierstrassIdentity, Theta.ThetaProdGlobalLaurent, Theta.Uniqueness
TateCurve.Discriminant -> TateCurve.A6Series
TateCurve.EisensteinKernels
TateCurve.EisensteinSeries -> TateCurve.EisensteinKernels, TateCurve.Weierstrass
TateCurve.GroupLaw -> TateCurve.AbelStep, TateCurve.AdditionLaw, TateCurve.LargePointParametrization
TateCurve.IntegralModel -> TateCurve.A6Series, TateCurve.Discriminant
TateCurve.LargePointParametrization -> TateCurve.CoordinateInversion, TateCurve.IntegralModel, TateCurve.TatePointOnCurve
TateCurve.Parametrization -> TateCurve.Weierstrass
TateCurve.PointMap -> TateCurve.Discriminant, TateCurve.WeierstrassIdentity, TateCurve.Quotient
TateCurve.Quotient -> AnalyticQuotient, QParameter.Basic
TateCurve.SphereBounds -> TateCurve.Discriminant, TateCurve.Parametrization
TateCurve.SurjectivityAnnulus -> TateCurve.GroupLaw, TateCurve.SphereBounds
TateCurve.SurjectivitySphere -> TateCurve.GroupLaw, TateCurve.SphereBounds
TateCurve.TatePointMem -> TateCurve.WeierstrassIdentity, Theta.Uniqueness
TateCurve.TatePointOnCurve -> Analysis.StrassmannSphere, Arithmetic.DivisorConvolution, TateCurve.DefectAnnulusLaurent, TateCurve.DefectVanishing, TateCurve.EisensteinSeries, TateCurve.TatePointMem, Theta.LaurentSphere
TateCurve.TateUniformization -> TateCurve.SurjectivityAnnulus, TateCurve.SurjectivitySphere
TateCurve.Weierstrass -> QParameter.Basic
TateCurve.WeierstrassIdentity -> TateCurve.Parametrization
Theta.Basic -> QParameter.Basic
Theta.Divisor -> Theta.Product
Theta.Durfee -> Theta.Normalization, Theta.QBinomial, Theta.Divisor
Theta.FactorSeries -> Theta.Product
Theta.LaurentSphere -> Theta.Uniqueness
Theta.LaurentSphereReduce -> Theta.LaurentSphere
Theta.LaurentUnitSphere -> Analysis.StrassmannSphere, Theta.LaurentSphereReduce, Theta.LaurentSphere
Theta.Normalization -> Theta.ThetaProdGlobalLaurent, Theta.LaurentUnitSphere
Theta.Periodicity -> Theta.Basic
Theta.Product -> Theta.Periodicity
Theta.PuncturedProduct -> TateCurve.Parametrization, Theta.Durfee, Theta.ThetaProdGlobalLaurent
Theta.QBinomial
Theta.ThetaProdGlobalLaurent -> Theta.FactorSeries, Theta.ThetaProdLaurent
Theta.ThetaProdLaurent -> Theta.Uniqueness, Theta.Divisor
Theta.Uniqueness -> Theta.Product
Theta.WeightSpace -> Theta.Durfee, Theta.LaurentUnitSphere, Theta.Periodicity, Theta.ThetaProdGlobalLaurent
```

The 51 Tate modules import these 38 Mathlib modules directly. All 38 have cached artifacts for Lean `4.33.1`. `AnalyticQuotient` imports the `Mathlib` umbrella.

```text
Mathlib
Mathlib.Algebra.BigOperators.Intervals
Mathlib.Algebra.BigOperators.NatAntidiagonal
Mathlib.Algebra.BigOperators.Ring.Finset
Mathlib.Algebra.Polynomial.Eval.Coeff
Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
Mathlib.Analysis.Normed.Field.Basic
Mathlib.Analysis.Normed.Field.Lemmas
Mathlib.Analysis.Normed.Field.Ultra
Mathlib.Analysis.Normed.Group.InfiniteSum
Mathlib.Analysis.Normed.Group.Tannery
Mathlib.Analysis.Normed.Group.Ultra
Mathlib.Analysis.Normed.Module.Basic
Mathlib.Analysis.Normed.Ring.InfiniteSum
Mathlib.Analysis.Normed.Ring.Ultra
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.SpecialFunctions.Log.Basic
Mathlib.Analysis.SpecialFunctions.Log.Summable
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecificLimits.Basic
Mathlib.Analysis.SpecificLimits.Normed
Mathlib.Data.Nat.Choose.Basic
Mathlib.Data.ZMod.Basic
Mathlib.FieldTheory.KummerPolynomial
Mathlib.LinearAlgebra.FiniteDimensional.Basic
Mathlib.NumberTheory.Divisors
Mathlib.NumberTheory.TsumDivisorsAntidiagonal
Mathlib.Order.Filter.AtTopBot.Ring
Mathlib.RingTheory.AdjoinRoot
Mathlib.Tactic.FieldSimp
Mathlib.Tactic.Linarith
Mathlib.Tactic.LinearCombination
Mathlib.Tactic.Ring
Mathlib.Topology.Algebra.InfiniteSum.NatInt
Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
Mathlib.Topology.Algebra.InfiniteSum.Ring
```
