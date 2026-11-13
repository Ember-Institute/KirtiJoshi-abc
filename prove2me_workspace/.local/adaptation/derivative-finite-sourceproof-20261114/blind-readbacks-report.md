Independent blind readback of the three specified Lean source files produced nine declaration rows in `readbacks.json`: six adjoin theorems, two localization theorems, and the final finite-bad-place theorem. There are no source-level private declarations or instances in these files. Section hypotheses are explicitly included in each static full signature. These signatures are reconstructed from source, not obtained from Lean elaboration.

The readback used only the supplied Lean files and imported Lean definitions and proofs in the main workspace. It did not use a README, ledger, external source prose, network access, compiler, MCP-CI, repository mutation, or cache mutation. Lean comments claiming a pinned upstream source were not used as mathematical evidence or independently authenticated. All nine declarations contain proof bodies that reuse imported constructions and lemmas. Their presence is not a compilation or axiom-audit receipt.

The construction behind the new extension compatibility theorem is concrete. For a compatible scalar tower R → S → T with T formally étale over S, the imported extension sends the universal Kähler differential of T through the inverse of the base-change equivalence and then through the base-changed linear map associated to the original derivation. The new equality says that restriction along S → T recovers the original derivation. This is not an assumed extension law.

The actual `derivAlong t` checks `Transcendental ℚ t ∧ Algebra.IsAlgebraic ℚ⟮t⟯ K`. Its positive branch extends actual polynomial differentiation on `Algebra.adjoin ℚ {t}` by this Kähler construction; its negative branch is zero. The new evaluation theorem has precisely the hypotheses needed for the positive branch. The polynomial-adjoin membership theorem uses the stronger finite-dimensional hypothesis, together with membership of ℚ and t in the valuation ring, to evaluate a derivative polynomial in that ring. It does not yet show preservation of an entire place.

The first localization theorem takes an actual finite set G in `chartRing t` and an actual spanning equality over `Algebra.adjoin ℚ {t}`. It uses submodule-span induction. In its scalar step the Leibniz rule requires both a scalar and its derivative in the valuation ring, as well as membership of a chart element; those facts come from the adjoin theorems and the actual chart-ring inclusion in the place. This theorem assumes the finite spanning set. The final theorem obtains one from `Module.Finite.fg_top` and the imported finite-module instance for the integral closure chart ring.

The second localization theorem is tied to the actual place P and the associated height-one prime `P.toChart t htP`. The equality `Place.ofChart_toChart` identifies P with the localization of the chart ring at that prime. A local element therefore has the form a/u, with a and u in the chart ring and u outside the associated prime. The membership equivalence turns this last condition into nonmembership in `P.1.nonunits`. The valuation-subring criterion then supplies nonzero u and membership of u⁻¹ in P.1. The quotient-rule expression is `(u⁻¹)^2 * (u * D(a) - a * D(u))`. Each factor belongs to P.1. The denominator is a unit of this specific local ring; no arbitrary denominator is assumed invertible in the local ring.

The final theorem states exactly

```lean
{P : Place M.K | ψ ∈ P.1 ∧
  ∃ s ∈ P.1, CurveDeriv.derivAlong ψ s ∉ P.1}.Finite
```

The place type is the full subtype of proper valuation subrings containing ℚ. The theorem preserves the condition ψ ∈ P.1; it makes no assertion about derivative preservation at places that do not contain ψ. The supplied `Model N` already contains the Fermat field presentation, transcendental coordinate, finite extension, and degree data. `M.isCurveField` follows from that data, and finiteness over ℚ(ψ) follows for every transcendental ψ. The theorem assumes a model and does not construct one.

The proof obtains a finite ℚ[ψ]-module generating set G for the integral closure chart ring. For each g ∈ G it uses the already proved finiteness of the actual pole set `{P | derivAlong ψ g ∉ P.1}`. The displayed set is a subset of their finite union: membership at all generator derivatives implies membership on the whole chart ring, and then on the whole local ring by the localization theorem. There is no parameter D, no assumed derivative law, and no assumed finite exceptional boundary. Import reuse is mathematical proof reuse, not a fresh compilation certificate.

All three language fields in every row are independently stated with their hypotheses and conclusion. Simplified Chinese mathematical terms are used in `zh_Hans`, with human names such as Kähler, Leibniz, and Fermat retained in Latin script. Japanese uses standard mathematical terms such as ケーラー微分, 導分, 形式的エタール, 整閉包, 付値部分環, 素イデアル, 単元, and 局所化. All quotation fields are null pending the root agent's separate Mochizuki geometry-context review.

No compilation, elaboration, scheduler receipt, axiom audit, or whole-project acceptance is claimed. Static JSON and declaration coverage checks were performed on the output artifacts only.
