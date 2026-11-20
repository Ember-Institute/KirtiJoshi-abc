The three readbacks cover the integrated curve height fields. They contain English, Simplified Chinese, and Japanese sections. The Chinese readbacks use 紧致有界子集 for “compactly bounded subset” according to TERM-016. The Japanese コンパクト有界部分集合 is formed by analogy with the English compound and follows the earlier Statement II readback.

Precise inputs and outputs:

| Declaration | Required inputs | Output scope |
|---|---|---|
| `DiscrepancyEquiv.ge` | A type `α`, functions `f,g : α → ℝ`, a set `s`, and a proof `f ≈[s] g` | The second one-sided bound `g ≲[s] f` |
| `NorthcottHyp` | No selected provider or compact set | A proposition quantifying over every `d : ℕ`, `H : ℝ` and all actual tripod points |
| `northcottHyp` | No theorem argument | Proof of `NorthcottHyp`, from current `boundedDegreeFiniteness` |
| `northcott` | `hN : NorthcottHyp`, `K`, `d`, `H` | Finiteness on `K.set ∩ ptLE d` with `htCan ≤ H` |
| `northcott_of_equiv` | `hN`, `K`, `d`, arbitrary `h : Pt → ℝ`, a proof `(1/6)h ≈[K.set] htCan`, and `H` | Finiteness on `K.set ∩ ptLE d` with `h ≤ H` |
| `curveInputs_htCan_equiv` | Actual `P : CurveProviders`, `K : CompactlyBounded` | The height comparison on all of `K`; `d` is unused and is not a theorem parameter |
| `curveInputs_height_eq` | Actual `P`, `K`, `d`, actual point `x` and membership `hx` | Definitional equality for the same `P.curve/P.arith/P.tate`; `hx` is unused in the proof |
| `curveInputs_northcott` | Actual `P`, `K`, `d`, arbitrary real `H` | Finite set of points of degree at most `d` and provider height at most `H` inside `K` |

The result types use `tripodTheory`'s actual point, set, degree restriction, and height. There is no replacement carrier, arbitrary provider-height field, fixed number field, or extra positivity assumption on H. `P` is required for all three field producers; the drafts do not produce `tripodProviders` or a complete `CurveInputs` object. The complete source structure in the `design/` file remains a source selection, not an imported declaration.

Precise source consumers:

1. `refer/iut/Iut/Tripod/CurveFacts.lean:498` selects `h := P.h`; line 503 assigns `height_eq`; line 508 assigns `htCan_equiv`; line 509 assigns `northcott := northcott_of_equiv hN K d hh`.
2. `refer/iut/Iut/Concrete/Existence.lean:402` declares `CurveInputs.height_eq`; line 408 declares `htCan_equiv`; line 410 declares `northcott`. `toCorollary22Inputs` at line 474 forwards these as `localData_height` at 477, `htCan_equiv` at 479, and `northcott` at 480.
3. `refer/iut/Iut/Implication/Corollary22.lean:404` uses `I.localData_height x hx` inside `Corollary22Inputs.c2`. This identifies the local-record height with the global `I.h x` used by its threshold and arithmetic estimates.
4. `refer/iut/Iut/Implication/Corollary23.lean:76` uses `Id.northcott H` to prove finiteness of the low-height part of the exceptional set. At line 100 it uses `Id.htCan_equiv.ge`, restricted to the complement of that set, to transfer the high-height estimate to the Weil height. The complete theorem still requires `I`, the matching theta-existence family, Chebyshev and prime-counting witnesses, and the universal `h312` family.
5. `refer/iut/Iut/Tripod/Main.lean:137`–`:142` is the actual source assembly: the constructor receives `northcottHyp` and `legendreHeight`, and its result is passed through `toCorollary22Inputs` into `statementII_of_cor312`.

Original paper context, Mochizuki only:

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position*, February 2009, Proposition 1.4(iv), printed and PDF page 6. [Official PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf). The local copy under `refer/Mochizuki/` has SHA-256 `b9dc115af61dca7fe434332ebafddf6a376a9e2926dad4e1ea2dcc0d2441f768`.

> (iv) Let $d$ be a positive integer, $C\in\mathbb R$. Suppose further that the line bundle $L_{\mathbb Q}$ is ample on $X_{\mathbb Q}$. Then the set of points $x\in X(\overline{\mathbb Q})^{\le d}$ [cf. Example 1.3, (i)] such that $\mathrm{ht}_L(x)\le C$ is finite.

Here the concrete Lean proof restricts to tripod points and uses their absolute logarithmic Weil height. The transfer to Tate height is the additional application of the actual provider comparison.

- *Arithmetic Elliptic Curves in General Position*, Definition 1.2(ii), local markdown lines 95–103: bounded discrepancy and the symmetric absolute-difference relation. IUT IV Remark 2.3.1(ii), local markdown line 1543, corrects the reversed one-sided symbols in that definition. The adapted `DiscrepancyLE` follows the corrected `f ≤ g + C` direction.
- The same GenEll paper, Example 1.3(ii), local markdown lines 121–133: the local domains and support used for a compactly bounded subset. The placeholders in the translations are retained intentionally.
- The same GenEll paper, Proposition 1.4(iv), local markdown line 155: points of bounded degree and bounded ample height form a finite set. This is the original height-finiteness context for the Northcott field. Its use here is uniform over varying fields of definition of bounded degree.
- *Inter-universal Teichmüller Theory IV*, Corollary 2.2(i), local markdown lines 1159–1167: the normalized degree of the local q-divisor and the comparison of its one-sixth multiple with the height of `ω_X(D)`. The surrounding statement includes the prime-2 support and bounded-j conditions; the selected code fields cover the all-primes height comparison and its Northcott consequence, not the complete corollary.
- IUT IV proof of Corollary 2.2(i), local markdown lines 1227–1239: comparison with the moduli height at infinity and its degree-six pullback. This explains the coefficient `1/6` in `htCan_equiv`.

The independent readbacks were prepared from the source drafts; target compilation and review are recorded in the adjacent source ledger.
