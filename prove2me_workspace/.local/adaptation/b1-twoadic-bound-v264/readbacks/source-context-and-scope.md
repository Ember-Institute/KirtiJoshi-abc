The reader drafts are `two-adic-bound.md` and `curve-inputs-consumers.md`, each with English, Simplified Chinese, and Japanese sections. They read the proposed Lean files in `/tmp/p2m-tripod-twoadic-bound-next-20261118` and preserve the Chinese placeholder `【译名待定：compactly bounded subset】`. All other Chinese and Japanese prose terms are translated, except mathematical personal names and exact code identifiers. No CI or workspace edits were performed.

Exact mathematical scope:

- `TwoAdicBoundHyp P K B` is `∀ x ∈ K.set, (P.localData x).heightEq 2 ≤ B`.
- `twoAdicBound` takes the actual `P : CurveProviders` and `K : CompactlyBounded`. Its statement has no point-degree parameter, selected-place input, variable prime, or externally chosen height function.
- `K.V` contains 2; its local bound is the actual `K.c`. Membership in `K.set` bounds the logarithmic absolute values of the actual generators at the required finite and infinite places. The proof obtains `K.c ≥ 0` from an actual point of `K`; it does not assume that every `K.c` is globally nonnegative.
- `P.localData x` uses exactly `P.curve x`, `P.arith x`, and `P.tate x`. The contributing set is all multiplicative places with residue characteristic 2. Its q-orders, residue degrees, and denominator are those of the same actual field `F_x`.
- `twoAdicBound'` proves the raw bound `4*K.c`. `twoAdicBound` weakens it to `max (4*K.c) 0`. If `K` is empty, the quantified height claim is vacuous and the chosen maximum remains nonnegative.
- `curveInputs_B_nonneg` takes `K` only. `curveInputs_heightEq_two_le` takes `P,K,d,x,hx`; `hx` is membership in the actual `tripodTheory` locus `K ∩ ptLE d`. The proof uses `hx.1` only, so the degree bound is a consumer-domain restriction, not an additional analytic hypothesis.

Exact original code anchors and consumers:

1. `refer/iut/Iut/Tripod/CurveFacts.lean:409`: `TwoAdicBoundHyp` definition. The source constructor chooses `B := max (4*K.c) 0` at line 510, proves nonnegativity at 511, and inserts `heightEq_two_le` at 512.
2. `refer/iut/Iut/Tripod/TwoAdic.lean:516`: local term bound; `:568`: finite-sum normalized bound `twoAdicBound'`; `:595`: exact requested root `twoAdicBound`.
3. `refer/iut/Iut/Concrete/Existence.lean:412`–`:417`: `CurveInputs.B`, `B_nonneg`, and `heightEq_two_le`. `toCorollary22Inputs` forwards all three at lines 481–483.
4. `refer/iut/Iut/Implication/Corollary22.lean:379`–`:380`: B appears in the height threshold. At line 453, `c2` uses `heightEq_two_le` in its contradiction to an ℓ-cyclic subgroup, bounding `h - heightEq 2` from below by `h-B`. At line 512 it uses the bound when proving a bad place exists away from 2 and ℓ. At lines 546–547 it restores the all-primes height from the contribution away from 2 and ℓ. The final conclusion at line 392 has additive term `40*pnt.η + B/3`.
5. `refer/iut/Iut/Implication/Corollary23.lean:80`: the statement-II argument uses additive constant `6*(40*pnt.η + B/3)` before scaling by one sixth.
6. `refer/iut/Iut/Tripod/Main.lean:139`: the actual source assembly passes `twoAdicBound _ K` into `curveInputs` beside the same provider's height comparison.

Mochizuki primary-paper context only:

- *Arithmetic Elliptic Curves in General Position*, Definition 3.3, local markdown line 381: local height is the positive valuation order of the Tate parameter. The preceding local setup, lines 349–361, fixes the local field and its surjective integer valuation. Local primary PDF: `/home/admin-wsl/Coq/abc/refer/Mochizuki/Arithmetic Elliptic Curves in General Position.pdf`.
- *Inter-universal Teichmüller Theory IV*, Corollary 2.2(i), local markdown lines 1159–1167: defines normalized q-divisor heights at all finite primes and away from 2, and states equality of their bounded-discrepancy classes. The surrounding hypotheses include support containing 2 and the bounded-j condition at 2. The proof at lines 1227–1233 uses that bounded-j condition for the difference.
- IUT IV, proof of Corollary 2.2(ii), local markdown line 1357: the difference between the one-sixth all-primes height and the one-sixth height away from 2 is bounded by a positive constant depending only on the specified subset. Lines 1359–1367 insert that constant into the final height inequality. Local primary PDF: `/home/admin-wsl/Coq/abc/refer/Mochizuki/Inter-universal Teichmuller Theory IV.pdf`.

Normalization must stay explicit. The paper's constant in the last passage bounds a difference already scaled by 1/6. The Lean field B bounds the unscaled `heightEq 2`. The drafts do not identify those two constants. They describe the same bounded prime-2 contribution with the exact scaling of the selected code. The paper does not supply the numerical constant `max(4*K.c,0)` in this passage; that explicit value comes from the selected local Lean proof.

The source packet retains full proof text for the analytic/local arithmetic chain. Its presence is a source draft, not a compiler receipt. The results do not construct the actual supplied provider, a full `CurveInputs`, the other arithmetic fields, or the universal Corollary 3.12 family.
