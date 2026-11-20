# SL₂ image from the local Tate theorem

## 简体中文

- `prime_dvd_card_range_from_source` 适用于数域 $F$ 上任意带有给定曲线算术记录、泰特输入和模 $\ell$ 表示 $\rho_\ell$ 的椭圆曲线，$\ell$ 为奇素数。(P5) 给出乘法约化处 $w$，其剩余特征既不为 $2$ 也不为 $\ell$。(P2) 保证在每个乘法约化处，$\ell$ 都不整除当地泰特参数的阶。特别地，$\ell\nmid\operatorname{ord}_w(q_w)$。取 $\ell$-挠点域 $L$ 中位于 $w$ 上方的有限处 $w'$。局部泰特定理给出 $\ell\mid e(w'/w)$。该分歧指数整除 $|\operatorname{Gal}(L/F)|$，后者等于 $|\operatorname{im}\rho_\ell|$。因此 $\ell\mid|\operatorname{im}\rho_\ell|$。
- `sl_le_range_of_from_source` 取素数 $\ell\ge5$，并假设 (P2)、(P4)、(P5)。素数 $\ell\ge5$ 为奇数，因此第一条结论适用。由柯西定理，像中存在阶为 $\ell$ 的元素 $T$。它满足 $T\ne I$ 和 $(T-I)^2=0$。(P4) 排除伽罗瓦稳定的 $\ell$ 阶循环子群，因此像没有不变直线。群生成引理给出任意 $A\in\mathrm{SL}_2(\mathbb F_\ell)$ 都经 `A.toGL` 落入表示的像。
- `sl2Image_from_source` 对任意供应器 $P$ 和任意三脚点 $x$，把 (P2) 和 (P5) 从 `(P.localData x).bad` 转到同一条曲线的 `badAll`。在这些处，局部数据的 `hv` 就是泰特参数的阶，`p` 就是剩余特征。该定理把第二条结论用于 `P.curve x`、`P.arith x`、`P.tate x` 和 `P.modRep x ℓ hℓ`，得到 `SL2ImageHyp P`。`curveInputs_from_source` 通过 `curveInputsOfSL2Image` 使用该证明来填写 `sl2_of` 字段。

## English

- `prime_dvd_card_range_from_source` applies to any elliptic curve over a number field $F$ with the given curve arithmetic and Tate inputs. Let $\rho_\ell$ be the supplied mod-$\ell$ representation for an odd prime $\ell$. Condition (P5) gives a place $w$ of multiplicative reduction whose residue characteristic differs from $2$ and $\ell$. By (P2), $\ell$ divides none of the Tate parameter orders at places of multiplicative reduction. In particular, $\ell\nmid\operatorname{ord}_w(q_w)$. Choose a place $w'$ of the $\ell$-torsion field $L$ above $w$. The local Tate theorem gives $\ell\mid e(w'/w)$. This ramification index divides $|\operatorname{Gal}(L/F)|$, which equals $|\operatorname{im}\rho_\ell|$. Thus $\ell\mid|\operatorname{im}\rho_\ell|$.
- `sl_le_range_of_from_source` assumes that $\ell$ is prime, $\ell\ge5$, and (P2), (P4), and (P5) hold. The prime $\ell\ge5$ is odd, so the first theorem applies. Cauchy’s theorem gives an element $T$ of order $\ell$ in the image. It satisfies $T\ne I$ and $(T-I)^2=0$. Condition (P4) rules out a Galois-stable cyclic subgroup of order $\ell$, so the image preserves no line. The generation lemma puts every $A\in\mathrm{SL}_2(\mathbb F_\ell)$ in the image via `A.toGL`.
- For every provider $P$ and tripod point $x$, `sl2Image_from_source` transfers (P2) and (P5) from `(P.localData x).bad` to `badAll` for the same curve. At these places, `hv` gives the Tate parameter order and `p` gives the residue characteristic. The proof applies the SL₂ inclusion to `P.curve x`, `P.arith x`, `P.tate x`, and `P.modRep x ℓ hℓ` to establish `SL2ImageHyp P`. The constructor `curveInputs_from_source` passes the proof to `curveInputsOfSL2Image` to fill the `sl2_of` field.

## 日本語

- `prime_dvd_card_range_from_source` は、曲線の算術データ、テイト入力、および奇素数 $\ell$ に対する法 $\ell$ の表現 $\rho_\ell$ が与えられた、数体 $F$ 上の任意の楕円曲線に適用できる。(P5) により、剰余標数が $2$ とも $\ell$ とも異なる乗法的還元の素点 $w$ を取る。(P2) により、$\ell$ は各乗法的還元の素点におけるテイトパラメータの位数を割り切らない。特に $\ell\nmid\operatorname{ord}_w(q_w)$ が成り立つ。$\ell$-捩れ点体 $L$ で $w$ の上にある素点 $w'$ を取る。局所テイト定理により $\ell\mid e(w'/w)$ が成り立つ。この分岐指数は $|\operatorname{Gal}(L/F)|$ を割り切り、このガロア群の位数は $|\operatorname{im}\rho_\ell|$ に等しい。したがって $\ell\mid|\operatorname{im}\rho_\ell|$ が成り立つ。
- `sl_le_range_of_from_source` は、$\ell\ge5$ の素数 $\ell$ について (P2)、(P4)、(P5) を仮定する。素数 $\ell\ge5$ は奇数なので、最初の定理を適用できる。コーシーの定理により、像は位数 $\ell$ の元 $T$ を含む。この元は $T\ne I$ と $(T-I)^2=0$ を満たす。(P4) によりガロア作用で安定な位数 $\ell$ の巡回部分群が存在しないため、像が保つ直線はない。群の生成に関する補題により、任意の $A\in\mathrm{SL}_2(\mathbb F_\ell)$ は `A.toGL` を通じて表現の像に属する。
- 任意の供給データ $P$ と 三脚の点 $x$ に対し、`sl2Image_from_source` は (P2) と (P5) を `(P.localData x).bad` から同じ曲線の `badAll` に移す。これらの素点において、`hv` はテイトパラメータの位数、`p` は剰余標数を与える。`P.curve x`、`P.arith x`、`P.tate x`、`P.modRep x ℓ hℓ` に特殊線形群の包含を適用し、`SL2ImageHyp P` を得る。`curveInputs_from_source` はこの証明を `curveInputsOfSL2Image` に渡し、`sl2_of` フィールドを与える。

[Adapted divisibility proof](../../../../Solutions/Source_SL2ImageFromSource.lean#L21) · [Adapted image inclusion](../../../../Solutions/Source_SL2ImageFromSource.lean#L33) · [Tripod proof](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L23) · [Tripod constructor](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L40)

[iut divisibility proof](../../../../../refer/iut/Iut/Concrete/SL2Image.lean#L217) · [iut image inclusion](../../../../../refer/iut/Iut/Concrete/SL2Image.lean#L229) · [iut tripod proof](../../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L442) · [iut tripod constructor](../../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L492)
