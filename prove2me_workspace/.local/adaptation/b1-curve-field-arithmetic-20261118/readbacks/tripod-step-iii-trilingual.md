# Step (iii) for the Legendre curve

## English

Let `P : CurveProviders` and `x : Pt`. The curve `P.curve x` is $E_\lambda\colon y^2=z(z-1)(z-\lambda)$ over its designated number field of definition. Its tripodal field is $F_{\mathrm{tpd}}=\mathbb Q(\lambda)$ and its field of moduli is $F_{\mathrm{mod}}=\mathbb Q(j(E_\lambda))$. Fix a prime $\ell\ge7$ whose mod-$\ell$ image contains $\mathrm{SL}_2(\mathbb F_\ell)$. At each finite place of multiplicative reduction, P2 requires that $\ell$ does not divide the Tate order. P5 requires one such place of residue characteristic outside $\{2,\ell\}$. Assume `AnabelianExistence AG TG` and `HasCoreUniversally AG (P.curve x).F (P.curve x).E`. The definitions `thetaDataOf` and `qPilotInputsOf` supply $D$ and `QI : QPilotInputs D` from that curve, representation, and Tate family. The theorem takes any `LT : LocalTheory.{0,v} D.Kt` and `TL : ThetaLocalData D LT`. [Curve of the point](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf.lean#L25) · [Step (iii) hypotheses](../../../../Solutions/Source_TripodTowerStepIII.lean#L25) · [Tripodal field of the Legendre curve](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldIdentification.lean#L82)

Let $K_t$ be the torsion field `D.Kt`. At each finite place $w$ of $K_t$, let $p$ be its residue characteristic. The tripodal place $u$ below $w$ is `placeTpd D.F D.E D.prime.torsionField w`. Write $e(w/u)$ for the relative ramification index. The theorem takes two local hypotheses.

- $v_p(e(w/u))\le\operatorname{wildConst}(\ell,p)$ for every $w$. The constant is $12,2,1,1$ at $2,3,5,\ell$, respectively, and $0$ elsewhere. [Wild constant](../../../../Solutions/Source_ReferenceIutTowerLocalFacts.lean#L26)
- $e(w/u)\le 30\ell$ for every $w$ with $p\notin\{2,3,5,\ell\}$. [Local bounds](../../../../Solutions/Source_TripodTowerStepIII.lean#L50)

The proof supplies the Galois instance for $F_{\mathrm{tpd}}/F_{\mathrm{mod}}$. For $p\notin\{2,3,5,\ell\}$, it proves $e(w/u)=1$ when no selected bad place of $D.F$ lies above $u$. It multiplies the two relative indices through $D.F$, each of which is $1$. It also supplies $e(u/u_0)\le2$ for each $u$ above a selected bad moduli place $u_0\in D.VBad$. The q-pilot gives finiteness of the bad places and a bad-place witness for every bad residue characteristic. [Galois instance](../../../../Solutions/Source_TripodTpdGalois.lean#L266) · [Index one](../../../../Solutions/Source_TripodUnramified.lean#L50) · [Index at most two](../../../../Solutions/Source_TripodTpdRamIdx.lean#L261) · [q-pilot interface](../../../../Solutions/Source_ReferenceIutThetaLocalBadChars.lean#L99)

The curve specialization packages both explicit bounds and the index-one fact as `TowerLocalFacts`. The sum proof uses its index-one field to transfer ramification outside the exceptional and bad moduli characteristics to $F_{\mathrm{tpd}}$. It bounds those primes by the different degree. It uses the ramification bound of $2$ and the conductor degree for the bad moduli characteristics outside $\{2,3,5,\ell\}$. The primes in $\{2,3,5,\ell\}$ contribute at most $5+\log\ell$. [Exceptional primes](../../../../Solutions/Source_ReferenceIutTowerStepIII.lean#L310) · [Construction of TowerLocalFacts](../../../../Solutions/Source_TripodTowerStepIII.lean#L62) · [Ramification transfer and sum bounds](../../../../Solutions/Source_ReferenceIutTowerStepIII.lean#L354)

Write $S$ for `(TL.withBadChars QI).dst`. It is the union of $\{2,3,5,\ell\}$, the q-pilot's bad residue characteristics, and the residue characteristics that ramify in $K_t$. Write $d_{\mathrm{mod}}=[F_{\mathrm{mod}}:\mathbb Q]$. The inequality from `step_iii_of_curve` is

$$
\sum_{p\in S}\log p
\le 2d_{\mathrm{mod}}\bigl(\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})+D.\mathrm{logConductorDeg}\bigr)+5+\log\ell.
$$

The different degree uses the absolute different of $F_{\mathrm{tpd}}$. The conductor degree sums the log norms of the selected bad tripodal places. Both degrees are normalized by $[F_{\mathrm{tpd}}:\mathbb Q]$. This is the Step (iii) field of `TowerArithmetic` for the local data `TL.withBadChars QI`. R4 and Step (ii) are the other two fields required by the pointwise P7 theorem. [Normalized degrees](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean#L22) · [Distinguished primes](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L62) · [Legendre Step (iii)](../../../../Solutions/Source_TripodTowerStepIII.lean#L46) · [Tower arithmetic](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L173)

The review reports only `propext`, `Classical.choice`, and `Quot.sound` for the audited declarations. [Legendre Step (iii) review](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021885-759d4e11-result.json) · [Reference tower construction](../../../../../refer/iut/Iut/Tripod/Tower.lean#L69)

## 中文

取 `P : CurveProviders` 和 `x : Pt`。`P.curve x` 是指定定义数域上的 Legendre 曲线 $E_\lambda\colon y^2=z(z-1)(z-\lambda)$。其三脚架域为 $F_{\mathrm{tpd}}=\mathbb Q(\lambda)$，模域为 $F_{\mathrm{mod}}=\mathbb Q(j(E_\lambda))$。固定素数 $\ell\ge7$，并假设模 $\ell$ 表示的像包含 $\mathrm{SL}_2(\mathbb F_\ell)$。P2 要求在曲线具有乘法约化的每个有限位，Tate 阶数均不被 $\ell$ 整除。P5 要求其中至少有一位的剩余特征在 $\{2,\ell\}$ 之外。另假设 `AnabelianExistence AG TG` 以及 `HasCoreUniversally AG (P.curve x).F (P.curve x).E`。`thetaDataOf` 与 `qPilotInputsOf` 用这条曲线、该表示和对应的 Tate 族给出 $D$ 和 `QI : QPilotInputs D`。定理接收任意 `LT : LocalTheory.{0,v} D.Kt` 与 `TL : ThetaLocalData D LT`。 [点的曲线](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf.lean#L25) · [步骤 (iii) 的假设](../../../../Solutions/Source_TripodTowerStepIII.lean#L25) · [Legendre 曲线的三脚架域](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldIdentification.lean#L82)

记 $K_t$ 为挠点域 `D.Kt`。对于 $K_t$ 的每个有限位 $w$，记其剩余特征为 $p$。$w$ 下方的三脚架域位 $u$ 由 `placeTpd D.F D.E D.prime.torsionField w` 给出，相对分歧指数记作 $e(w/u)$。定理显式接收两项局部假设。

- 对每个 $w$，有 $v_p(e(w/u))\le\operatorname{wildConst}(\ell,p)$。该常数在 $2,3,5,\ell$ 处依次取 $12,2,1,1$，其余处取 $0$。 [野分歧常数](../../../../Solutions/Source_ReferenceIutTowerLocalFacts.lean#L26)
- 对每个满足 $p\notin\{2,3,5,\ell\}$ 的 $w$，有 $e(w/u)\le30\ell$。 [局部分歧界](../../../../Solutions/Source_TripodTowerStepIII.lean#L50)

证明给出 $F_{\mathrm{tpd}}/F_{\mathrm{mod}}$ 的伽罗瓦实例。当 $p\notin\{2,3,5,\ell\}$ 且 $u$ 上方没有 $D.F$ 的所选坏位时，证明给出 $e(w/u)=1$。经过中间域 $D.F$ 的两个相对分歧指数都等于 $1$，其乘积即为 $e(w/u)$。对于每个 $u$，若它位于所选模域坏位 $u_0\in D.VBad$ 的上方，则 $e(u/u_0)\le2$。q-pilot 提供坏位的有限性，并为每个坏剩余特征给出相应的坏位。 [伽罗瓦实例](../../../../Solutions/Source_TripodTpdGalois.lean#L266) · [相对分歧指数为 1](../../../../Solutions/Source_TripodUnramified.lean#L50) · [相对分歧指数至多为 2](../../../../Solutions/Source_TripodTpdRamIdx.lean#L261) · [q-pilot 接口](../../../../Solutions/Source_ReferenceIutThetaLocalBadChars.lean#L99)

Legendre 特化将两项显式界和相对分歧指数为 1 的结论装入 `TowerLocalFacts`。求和证明使用其中分歧指数为 1 的字段，将例外素数和模域坏剩余特征以外的分歧下推到三脚架域，再用不同理想的次数控制其贡献。对于 $\{2,3,5,\ell\}$ 之外的模域坏剩余特征，证明使用分歧指数至多为 2 的界和导子次数。 $\{2,3,5,\ell\}$ 中的素数贡献至多为 $5+\log\ell$。 [例外素数](../../../../Solutions/Source_ReferenceIutTowerStepIII.lean#L310) · [塔局部条件的组装](../../../../Solutions/Source_TripodTowerStepIII.lean#L62) · [分歧下推及求和界](../../../../Solutions/Source_ReferenceIutTowerStepIII.lean#L354)

令 $S$ 为 `(TL.withBadChars QI).dst`。它是 $\{2,3,5,\ell\}$、q-pilot 的坏剩余特征集和在 $K_t$ 中分歧的有理素数集的并集。记 $d_{\mathrm{mod}}=[F_{\mathrm{mod}}:\mathbb Q]$，`step_iii_of_curve` 给出

$$
\sum_{p\in S}\log p
\le 2d_{\mathrm{mod}}\bigl(\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})+D.\mathrm{logConductorDeg}\bigr)+5+\log\ell.
$$

其中 `logDifferentDeg` 和 `logConductorDeg` 分别使用 $F_{\mathrm{tpd}}$ 的绝对不同理想和所选三脚架域坏位的对数范数之和，均除以 $[F_{\mathrm{tpd}}:\mathbb Q]$ 作归一化。这是局部数据取为 `TL.withBadChars QI` 时 `TowerArithmetic` 的步骤 (iii) 字段。R4 和步骤 (ii) 是逐点 P7 定理所需的另两个字段。 [归一化次数](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean#L22) · [指定素数集](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L62) · [Legendre 曲线的步骤 (iii)](../../../../Solutions/Source_TripodTowerStepIII.lean#L46) · [塔算术](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L173)

审查对受审声明只报告 `propext`、`Classical.choice` 和 `Quot.sound`。 [Legendre 步骤 (iii) 审查](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021885-759d4e11-result.json) · [参考塔算术构造](../../../../../refer/iut/Iut/Tripod/Tower.lean#L69)

## 日本語

`P : CurveProviders` と `x : Pt` を取る。`P.curve x` は、指定された定義体上の Legendre 曲線 $E_\lambda\colon y^2=z(z-1)(z-\lambda)$ である。三脚体は $F_{\mathrm{tpd}}=\mathbb Q(\lambda)$、モジュライ体は $F_{\mathrm{mod}}=\mathbb Q(j(E_\lambda))$ である。素数 $\ell\ge7$ を固定し、mod $\ell$ 表現の像が $\mathrm{SL}_2(\mathbb F_\ell)$ を含むと仮定する。P2 は、曲線が乗法的還元を持つ各有限素点で Tate 位数が $\ell$ で割り切れないことを要求する。P5 は、そのような素点のうち剰余標数が $\{2,\ell\}$ の外にあるものの存在を要求する。`AnabelianExistence AG TG` と `HasCoreUniversally AG (P.curve x).F (P.curve x).E` も仮定する。`thetaDataOf` と `qPilotInputsOf` は、この曲線、表現、および対応する Tate 族から $D$ と `QI : QPilotInputs D` を与える。定理は任意の `LT : LocalTheory.{0,v} D.Kt` と `TL : ThetaLocalData D LT` を受け取る。 [点に対応する曲線](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf.lean#L25) · [ステップ (iii) の仮定](../../../../Solutions/Source_TripodTowerStepIII.lean#L25) · [Legendre 曲線の三脚体](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldIdentification.lean#L82)

ねじれ点体 `D.Kt` を $K_t$ とする。$K_t$ の各有限素点 $w$ について、剰余標数を $p$ とする。$w$ の下にある三脚体の素点 $u$ は `placeTpd D.F D.E D.prime.torsionField w` で与えられる。相対分岐指数を $e(w/u)$ と書く。定理は二つの局所的な仮定を受け取る。

- すべての $w$ で $v_p(e(w/u))\le\operatorname{wildConst}(\ell,p)$ が成り立つ。この定数は $2,3,5,\ell$ でそれぞれ $12,2,1,1$ となり、それ以外で $0$ となる。 [野生分岐の定数](../../../../Solutions/Source_ReferenceIutTowerLocalFacts.lean#L26)
- $p\notin\{2,3,5,\ell\}$ を満たすすべての $w$ で $e(w/u)\le30\ell$ が成り立つ。 [局所分岐の評価](../../../../Solutions/Source_TripodTowerStepIII.lean#L50)

証明は $F_{\mathrm{tpd}}/F_{\mathrm{mod}}$ のガロア性のインスタンスを与える。$p\notin\{2,3,5,\ell\}$ で、$u$ の上に $D.F$ の指定された悪い素点がないとき、$e(w/u)=1$ が成り立つ。中間体 $D.F$ を経由する二つの相対分岐指数はともに $1$ であり、その積が $e(w/u)$ となる。モジュライ体の指定された悪い素点 $u_0\in D.VBad$ の上にある各 $u$ については、$e(u/u_0)\le2$ が成り立つ。q-pilot は、悪い素点が有限個であることと、各悪い剰余標数に対応する悪い素点の存在を与える。 [ガロア性](../../../../Solutions/Source_TripodTpdGalois.lean#L266) · [相対分岐指数が 1](../../../../Solutions/Source_TripodUnramified.lean#L50) · [相対分岐指数が 2 以下](../../../../Solutions/Source_TripodTpdRamIdx.lean#L261) · [q-pilot の定理](../../../../Solutions/Source_ReferenceIutThetaLocalBadChars.lean#L99)

Legendre 曲線への適用では、二つの明示的な評価と相対分岐指数が 1 であることを `TowerLocalFacts` にまとめる。対数和の証明は、その分岐指数が 1 であるという条件を使い、例外素数およびモジュライ体の悪い剰余標数を除いた分岐を三脚体へ移す。その寄与にはディファレントの次数を用いる。$\{2,3,5,\ell\}$ の外にあるモジュライ体の悪い剰余標数の寄与には、分岐指数が 2 以下という評価と導手の次数を用いる。 $\{2,3,5,\ell\}$ の素数の寄与は $5+\log\ell$ 以下である。 [例外素数](../../../../Solutions/Source_ReferenceIutTowerStepIII.lean#L310) · [体の塔の局所条件の構成](../../../../Solutions/Source_TripodTowerStepIII.lean#L62) · [分岐の移行と対数和の評価](../../../../Solutions/Source_ReferenceIutTowerStepIII.lean#L354)

$S$ を `(TL.withBadChars QI).dst` とする。これは $\{2,3,5,\ell\}$、q-pilot の悪い剰余標数、および $K_t$ で分岐する有理素数の和集合である。$d_{\mathrm{mod}}=[F_{\mathrm{mod}}:\mathbb Q]$ とすると、`step_iii_of_curve` は次の評価を与える。

$$
\sum_{p\in S}\log p
\le 2d_{\mathrm{mod}}\bigl(\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})+D.\mathrm{logConductorDeg}\bigr)+5+\log\ell.
$$

`logDifferentDeg` と `logConductorDeg` は、それぞれ $F_{\mathrm{tpd}}$ の絶対ディファレントと、指定された三脚体の悪い素点の対数ノルムの和を用いる。どちらも $[F_{\mathrm{tpd}}:\mathbb Q]$ で割って正規化する。これは、局所データが `TL.withBadChars QI` の場合の `TowerArithmetic` のステップ (iii) に当たる。R4 とステップ (ii) は、各点の P7 定理が要求する残り二つの条件である。 [正規化次数](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean#L22) · [指定された素数の集合](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L62) · [Legendre 曲線のステップ (iii)](../../../../Solutions/Source_TripodTowerStepIII.lean#L46) · [体の塔の算術](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L173)

レビューは、確認対象の宣言について `propext`、`Classical.choice`、`Quot.sound` のみを報告する。 [Legendre 曲線のステップ (iii) のレビュー](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021885-759d4e11-result.json) · [参照元の体の塔の構成](../../../../../refer/iut/Iut/Tripod/Tower.lean#L69)
