# Joshi II and the normalized witness on the selected P7 data

## English

### Normalized square coefficients

Write $j=1,\ldots,m$ for the Lean indices `Fin m` shifted by one, and put $a_j=(j/m)^2$. For every natural number $m>0$, the theorems `sum_normalized_squares` and `sum_normalized_square_root_logs` give

$$
\sum_{j=1}^m a_j=\frac{(m+1)(2m+1)}{6m},\qquad
\sum_{j=1}^m a_j\frac{qLog}{2(2m+1)}
=\frac{1}{12}\left(1+\frac1m\right)qLog.
$$

The second identity holds for every real `qLog`. When $qLog=\log|q|$ and $\ell=2m+1$, the factor $qLog/(2\ell)$ is the log norm of a $2\ell$-th root of $q$. This is the scalar calculation after `eq:val-rel-main2` in Joshi II, Theorem 9.2.1. [Lean identities](Source_JoshiIINormalizedSquareLogs.lean#L19) · [Joshi II](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:1147>)

For $m\ge2$, the sum of the $a_j$ is strictly less than $m$. The difference is $(m-1)(4m+1)/(6m)>0$. With $qLog<0$, multiplying by $qLog/(2\ell)$ reverses the inequality. The theorem `root_log_bound_lt_sum_normalized_square_root_logs` puts $m\,qLog/(2\ell)$ strictly below the second sum. The theorem `weighted_root_log_sum_lt_normalized_average` uses the same real place weights and root logs on both sides. It assumes the total $L_0=\sum_{v\in s}w_v r_v$ is negative. The average of the square-weighted sums factors as

$$
\frac1m\sum_{j=1}^m\sum_{v\in s}w_v a_j r_v=c_m L_0,
\qquad c_m=\frac{(m+1)(2m+1)}{6m^2}\in(0,1).
$$

Individual weights and logs can have either sign. [Single-log inequality](Source_JoshiIINormalizedSquareLogs.lean#L51) · [Finite-set inequality](Source_JoshiIINormalizedSquareLogs.lean#L64)

### Representatives and strict sign on P7

Fix `D : InitialThetaData`, `LT : LocalTheory D.Kt`, `TL : ThetaLocalData D LT`, and `QI : QPilotInputs D`. Let $F=D.F$ and let $M=\mathbb Q(j(D.E))$ be the moduli field inside $F$. Write $K_t=D.Kt$ for the $\ell$-torsion field, with $\ell=D.\ell$. The set $s=\texttt{QI.badModuliFinset}$ is the finite set of bad places of $M$. For each $v\in s$, let $u(v)$ be the place of $K_t$ selected over $v$ by `D.localData.sect.sectFin`. Write $d_v$ for its relative local degree over $v$ and $r_v=\log\|\texttt{TL.qroot}(u(v))\|$. The weight is $w_v=1/(d_v[M:\mathbb Q])$. The definition `normalizedWitnessLogAverage` takes the average above with those weights and logs and $m=(\ell-1)/2$. Denote its value by $A$. [Bad moduli places](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312QPilotModuli.lean:45) · [Witness definition](Source_JoshiIIP7NormalizedWitness.lean#L24)

Set `X = concreteVariantData D LT TL QI` and $L=\texttt{X.qPilot.lhs}=-\texttt{QI.qPilot.logQ}/(2\ell)$. The hypothesis `hModuli` identifies the given map $M\to K_t$ with the composite $M\to F\to K_t$. This is the compatibility recorded in `D.towerModK`. The representative formula then gives $L=L_0$. The sign proof uses `D.global.bad_nonempty` and a place of $F$ lying over one of the bad moduli places. The terms of `logQ` are positive because the place weight and Tate order are positive and the residue characteristic is prime. The nonempty support gives $\texttt{QI.qPilot.logQ}>0$, hence $L<0$. Since $D$ supplies $\ell\ge5$, we have $m\ge2$. The theorem `qPilot_lhs_lt_normalizedWitnessLogAverage` proves $L<A$. The factorization also gives $A=c_mL<0$. [Algebra tower](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Basic.lean:139) · [Representative formula](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312RepresentativeQPilot.lean:87) · [Sign proof](Source_JoshiIIP7NormalizedWitness.lean#L34) · [Strict comparison](Source_JoshiIIP7NormalizedWitness.lean#L58)

The source P7 predicate identifies $X$ with the bundle built at the selected point and prime $\ell\ge7$. Its local data use the witness that the $2$-torsion is rational. The same `QI` sets the bad residue characteristics and gives `X.qPilot`. The section and roots in the representative formula are those of this bundle. [Source P7 predicate](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodP7.lean:27) · [Concrete bundle](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:238)

### Required comparison with the hull volume

Put $R=\texttt{X.rhsData.rhs}$. Take the holomorphic hull of the theta-pilot region in each capsule. The procession average of the global log-volumes of those hulls is $R$. The theorem `corollary312Variant_of_normalizedWitnessLogAverage_le_rhs` takes `hModuli` and `hvolume`. The second hypothesis gives $A\le R$ for this same $X$. The proof composes

$$
L<A\le R
$$

to prove `Corollary312Variant X`, which asserts $L\le R$. Joshi II uses the local witness for a supremum of products of norms in its one-field setting. A connection to $R$ must give the stated comparison with the hull log-volume on $X$. [Hull log-volume](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_RightHandSide.lean:129) · [Conditional theorem](Source_JoshiIIP7NormalizedWitness.lean#L86) · [Joshi II](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:1147>)

For the project's concrete local theory, the existing hull-volume formula gives

$$
R=m^2 c_m L+\frac{m+3}{2}\log\pi.
$$

Thus $A\le R$ on that bundle asks for $(m^2-1)c_m(-L)\le \frac{m+3}{2}\log\pi$. The two new files leave this comparison as an input. The repository's rational Legendre family gives same-source P7 instances under its stated hypotheses with $R<L$. The strict witness comparison gives $A>R$ on those instances. [Concrete volume formula](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312GlobalVolume.lean:39) · [Coefficients](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312VolumeAggregation.lean:114) · [Source P7 counterexample](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFiveP7Counterexample.lean:59)

## 简体中文

### 归一化平方系数

把 Lean 的 `Fin m` 指标加一，记为 $j=1,\ldots,m$，并设 $a_j=(j/m)^2$。对每个正自然数 $m$，定理 `sum_normalized_squares` 和 `sum_normalized_square_root_logs` 给出

$$
\sum_{j=1}^m a_j=\frac{(m+1)(2m+1)}{6m},\qquad
\sum_{j=1}^m a_j\frac{qLog}{2(2m+1)}
=\frac{1}{12}\left(1+\frac1m\right)qLog.
$$

第二个等式适用于任意实数 `qLog`。当 $qLog=\log|q|$ 且 $\ell=2m+1$ 时，$qLog/(2\ell)$ 是 $q$ 的一个 $2\ell$ 次根的范数对数。这是 Joshi II 定理 9.2.1 在 `eq:val-rel-main2` 之后的标量计算。 [Lean 等式](Source_JoshiIINormalizedSquareLogs.lean#L19) · [Joshi II](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:1147>)

当 $m\ge2$ 时，$a_j$ 之和严格小于 $m$，差为 $(m-1)(4m+1)/(6m)>0$。若 $qLog<0$，乘以 $qLog/(2\ell)$ 会反转不等号。定理 `root_log_bound_lt_sum_normalized_square_root_logs` 给出 $m\,qLog/(2\ell)$ 严格小于第二个和式。定理 `weighted_root_log_sum_lt_normalized_average` 的两边使用同一组实数位权重与根的对数。其假设为总和 $L_0=\sum_{v\in s}w_v r_v<0$。平方加权和的平均值分解为

$$
\frac1m\sum_{j=1}^m\sum_{v\in s}w_v a_j r_v=c_m L_0,
\qquad c_m=\frac{(m+1)(2m+1)}{6m^2}\in(0,1).
$$

各个权重和对数可以取任意符号。 [单个对数的不等式](Source_JoshiIINormalizedSquareLogs.lean#L51) · [有限集不等式](Source_JoshiIINormalizedSquareLogs.lean#L64)

### P7 的代表位与严格符号

固定 `D : InitialThetaData`、`LT : LocalTheory D.Kt`、`TL : ThetaLocalData D LT` 和 `QI : QPilotInputs D`。记 $F=D.F$，模域 $M=\mathbb Q(j(D.E))$ 包含于 $F$。以 $K_t=D.Kt$ 表示 $\ell$-挠点域，其中 $\ell=D.\ell$。$s=\texttt{QI.badModuliFinset}$ 是 $M$ 上坏位的有限集。对每个 $v\in s$，令 $u(v)$ 为 `D.localData.sect.sectFin` 在 $K_t$ 中选在 $v$ 上方的位。记 $d_v$ 为 $u(v)$ 相对 $v$ 的局部次数，$r_v=\log\|\texttt{TL.qroot}(u(v))\|$，并取权重 $w_v=1/(d_v[M:\mathbb Q])$。定义 `normalizedWitnessLogAverage` 用这些权重和对数，并以 $m=(\ell-1)/2$ 取上述平均值，记所得值为 $A$。 [坏模域位](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312QPilotModuli.lean:45) · [见证均值的定义](Source_JoshiIIP7NormalizedWitness.lean#L24)

设 `X = concreteVariantData D LT TL QI`，$L=\texttt{X.qPilot.lhs}=-\texttt{QI.qPilot.logQ}/(2\ell)$。假设 `hModuli` 要求给定映射 $M\to K_t$ 等于复合映射 $M\to F\to K_t$。`D.towerModK` 记录了这一相容性。代表位公式据此给出 $L=L_0$。符号证明用 `D.global.bad_nonempty` 取得一个坏模域位，再取该位上方的 $F$ 的有限位。`logQ` 的每项均为正，因为位权重和 Tate 阶数为正，且剩余特征为素数。非空支撑给出 $\texttt{QI.qPilot.logQ}>0$，从而 $L<0$。$D$ 给出 $\ell\ge5$，所以 $m\ge2$。定理 `qPilot_lhs_lt_normalizedWitnessLogAverage` 证明 $L<A$。按系数分解又有 $A=c_mL<0$。 [域塔相容性](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Basic.lean:139) · [代表位公式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312RepresentativeQPilot.lean:87) · [符号证明](Source_JoshiIIP7NormalizedWitness.lean#L34) · [严格比较](Source_JoshiIIP7NormalizedWitness.lean#L58)

源 P7 谓词将 $X$ 等同于在所选点与素数 $\ell\ge7$ 处构造的数据包。其局部数据由 $2$-挠点有理性的见证构造。同一个 `QI` 设定坏剩余特征并给出 `X.qPilot`。代表位公式使用该数据包中的截面和根。 [源 P7 谓词](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodP7.lean:27) · [具体数据包](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:238)

### 所需的全纯包体积比较

设 $R=\texttt{X.rhsData.rhs}$。它先对每个胶囊的 theta-pilot 区域取全纯包并求全局对数体积，再按 procession 取平均。定理 `corollary312Variant_of_normalizedWitnessLogAverage_le_rhs` 接受 `hModuli` 和 `hvolume`。后一假设给出同一 $X$ 上的 $A\le R$。证明将

$$
L<A\le R
$$

合成为 `Corollary312Variant X`，即 $L\le R$。Joshi II 在单个局部域的设置中以局部见证估计范数乘积的上确界。要接到 $R$，仍需给出它与此处 $X$ 上全纯包对数体积的上述比较。 [全纯包对数体积](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_RightHandSide.lean:129) · [条件定理](Source_JoshiIIP7NormalizedWitness.lean#L86) · [Joshi II](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:1147>)

对项目的具体局部理论，已有的全纯包体积公式给出

$$
R=m^2 c_m L+\frac{m+3}{2}\log\pi.
$$

因此在该数据包上，$A\le R$ 等价于 $(m^2-1)c_m(-L)\le \frac{m+3}{2}\log\pi$。两份新文件把这一比较留作输入。仓库中的有理 Legendre 族在其陈述的假设下给出同源 P7 的 $R<L$ 实例。对这些实例，严格见证比较给出 $A>R$。 [具体体积公式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312GlobalVolume.lean:39) · [系数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312VolumeAggregation.lean:114) · [源 P7 反例](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFiveP7Counterexample.lean:59)

## 日本語

### 正規化した平方係数

Lean の `Fin m` の添字に $1$ を加えて $j=1,\ldots,m$ と書き、$a_j=(j/m)^2$ と置く。正の自然数 $m$ に対し、定理 `sum_normalized_squares` と `sum_normalized_square_root_logs` は次の等式を与える。

$$
\sum_{j=1}^m a_j=\frac{(m+1)(2m+1)}{6m},\qquad
\sum_{j=1}^m a_j\frac{qLog}{2(2m+1)}
=\frac{1}{12}\left(1+\frac1m\right)qLog.
$$

二つ目の等式は任意の実数 `qLog` に対して成り立つ。$qLog=\log|q|$ かつ $\ell=2m+1$ のとき、$qLog/(2\ell)$ は $q$ の $2\ell$ 乗根のノルムの対数である。これは Joshi II の定理 9.2.1 で `eq:val-rel-main2` に続くスカラー計算に当たる。 [Lean の等式](Source_JoshiIINormalizedSquareLogs.lean#L19) · [Joshi II](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:1147>)

$m\ge2$ では $a_j$ の和は $m$ より真に小さく、その差は $(m-1)(4m+1)/(6m)>0$ である。$qLog<0$ のとき、$qLog/(2\ell)$ を掛けると不等号の向きが反転する。定理 `root_log_bound_lt_sum_normalized_square_root_logs` は $m\,qLog/(2\ell)$ が二つ目の和より真に小さいことを与える。定理 `weighted_root_log_sum_lt_normalized_average` の両辺は、同じ実数値の素点の重みと根の対数を使う。仮定は全体の和 $L_0=\sum_{v\in s}w_v r_v<0$ である。平方重み付き和の平均は次のように因数分解できる。

$$
\frac1m\sum_{j=1}^m\sum_{v\in s}w_v a_j r_v=c_m L_0,
\qquad c_m=\frac{(m+1)(2m+1)}{6m^2}\in(0,1).
$$

個々の重みと対数の符号は任意である。 [単一対数の不等式](Source_JoshiIINormalizedSquareLogs.lean#L51) · [有限集合の不等式](Source_JoshiIINormalizedSquareLogs.lean#L64)

### P7 の代表素点と厳密な符号

`D : InitialThetaData`、`LT : LocalTheory D.Kt`、`TL : ThetaLocalData D LT`、`QI : QPilotInputs D` を固定する。$F=D.F$ とし、$M=\mathbb Q(j(D.E))$ を $F$ に含まれるモジュライ体とする。$\ell=D.\ell$ とし、$K_t=D.Kt$ を $\ell$-ねじれ体とする。$s=\texttt{QI.badModuliFinset}$ は $M$ の悪い素点の有限集合である。各 $v\in s$ に対し、`D.localData.sect.sectFin` が選ぶ $v$ の上の $K_t$ の素点を $u(v)$ とする。$u(v)$ の $v$ に対する局所拡大次数を $d_v$ とし、$r_v=\log\|\texttt{TL.qroot}(u(v))\|$、$w_v=1/(d_v[M:\mathbb Q])$ と置く。`normalizedWitnessLogAverage` はこの重みと対数を使い、$m=(\ell-1)/2$ として上の平均を取る。その値を $A$ とする。 [モジュライ体の悪い素点](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312QPilotModuli.lean:45) · [証人の平均の定義](Source_JoshiIIP7NormalizedWitness.lean#L24)

`X = concreteVariantData D LT TL QI` と置き、$L=\texttt{X.qPilot.lhs}=-\texttt{QI.qPilot.logQ}/(2\ell)$ とする。仮定 `hModuli` は、与えられた写像 $M\to K_t$ が合成 $M\to F\to K_t$ と等しいことを要求する。この両立性は `D.towerModK` に記録される。これにより代表素点の公式から $L=L_0$ が従う。符号の証明では `D.global.bad_nonempty` からモジュライ体の悪い素点を一つ取り、その上の $F$ の有限素点を取る。`logQ` の各項は、素点の重みとテイトパラメータの位数が正であり、剰余標数が素数であるため正である。台は空でないので $\texttt{QI.qPilot.logQ}>0$ となり、$L<0$ が従う。$D$ が $\ell\ge5$ を与えるので $m\ge2$ である。定理 `qPilot_lhs_lt_normalizedWitnessLogAverage` は $L<A$ を証明する。因数分解により $A=c_mL<0$ も従う。 [体の塔の両立性](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Basic.lean:139) · [代表素点の公式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312RepresentativeQPilot.lean:87) · [符号の証明](Source_JoshiIIP7NormalizedWitness.lean#L34) · [狭義不等式](Source_JoshiIIP7NormalizedWitness.lean#L58)

ソース P7 の述語は $X$ を、選ばれた点と素数 $\ell\ge7$ から構成したデータと同一視する。局所データは $2$-ねじれ点の有理性の証拠から構成する。同じ `QI` が悪い剰余標数を設定し、`X.qPilot` を与える。代表素点の公式は、同じデータの切断と根を使う。 [ソース P7 の述語](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodP7.lean:27) · [具体データ](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:238)

### 正則包の体積との比較

$R=\texttt{X.rhsData.rhs}$ とする。これは、カプセルごとにテータ・パイロット領域の正則包の大域対数体積を求め、procession 全体で平均した値である。定理 `corollary312Variant_of_normalizedWitnessLogAverage_le_rhs` は `hModuli` と `hvolume` を受け取る。後者は同じ $X$ 上で $A\le R$ を与える。証明では

$$
L<A\le R
$$

をつないで `Corollary312Variant X`、すなわち $L\le R$ を得る。Joshi II は一つの局所体の設定で、局所的な証人を使ってノルムの積の上限を評価する。$R$ につなぐには、この $X$ における正則包の対数体積との上記の比較が要る。 [正則包の対数体積](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_RightHandSide.lean:129) · [条件付き定理](Source_JoshiIIP7NormalizedWitness.lean#L86) · [Joshi II](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:1147>)

プロジェクトの具体的な局所理論では、既存の正則包の体積公式により

$$
R=m^2 c_m L+\frac{m+3}{2}\log\pi.
$$

したがって、このデータでの $A\le R$ は $(m^2-1)c_m(-L)\le \frac{m+3}{2}\log\pi$ と同値である。二つの新しいファイルでは、この比較を入力として受け取る。リポジトリの有理 Legendre 族は、記載の仮定の下で同じソース P7 に属する $R<L$ の例を与える。この場合、証人の狭義不等式から $A>R$ が従う。 [具体的な体積公式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312GlobalVolume.lean:39) · [係数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312VolumeAggregation.lean:114) · [ソース P7 の反例](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFiveP7Counterexample.lean:59)
