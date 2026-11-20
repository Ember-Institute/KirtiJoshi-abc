# Bad residue characteristics and step (iii) / 坏剩余特征与步骤 (iii) / 悪い剰余標数とステップ (iii)

## English

### `ThetaLocalData.withBadChars`

Fix anabelian geometry `AG`, its tempered geometry `TG`, and initial theta data `D : InitialThetaData AG TG`. Let $F$ be its field of definition, $E$ its elliptic curve, and $K_t$ its $\ell$-torsion field `D.Kt`, where $\ell=D.\ell$. Let $B=\mathrm{badPlacesOver}(D.F,D.E,D.VBad)$ be the set of finite places of $F$ above the selected bad places `D.VBad` of the field of moduli. The noncomputable construction takes `LT : LocalTheory.{u,v} D.Kt`, `TL : ThetaLocalData D LT`, and `QI : QPilotInputs D`. The input `QI` proves that $B$ is finite and that every finite place $w$ of $F$ has positive residue degree $f_w$. [Construction](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalBadChars.lean:49) · [Inputs to the q-pilot](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutQPilot.lean:28)

The result has type `ThetaLocalData D LT`. Its finite set of bad residue characteristics is $B_p=\{p_w\mid w\in B\}$, given by `QI.qPilot.badFinset.image residueChar`. Here $p_w$ is the residue characteristic of $w$. Every member of $B_p$ is prime and has a witness in $B$. For each finite place $v$ of $K_t$, the result uses the root `TL.qroot v` in $(K_t)_v$ if the residue characteristic of $v$ belongs to $B_p$. It uses $1$ otherwise. Write $r_v$ for this value. It is nonzero and has $\operatorname{ord}_p(r_v)\ge0$, where $p$ is the residue characteristic of $v$ and $\operatorname{ord}_p$ has $\operatorname{ord}_p(p)=1$. If $B$ is empty, all these roots are $1$. [Bad residue characteristics](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalBadChars.lean:26) · [Local theta data](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:49)

For every $w\in B$ and every $v$ above $w$, the residue characteristic of $v$ belongs to $B_p$. The comparison map $\iota_{w,v}\colon F_w\to(K_t)_v$ is `TL.embedF` for the given relation of places. Let $q_w$ be the Tate parameter at $w$, $\operatorname{qOrder}(w)$ its integer order, and $e_w$ the ramification index of $w$ over its rational prime. The result gives

$$
r_v^{2\ell}=\iota_{w,v}(q_w),\qquad
\operatorname{ord}_p(r_v)=\frac{\operatorname{qOrder}(w)}{2\ell e_w}.
$$

For each rational prime $p$ and each finite set of places with underlying set $B$, the result also gives the weighted identity

$$
\sum_{v\mid p}\frac{[(K_t)_v:\mathbb Q_p]}{[K_t:\mathbb Q]}\operatorname{ord}_p(r_v)
=\frac{1}{2\ell}\sum_{\substack{w\in B\\p_w=p}}\frac{f_w}{[F:\mathbb Q]}\operatorname{qOrder}(w).
$$

The left sum uses the fiber of `LT` over $p$ and its place weights. Both sides are zero if $p\notin B_p$. [Root identities and weighted sum](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:63) · [Construction of the weighted identity](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalBadChars.lean:74)

### `ThetaLocalData.step_iii_of_qPilotInputs`

Fix anabelian geometry `AG`, its tempered geometry `TG`, and `D : InitialThetaData AG TG`. Let $F=D.F$ with curve $E=D.E$, $K_t=D.Kt$, and $B$ be the finite places of $F$ above the selected bad moduli places `D.VBad`. Take `LT : LocalTheory.{u,v} D.Kt`, `TL : ThetaLocalData D LT`, and `QI : QPilotInputs D`. Its fields give the finiteness of $B$ and positive residue degrees at all finite places of $F$. Write $B_p$ for the residue characteristics of the places in $B$. Write $F_{\mathrm{mod}}$ for the field of moduli of $E$, $F_{\mathrm{tpd}}=D.\mathrm{tripodalField}$ for the tripodal field, and $d_{\mathrm{mod}}=[F_{\mathrm{mod}}:\mathbb Q]$. The prime $\ell$ is the prime in `D.prime`. The theorem takes `TowerLocalFacts D.E D.VBad D.prime`. For every finite place $v$ of $K_t$ with residue characteristic $p$, put $u$ for its restriction to $F_{\mathrm{tpd}}$ and $e(v/u)$ for the relative ramification index. The three fields require the following bounds. [Tower local facts](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerLocalFacts.lean:116)

- The $p$-adic order of $e(v/u)$ is at most $v_p(2^{12}\cdot3^2\cdot5)+\mathbf 1_{p=\ell}$.
- If $p\notin\{2,3,5,\ell\}$ and no $w\in B$ lies above $u$, then $e(v/u)=1$.
- If $p\notin\{2,3,5,\ell\}$, then $e(v/u)\le30\ell$.

The theorem also takes `RelRamIdxModLeTwo D.E D.VBad`, which requires $e(u/u_0)\le2$ for every finite place $u$ of $F_{\mathrm{tpd}}$ above a place $u_0\in D.VBad$ of $F_{\mathrm{mod}}$. The extension $F_{\mathrm{tpd}}/F_{\mathrm{mod}}$ must be Galois. `QI` and the image description of $B_p$ supply the finiteness of $B$ and a bad-place witness for each $p\in B_p$. [Relative ramification bound](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerLocalFacts.lean:108) · [Step (iii)](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalBadChars.lean:99)

For $S=(\mathrm{TL.withBadChars}\,\mathrm{QI}).\mathrm{dst}$, the conclusion is

$$
\sum_{p\in S}\log p
\le 2d_{\mathrm{mod}}\bigl(\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})+D.\mathrm{logConductorDeg}\bigr)
   +5+\log\ell.
$$

The finite set $S$ is the union of $\{2,3,5,\ell\}$, $B_p$, and the residue characteristics of the finite places of $K_t$ whose ramification index over $\mathbb Q$ differs from $1$. Each distinguished prime occurs once in the sum. The different degree is the log norm of the absolute different of $F_{\mathrm{tpd}}$ divided by $[F_{\mathrm{tpd}}:\mathbb Q]$. The conductor degree sums the log norms of the finite places of $F_{\mathrm{tpd}}$ below some $w\in B$ and divides by the same field degree. [Distinguished primes](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:62) · [Normalized degrees](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

## 简体中文

### `ThetaLocalData.withBadChars`

固定远 Abel 几何 `AG`、其缓和几何 `TG` 及初始 Θ 数据 `D : InitialThetaData AG TG`。记 $F$ 为定义数域，$E$ 为其中的椭圆曲线，$K_t$ 为 $\ell$ 挠点域 `D.Kt`，其中 $\ell=D.\ell$。$B=\mathrm{badPlacesOver}(D.F,D.E,D.VBad)$ 由 $F$ 上位于模域所选坏处 `D.VBad` 上方的有限处组成。该不可计算构造接收 `LT : LocalTheory.{u,v} D.Kt`、`TL : ThetaLocalData D LT` 和 `QI : QPilotInputs D`。`QI` 给出 $B$ 的有限性以及 $F$ 每个有限处 $w$ 的剩余次数 $f_w$ 的正性。 [构造](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalBadChars.lean:49) · [q-pilot 输入](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutQPilot.lean:28)

结果的类型为 `ThetaLocalData D LT`。坏剩余特征有限集为 $B_p=\{p_w\mid w\in B\}$，由 `QI.qPilot.badFinset.image residueChar` 给出，其中 $p_w$ 为 $w$ 的剩余特征。$B_p$ 的每个成员都是素数，且在 $B$ 中有一个见证。对 $K_t$ 的每个有限处 $v$，若 $v$ 的剩余特征在 $B_p$ 中，就在 $(K_t)_v$ 中取根 `TL.qroot v`，其余情形取 $1$。记该值为 $r_v$。它非零且满足 $\operatorname{ord}_p(r_v)\ge0$，这里 $p$ 为 $v$ 的剩余特征，赋值归一化为 $\operatorname{ord}_p(p)=1$。若 $B$ 为空，所有根均为 $1$。 [坏剩余特征](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalBadChars.lean:26) · [局部 Θ 数据](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:49)

对每个 $w\in B$ 及其上方每个 $v$，$v$ 的剩余特征都在 $B_p$ 中。完备化比较映射 $\iota_{w,v}\colon F_w\to(K_t)_v$ 由 `TL.embedF` 在该上覆关系处给出。记 $q_w$ 为 $w$ 处的 Tate 参数，$\operatorname{qOrder}(w)$ 为其整数阶，$e_w$ 为 $w$ 在有理素数上的分歧指数。结果给出

$$
r_v^{2\ell}=\iota_{w,v}(q_w),\qquad
\operatorname{ord}_p(r_v)=\frac{\operatorname{qOrder}(w)}{2\ell e_w}.
$$

对每个有理素数 $p$ 和每个底层集合为 $B$ 的有限处集，结果还给出加权恒等式

$$
\sum_{v\mid p}\frac{[(K_t)_v:\mathbb Q_p]}{[K_t:\mathbb Q]}\operatorname{ord}_p(r_v)
=\frac{1}{2\ell}\sum_{\substack{w\in B\\p_w=p}}\frac{f_w}{[F:\mathbb Q]}\operatorname{qOrder}(w).
$$

左端使用 `LT` 在 $p$ 上的纤维和处权重。当 $p\notin B_p$ 时，两侧均为零。 [根的等式与加权求和](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:63) · [加权恒等式的构造](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalBadChars.lean:74)

### `ThetaLocalData.step_iii_of_qPilotInputs`

固定远 Abel 几何 `AG`、其缓和几何 `TG` 和 `D : InitialThetaData AG TG`。记 $F=D.F$、$E=D.E$、$K_t=D.Kt$，$B$ 为 $F$ 上覆于模域所选坏处 `D.VBad` 的有限处集。取 `LT : LocalTheory.{u,v} D.Kt`、`TL : ThetaLocalData D LT` 和 `QI : QPilotInputs D`。最后一项给出 $B$ 的有限性和 $F$ 上每个有限处的剩余次数正性。记 $B_p$ 为 $B$ 中处的剩余特征集。记 $F_{\mathrm{mod}}$ 为 $E$ 的模域，$F_{\mathrm{tpd}}=D.\mathrm{tripodalField}$ 为三脚架域，$d_{\mathrm{mod}}=[F_{\mathrm{mod}}:\mathbb Q]$，素数 $\ell$ 由 `D.prime` 给出。定理接收 `TowerLocalFacts D.E D.VBad D.prime`。对 $K_t$ 的每个有限处 $v$，记 $p$ 为其剩余特征，$u$ 为其在 $F_{\mathrm{tpd}}$ 下方的处，$e(v/u)$ 为相对分歧指数。该结构的三个字段要求以下各式。 [塔局部事实](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerLocalFacts.lean:116)

- $e(v/u)$ 的 $p$ 进阶至多为 $v_p(2^{12}\cdot3^2\cdot5)+\mathbf 1_{p=\ell}$。
- 若 $p\notin\{2,3,5,\ell\}$ 且 $u$ 上方没有 $B$ 中的处，则 $e(v/u)=1$。
- 若 $p\notin\{2,3,5,\ell\}$，则 $e(v/u)\le30\ell$。

定理还接收 `RelRamIdxModLeTwo D.E D.VBad`。对 $F_{\mathrm{mod}}$ 中每个 $u_0\in D.VBad$ 及 $F_{\mathrm{tpd}}$ 上位于其上方的每个有限处 $u$，它要求 $e(u/u_0)\le2$。扩张 $F_{\mathrm{tpd}}/F_{\mathrm{mod}}$ 为伽罗瓦扩张。`QI` 和 $B_p$ 的像描述给出 $B$ 的有限性以及每个 $p\in B_p$ 对应的坏处见证。 [相对分歧指数界](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerLocalFacts.lean:108) · [步骤 (iii)](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalBadChars.lean:99)

令 $S=(\mathrm{TL.withBadChars}\,\mathrm{QI}).\mathrm{dst}$，结论为

$$
\sum_{p\in S}\log p
\le 2d_{\mathrm{mod}}\bigl(\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})+D.\mathrm{logConductorDeg}\bigr)
   +5+\log\ell.
$$

有限集 $S$ 为 $\{2,3,5,\ell\}$、$B_p$ 以及 $K_t$ 中在 $\mathbb Q$ 上分歧指数异于 $1$ 的有限处的剩余特征的并集。每个指定素数在和中计一次。不同理想的对数次数是 $F_{\mathrm{tpd}}$ 的绝对不同理想的范数取对数后除以 $[F_{\mathrm{tpd}}:\mathbb Q]$。导子的对数次数对位于某个 $w\in B$ 下方的三脚架域有限处的对数范数求和，再除以同一个数域次数。 [指定素数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:62) · [归一化对数次数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

## 日本語

### `ThetaLocalData.withBadChars`

遠アーベル幾何学 `AG`、その緩和幾何学 `TG`、および初期 Θ データ `D : InitialThetaData AG TG` を固定する。$F$ を定義体、$E$ をその楕円曲線、$K_t$ を $\ell$ ねじれ点体 `D.Kt` とし、$\ell=D.\ell$ とする。$B=\mathrm{badPlacesOver}(D.F,D.E,D.VBad)$ は、モジュライ体の指定された悪い素点 `D.VBad` の上にある $F$ の有限素点の集合である。この非計算的な構成は `LT : LocalTheory.{u,v} D.Kt`、`TL : ThetaLocalData D LT`、および `QI : QPilotInputs D` を受け取る。`QI` は、$B$ の有限性と $F$ のすべての有限素点 $w$ における剰余次数 $f_w$ の正値性を与える。 [構成](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalBadChars.lean:49) · [q-pilot の入力](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutQPilot.lean:28)

結果の型は `ThetaLocalData D LT` である。悪い剰余標数の有限集合は $B_p=\{p_w\mid w\in B\}$ であり、`QI.qPilot.badFinset.image residueChar` で与えられる。ここで $p_w$ は $w$ の剰余標数である。$B_p$ の各元は素数であり、対応する素点が $B$ に存在する。$K_t$ の各有限素点 $v$ では、剰余標数が $B_p$ に属するときに $(K_t)_v$ の根 `TL.qroot v` を取り、それ以外では $1$ を取る。この値を $r_v$ とする。$r_v$ は非零であり、$\operatorname{ord}_p(r_v)\ge0$ を満たす。$p$ を $v$ の剰余標数とすると、付値は $\operatorname{ord}_p(p)=1$ と正規化する。$B$ が空であれば、すべての根は $1$ となる。 [悪い剰余標数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalBadChars.lean:26) · [局所 Θ データ](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:49)

各 $w\in B$ とその上にある各 $v$ に対し、$v$ の剰余標数は $B_p$ に属する。完備化の比較写像 $\iota_{w,v}\colon F_w\to(K_t)_v$ は、その素点の関係に対応する `TL.embedF` である。$q_w$ を $w$ における Tate パラメータ、$\operatorname{qOrder}(w)$ をその整数位数、$e_w$ を有理素数の上の $w$ の分岐指数とする。結果は次の等式を与える。

$$
r_v^{2\ell}=\iota_{w,v}(q_w),\qquad
\operatorname{ord}_p(r_v)=\frac{\operatorname{qOrder}(w)}{2\ell e_w}.
$$

各有理素数 $p$ と、台集合が $B$ である各有限集合について、次の重み付き等式も成り立つ。

$$
\sum_{v\mid p}\frac{[(K_t)_v:\mathbb Q_p]}{[K_t:\mathbb Q]}\operatorname{ord}_p(r_v)
=\frac{1}{2\ell}\sum_{\substack{w\in B\\p_w=p}}\frac{f_w}{[F:\mathbb Q]}\operatorname{qOrder}(w).
$$

左辺の和は `LT` の $p$ 上のファイバーとその重みを用いる。$p\notin B_p$ のとき、両辺とも零となる。 [根の等式と重み付きの和](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:63) · [重み付き等式の構成](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalBadChars.lean:74)

### `ThetaLocalData.step_iii_of_qPilotInputs`

遠アーベル幾何学 `AG`、その緩和幾何学 `TG`、および `D : InitialThetaData AG TG` を固定する。$F=D.F$、$E=D.E$、$K_t=D.Kt$ とし、$B$ をモジュライ体の指定された悪い素点 `D.VBad` の上にある $F$ の有限素点の集合とする。`LT : LocalTheory.{u,v} D.Kt`、`TL : ThetaLocalData D LT`、および `QI : QPilotInputs D` を取る。`QI` は $B$ の有限性と $F$ のすべての有限素点の剰余次数の正値性を与える。$B_p$ は $B$ の素点の剰余標数の集合である。$F_{\mathrm{mod}}$ を $E$ のモジュライ体、$F_{\mathrm{tpd}}=D.\mathrm{tripodalField}$ を三脚体、$d_{\mathrm{mod}}=[F_{\mathrm{mod}}:\mathbb Q]$ とする。素数 $\ell$ は `D.prime` で与えられる。定理は `TowerLocalFacts D.E D.VBad D.prime` を受け取る。$K_t$ の各有限素点 $v$ について、$p$ をその剰余標数、$u$ を $v$ の下にある $F_{\mathrm{tpd}}$ の素点、$e(v/u)$ を相対分岐指数とする。この構造の三つのフィールドは以下を要求する。 [体の塔の局所条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerLocalFacts.lean:116)

- $e(v/u)$ の $p$ 進付値は $v_p(2^{12}\cdot3^2\cdot5)+\mathbf 1_{p=\ell}$ 以下である。
- $p\notin\{2,3,5,\ell\}$ で、$u$ の上に $B$ の素点がなければ、$e(v/u)=1$ である。
- $p\notin\{2,3,5,\ell\}$ ならば、$e(v/u)\le30\ell$ である。

定理は `RelRamIdxModLeTwo D.E D.VBad` も受け取る。これは、$F_{\mathrm{mod}}$ の各素点 $u_0\in D.VBad$ とその上にある $F_{\mathrm{tpd}}$ の各有限素点 $u$ に対し、$e(u/u_0)\le2$ を要求する。$F_{\mathrm{tpd}}/F_{\mathrm{mod}}$ はガロア拡大である。`QI` と $B_p$ の像としての記述は、$B$ の有限性と各 $p\in B_p$ に対応する悪い素点の存在を与える。 [相対分岐指数の上界](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerLocalFacts.lean:108) · [ステップ (iii)](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalBadChars.lean:99)

$S=(\mathrm{TL.withBadChars}\,\mathrm{QI}).\mathrm{dst}$ とすると、結論は次の不等式である。

$$
\sum_{p\in S}\log p
\le 2d_{\mathrm{mod}}\bigl(\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})+D.\mathrm{logConductorDeg}\bigr)
   +5+\log\ell.
$$

有限集合 $S$ は $\{2,3,5,\ell\}$、$B_p$、および $\mathbb Q$ の上の分岐指数が $1$ と異なる $K_t$ の有限素点の剰余標数の和集合である。和では指定された各素数を一度ずつ数える。不同イデアルの対数次数は、$F_{\mathrm{tpd}}$ の絶対不同イデアルのノルムの対数を $[F_{\mathrm{tpd}}:\mathbb Q]$ で割った値である。導手の対数次数は、ある $w\in B$ の下にある三脚体の有限素点の対数ノルムの和を同じ体の次数で割った値である。 [指定された素数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:62) · [正規化した対数次数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

## MCP-CI

The archived leaf check and review succeeded against the recorded Lean inputs. The review reports `propext`, `Classical.choice`, and `Quot.sound` for both declarations, with `no_sorryAx = true`. [Leaf check ci-021649-3ffa7c78](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021649-3ffa7c78-result.json) · [Review ci-021667-f7dd1302](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021667-f7dd1302-result.json)
