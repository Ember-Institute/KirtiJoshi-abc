# Pointwise theta data and P7 / 逐点 Θ 数据与 P7 / 点ごとの Θ データと P7

## English

### `CurveInputs.pointThetaData`

Fix a height theory $T$, anabelian geometry `AG`, and tempered geometry `TG` over `AG`. Let $K:T.\mathrm{CBS}$, $d\in\mathbb N$, `CI : CurveInputs.{u} T AG K d`, and `anab : AnabelianExistence AG TG`. Write $I=\mathrm{CI.toCorollary22Inputs}$. Take a tripodal point $x$ and a proof $h_x$ that $x\in T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$, with $x\notin I.\mathrm{excCore}$. The exceptional set consists of points for which some such proof gives a curve that fails the universal core condition. Thus the selected curve satisfies this condition. After each base change along an embedding of its field of definition into a characteristic-zero field, the base change of `CF AG F E`, the quotient by the sign involution, is a core of the base change of the once-punctured curve. [Universal core condition](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:32) · [Core exceptional set](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:137)

Put $L=I.\mathrm{localData}(x,h_x)$, the local height data of the selected curve. Take a prime $\ell\ge7$ with the following properties. [Constructor inputs](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutPointThetaData.lean:39) · [Image condition](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:154)

- P2 requires $\ell\nmid L.\mathrm{hv}(w)$ at every $w\in L.\mathrm{bad}$. These are the finite places of multiplicative reduction, and $L.\mathrm{hv}(w)$ is the integer order of the Tate parameter.
- P5 requires a place $w\in L.\mathrm{bad}$ with residue characteristic $L.\mathrm{p}(w)\notin\{2,\ell\}$.
- P6 is `I.SL2Image x ℓ`. For every membership proof $h_x$ and primality proof $h_\ell$, it requires the image of the mod-$\ell$ representation `CI.modRep x hx ℓ hℓ` to contain $\mathrm{SL}_2(\mathbb Z/\ell\mathbb Z)$ inside $\mathrm{GL}_2(\mathbb Z/\ell\mathbb Z)$.

The noncomputable construction uses the selected curve and its mod-$\ell$ representation to form the initial theta data $D$. The geometric input `anab` applies to the global and admissible-prime data, the Tate family, and the universal core condition. Over the canonical inclusion from the field of moduli into the torsion field, it supplies an orbicurve and a witness of local geometric data for that orbicurve. The construction chooses these witnesses and uses the same Tate family in $D$. A moduli place belongs to the selected bad set exactly when its residue characteristic lies outside $\{2,\ell\}$, it has a place of the field of definition above it, and the curve has multiplicative reduction at every place above it. [Geometric input and choice](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutInitialThetaData.lean:26) · [Selected bad moduli places](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:55)

The result `PointThetaData CI x hx ℓ` contains $D$ and `QI : QPilotInputs D`. The latter gives finiteness of the selected bad places of $D.F$ and positive residue degree at every finite place of $D.F$. Write $F_{\mathrm{mod}}$ and $F_{\mathrm{tpd}}$ for the field of moduli and tripodal field of the curve in $D$. Its six remaining fields give

$$
\begin{aligned}
D.\ell &= \ell,\\
[F_{\mathrm{mod}}:\mathbb Q]&\le d,\\
\mathrm{QI.qPilot.logQ}&=L.\mathrm{heightOther}(2,\ell),\\
T.\mathrm{logDiff}(T.\mathrm{tripod},x)&=\operatorname{logDifferentDeg}(F_{\mathrm{tpd}}),\\
D.\mathrm{logConductorDeg}&\le T.\mathrm{logCond}(T.\mathrm{tripod},x),\\
T.\mathrm{logCond}(T.\mathrm{tripod},x)&\le D.\mathrm{logConductorDeg}+\log(2\ell).
\end{aligned}
$$

The q-pilot logarithm sums $(f_w/[D.F:\mathbb Q])\,\operatorname{qOrder}(w)\log p_w$ over the finite places $w$ of $D.F$ lying above the selected bad moduli places. Here $f_w$ and $p_w$ are the residue degree and residue characteristic of $w$. The height on the right uses the local height sum at residue characteristics outside $\{2,\ell\}$, divided by the field degree. The different degree is the log norm of the absolute different of $F_{\mathrm{tpd}}$ divided by $[F_{\mathrm{tpd}}:\mathbb Q]$. The conductor degree sums the log norms of the finite places of $F_{\mathrm{tpd}}$ below a selected bad place of $D.F$, with the same denominator. [Result fields](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutPointThetaData.lean:26) · [q-pilot logarithm](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_LeftHandSide.lean:110) · [Local height part](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts.lean:31) · [Normalized degrees](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

### `CurveInputs.concreteThetaDataExistence_of_pointwise`

Fix a height theory $T$, anabelian geometry `AG`, and tempered geometry `TG` over `AG`. Let $K:T.\mathrm{CBS}$, $d\in\mathbb N$, `CI : CurveInputs.{u} T AG K d`, `anab : AnabelianExistence AG TG`, and $I=\mathrm{CI.toCorollary22Inputs}$. The theorem takes a supplier `localInputs`. It applies to every tripodal point $x$ with membership proof $h_x$ in $T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$, outside $I.\mathrm{excCore}$, and to each prime $\ell\ge7$ under P2, P5, and P6. Put $L=I.\mathrm{localData}(x,h_x)$. P2 requires $\ell\nmid L.\mathrm{hv}(w)$ at every $w\in L.\mathrm{bad}$. P5 requires some $w\in L.\mathrm{bad}$ with $L.\mathrm{p}(w)\notin\{2,\ell\}$. P6 requires the mod-$\ell$ image to contain $\mathrm{SL}_2(\mathbb Z/\ell\mathbb Z)$ for every membership and primality proof. For these inputs set `P := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl`. The supplier gives `LT : LocalTheory.{u,v} P.data.Kt` and `TL : ThetaLocalData P.data LT`, with `TowerArithmetic P.data LT (TL.withBadChars P.qPilotInputs)`. [Pointwise supplier](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveConcreteExistence.lean:40)

Write $D=P.\mathrm{data}$, $d_{\mathrm{mod}}=[F_{\mathrm{mod}}:\mathbb Q]$, and $S=(\mathrm{TL.withBadChars}\,P.\mathrm{qPilotInputs}).\mathrm{dst}$. Here $S$ is the union of $\{2,3,5,\ell\}$, the q-pilot's bad residue characteristics, and the residue characteristics of finite places ramified over $\mathbb Q$ in $D.Kt$. The supplied tower arithmetic requires all three bounds below on this data. [Distinguished primes and local different term](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:29) · [Tower arithmetic](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173)

- R4 requires $p-2<e$ to imply $p\le552960d_{\mathrm{mod}}\ell$ and $\log e\le-3+4\log(552960d_{\mathrm{mod}}\ell)$ at every finite place of $D.Kt$. Here $p$ is its residue characteristic and $e$ its ramification index over $\mathbb Q$. The subtraction in the premise is in $\mathbb N$.
- Step (ii) requires $\sum_{p\in S}\mathrm{LT.logDK}(p)\le\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})+D.\mathrm{logConductorDeg}+2\log\ell+21$. The term $\mathrm{LT.logDK}(p)$ sums the place weights times the normalized different exponent times $\log p$ over the finite places above $p$ in $D.Kt$.
- Step (iii) requires $\sum_{p\in S}\log p\le2d_{\mathrm{mod}}\bigl(\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})+D.\mathrm{logConductorDeg}\bigr)+5+\log\ell$.

The conclusion is `ConcreteThetaDataExistence I`. It gives witnesses for every point and prime with the preceding conditions and P3. P3 requires $L.\mathrm{hv}(w)<\sqrt{I.\mathrm{h}(x)}$ at each $w\in L.\mathrm{bad}$ with $L.\mathrm{p}(w)=\ell$, with the Tate order viewed as a real number. The witnesses are $P.\mathrm{data}$, the supplied `LT`, `TL.withBadChars P.qPilotInputs`, and $P.\mathrm{qPilotInputs}$, together with their tower arithmetic. The conclusion gives $D.\ell=\ell$, $D.\mathrm{dmod}\le d$, and the equality of the concrete bundle's q-pilot logarithm with $L.\mathrm{heightOther}(2,\ell)$. It also identifies the point's different quantity with the normalized tripodal different degree and bounds the point's conductor quantity below by $D.\mathrm{logConductorDeg}$ and above by $D.\mathrm{logConductorDeg}+\log(2\ell)$. [P7 quantifiers and fields](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:36) · [Witnesses](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveConcreteExistence.lean:54)

## 简体中文

### `CurveInputs.pointThetaData`

固定高度理论 $T$、远 Abel 几何 `AG` 及其缓和几何 `TG`。给定 $K:T.\mathrm{CBS}$、$d\in\mathbb N$、`CI : CurveInputs.{u} T AG K d` 和 `anab : AnabelianExistence AG TG`。记 $I=\mathrm{CI.toCorollary22Inputs}$。取三脚架上的点 $x$ 和成员资格证明 $h_x$，使得 $x\in T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$，且 $x\notin I.\mathrm{excCore}$。例外集由存在此类成员资格证明且相应曲线不满足普遍核心条件的点组成。因此所选曲线满足此条件。沿定义域到任一特征零域的嵌入作基变换后，去掉一个点的椭圆曲线的基变换以 `CF AG F E` 的基变换为核心。`CF AG F E` 是该去点曲线按符号对合取商所得的轨形曲线。 [普遍核心条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:32) · [核心例外集](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:137)

记 $L=I.\mathrm{localData}(x,h_x)$ 为所选曲线的局部高度数据。取满足以下条件的素数 $\ell\ge7$。 [构造的输入](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutPointThetaData.lean:39) · [像条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:154)

- P2 要求每个 $w\in L.\mathrm{bad}$ 满足 $\ell\nmid L.\mathrm{hv}(w)$。这些处是乘法约化的有限处，$L.\mathrm{hv}(w)$ 是 Tate 参数的整数阶。
- P5 要求存在一个 $w\in L.\mathrm{bad}$，其剩余特征 $L.\mathrm{p}(w)\notin\{2,\ell\}$。
- P6 为 `I.SL2Image x ℓ`。对每个成员资格证明 $h_x$ 和素性证明 $h_\ell$，它要求模 $\ell$ 表示 `CI.modRep x hx ℓ hℓ` 的像包含 $\mathrm{GL}_2(\mathbb Z/\ell\mathbb Z)$ 中的二阶特殊线性群 $\mathrm{SL}_2(\mathbb Z/\ell\mathbb Z)$。

该不可计算构造使用所选曲线及其模 $\ell$ 表示形成初始 Θ 数据 $D$。几何输入 `anab` 使用全局数据、可容许素数数据、Tate 族和普遍核心条件。它在模域到挠点域的典范包含下给出一条轨形曲线，以及依赖于该曲线的局部几何数据见证。构造选取这两个见证，在 $D$ 中使用同一 Tate 族。模域中的一个有限处属于所选坏处集，当且仅当其剩余特征在 $\{2,\ell\}$ 之外、定义数域中存在上覆处，且曲线在所有上覆处均有乘法约化。 [几何输入与见证选取](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutInitialThetaData.lean:26) · [模域中所选坏处](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:55)

结果 `PointThetaData CI x hx ℓ` 包含 $D$ 和 `QI : QPilotInputs D`。后者给出 $D.F$ 中所选坏处的有限性以及 $D.F$ 每个有限处的剩余次数为正。记 $F_{\mathrm{mod}}$ 和 $F_{\mathrm{tpd}}$ 为 $D$ 中曲线的模域与三脚架域。结果的其余六个字段给出

$$
\begin{aligned}
D.\ell &= \ell,\\
[F_{\mathrm{mod}}:\mathbb Q]&\le d,\\
\mathrm{QI.qPilot.logQ}&=L.\mathrm{heightOther}(2,\ell),\\
T.\mathrm{logDiff}(T.\mathrm{tripod},x)&=\operatorname{logDifferentDeg}(F_{\mathrm{tpd}}),\\
D.\mathrm{logConductorDeg}&\le T.\mathrm{logCond}(T.\mathrm{tripod},x),\\
T.\mathrm{logCond}(T.\mathrm{tripod},x)&\le D.\mathrm{logConductorDeg}+\log(2\ell).
\end{aligned}
$$

q-pilot 的对数在 $D.F$ 上位于所选模域坏处上方的有限处 $w$ 求和，求和项为 $(f_w/[D.F:\mathbb Q])\,\operatorname{qOrder}(w)\log p_w$，其中 $f_w$ 和 $p_w$ 为 $w$ 的剩余次数与剩余特征。等式右侧的高度对剩余特征在 $\{2,\ell\}$ 之外的局部高度项求和，再除以定义数域次数。不同理想的对数次数是 $F_{\mathrm{tpd}}$ 的绝对不同理想的对数范数除以 $[F_{\mathrm{tpd}}:\mathbb Q]$。导子的对数次数在处于 $D.F$ 所选坏处下方的三脚架域有限处对对数范数求和，分母为同一三脚架域次数。 [结果字段](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutPointThetaData.lean:26) · [q-pilot 对数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_LeftHandSide.lean:110) · [局部高度分量](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts.lean:31) · [归一化对数次数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

### `CurveInputs.concreteThetaDataExistence_of_pointwise`

固定高度理论 $T$、远 Abel 几何 `AG` 及其缓和几何 `TG`。给定 $K:T.\mathrm{CBS}$、$d\in\mathbb N$、`CI : CurveInputs.{u} T AG K d` 和 `anab : AnabelianExistence AG TG`。记 $I=\mathrm{CI.toCorollary22Inputs}$。定理接收供给器 `localInputs`。它适用于每个三脚架上的点 $x$ 及其在 $T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ 中的成员资格证明 $h_x$，其中 $x$ 在 $I.\mathrm{excCore}$ 外，素数 $\ell\ge7$ 满足 P2、P5 和 P6。记 $L=I.\mathrm{localData}(x,h_x)$。P2 要求每个 $w\in L.\mathrm{bad}$ 满足 $\ell\nmid L.\mathrm{hv}(w)$。P5 要求存在一个 $w\in L.\mathrm{bad}$ 满足 $L.\mathrm{p}(w)\notin\{2,\ell\}$。P6 要求对每个成员资格和素性的证明，模 $\ell$ 表示的像都包含二阶特殊线性群 $\mathrm{SL}_2(\mathbb Z/\ell\mathbb Z)$。对这些输入，固定 `P := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl`。供给器给出 `LT : LocalTheory.{u,v} P.data.Kt` 与 `TL : ThetaLocalData P.data LT`，以及 `TowerArithmetic P.data LT (TL.withBadChars P.qPilotInputs)`。 [逐点供给器](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveConcreteExistence.lean:40)

记 $D=P.\mathrm{data}$、$d_{\mathrm{mod}}=[F_{\mathrm{mod}}:\mathbb Q]$ 和 $S=(\mathrm{TL.withBadChars}\,P.\mathrm{qPilotInputs}).\mathrm{dst}$。$S$ 是 $\{2,3,5,\ell\}$、q-pilot 的坏剩余特征，以及 $D.Kt$ 中在 $\mathbb Q$ 上分歧的有限处的剩余特征的并集。供给的塔算术在这组数据上要求以下三个界。 [指定素数与局部不同理想项](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:29) · [塔算术](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173)

- R4 要求 $D.Kt$ 的每个有限处在 $p-2<e$ 时满足 $p\le552960d_{\mathrm{mod}}\ell$ 和 $\log e\le-3+4\log(552960d_{\mathrm{mod}}\ell)$。这里 $p$ 为该处的剩余特征，$e$ 为其在 $\mathbb Q$ 上的分歧指数，前提中的减法在 $\mathbb N$ 中进行。
- 步骤 (ii) 要求 $\sum_{p\in S}\mathrm{LT.logDK}(p)\le\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})+D.\mathrm{logConductorDeg}+2\log\ell+21$。$\mathrm{LT.logDK}(p)$ 在 $D.Kt$ 的所有 $p$ 上覆处对处权重、归一化不同理想指数与 $\log p$ 的乘积求和。
- 步骤 (iii) 要求 $\sum_{p\in S}\log p\le2d_{\mathrm{mod}}\bigl(\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})+D.\mathrm{logConductorDeg}\bigr)+5+\log\ell$。

结论为 `ConcreteThetaDataExistence I`。它对满足上述条件以及 P3 的每对点和素数给出存在见证。P3 要求每个满足 $L.\mathrm{p}(w)=\ell$ 的 $w\in L.\mathrm{bad}$ 均满足 $L.\mathrm{hv}(w)<\sqrt{I.\mathrm{h}(x)}$，其中 Tate 阶数视为实数。见证为 $P.\mathrm{data}$、供给的 `LT`、`TL.withBadChars P.qPilotInputs` 和 $P.\mathrm{qPilotInputs}$，并带有相应的塔算术。结论给出 $D.\ell=\ell$、$D.\mathrm{dmod}\le d$，并将具体数据的 q-pilot 对数等同于 $L.\mathrm{heightOther}(2,\ell)$。它还将点的不同理想量等同于三脚架域的归一化不同理想对数次数，给出点的导子量的下界 $D.\mathrm{logConductorDeg}$ 和上界 $D.\mathrm{logConductorDeg}+\log(2\ell)$。 [P7 的量词与字段](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:36) · [见证](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveConcreteExistence.lean:54)

## 日本語

### `CurveInputs.pointThetaData`

高さ理論 $T$、遠アーベル幾何学 `AG`、およびその緩和幾何学 `TG` を固定する。$K:T.\mathrm{CBS}$、$d\in\mathbb N$、`CI : CurveInputs.{u} T AG K d`、`anab : AnabelianExistence AG TG` を与える。$I=\mathrm{CI.toCorollary22Inputs}$ とする。三脚の点 $x$ と $x\in T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ の証明 $h_x$ を取り、$x\notin I.\mathrm{excCore}$ とする。例外集合の点は、このような所属証明のうち、対応する曲線が普遍的なコア条件を満たさないものを少なくとも一つ持つ。したがって選んだ曲線はこの条件を満たす。定義体から標数零の体への任意の埋め込みに沿った底変換後に、一点を除いた楕円曲線の底変換に対し、符号の対合による商 `CF AG F E` の底変換がコアとなる。 [普遍的なコア条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:32) · [コアの例外集合](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:137)

$L=I.\mathrm{localData}(x,h_x)$ を選んだ曲線の局所高さデータとする。次の条件を満たす素数 $\ell\ge7$ を取る。 [構成の入力](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutPointThetaData.lean:39) · [像の条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:154)

- P2 は、各 $w\in L.\mathrm{bad}$ で $\ell\nmid L.\mathrm{hv}(w)$ を要求する。これらの素点は乗法的還元をもつ有限素点であり、$L.\mathrm{hv}(w)$ は Tate パラメータの整数位数である。
- P5 は、剰余標数 $L.\mathrm{p}(w)\notin\{2,\ell\}$ を満たす素点 $w\in L.\mathrm{bad}$ の存在を要求する。
- P6 は `I.SL2Image x ℓ` である。点の所属証明 $h_x$ と素数性の証明 $h_\ell$ の各組に対し、mod $\ell$ 表現 `CI.modRep x hx ℓ hℓ` の像が $\mathrm{GL}_2(\mathbb Z/\ell\mathbb Z)$ の部分群 $\mathrm{SL}_2(\mathbb Z/\ell\mathbb Z)$ を含むことを要求する。

この非計算的な構成は、選んだ曲線とその mod $\ell$ 表現を用いて初期 Θ データ $D$ を作る。幾何学的な入力 `anab` は、大域データ、許容素数のデータ、Tate 族、および普遍的なコア条件を用いる。モジュライ体からねじれ点体への標準包含の上で、軌道曲線と、その曲線に従属する局所幾何データの存在を与える。構成はこれらの証拠を選び、同じ Tate 族を $D$ に入れる。モジュライ体の有限素点が指定された悪い素点の集合に属するための必要十分条件は、剰余標数が $\{2,\ell\}$ の外にあり、上に定義体の素点が存在し、その上のすべての素点で曲線が乗法的還元をもつことである。 [幾何学的な入力と選択](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutInitialThetaData.lean:26) · [指定されたモジュライ体の悪い素点](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:55)

結果 `PointThetaData CI x hx ℓ` は $D$ と `QI : QPilotInputs D` を含む。後者は、$D.F$ の指定された悪い素点の有限性と $D.F$ の全有限素点の剰余次数の正値性を与える。$F_{\mathrm{mod}}$ と $F_{\mathrm{tpd}}$ を $D$ の曲線のモジュライ体と三脚体とする。残りの六つのフィールドは次を与える。

$$
\begin{aligned}
D.\ell &= \ell,\\
[F_{\mathrm{mod}}:\mathbb Q]&\le d,\\
\mathrm{QI.qPilot.logQ}&=L.\mathrm{heightOther}(2,\ell),\\
T.\mathrm{logDiff}(T.\mathrm{tripod},x)&=\operatorname{logDifferentDeg}(F_{\mathrm{tpd}}),\\
D.\mathrm{logConductorDeg}&\le T.\mathrm{logCond}(T.\mathrm{tripod},x),\\
T.\mathrm{logCond}(T.\mathrm{tripod},x)&\le D.\mathrm{logConductorDeg}+\log(2\ell).
\end{aligned}
$$

q-pilot の対数は、指定されたモジュライ体の悪い素点の上にある $D.F$ の有限素点 $w$ にわたる $(f_w/[D.F:\mathbb Q])\,\operatorname{qOrder}(w)\log p_w$ の和である。$f_w$ と $p_w$ は $w$ の剰余次数と剰余標数である。等式の右辺の高さは、剰余標数が $\{2,\ell\}$ の外にある局所高さの項の和を定義体の次数で割った値である。不同イデアルの対数次数は、$F_{\mathrm{tpd}}$ の絶対不同イデアルのノルムの対数を $[F_{\mathrm{tpd}}:\mathbb Q]$ で割った値である。導手の対数次数は、$D.F$ の指定された悪い素点の下にある三脚体の有限素点の対数ノルムの和を、同じ三脚体の次数で割った値である。 [結果のフィールド](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutPointThetaData.lean:26) · [q-pilot の対数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_LeftHandSide.lean:110) · [局所高さの成分](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts.lean:31) · [正規化した対数次数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

### `CurveInputs.concreteThetaDataExistence_of_pointwise`

高さ理論 $T$、遠アーベル幾何学 `AG`、およびその緩和幾何学 `TG` を固定する。$K:T.\mathrm{CBS}$、$d\in\mathbb N$、`CI : CurveInputs.{u} T AG K d`、`anab : AnabelianExistence AG TG` を与え、$I=\mathrm{CI.toCorollary22Inputs}$ とする。定理は供給関数 `localInputs` を受け取る。これは、三脚の各点 $x$ と $T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ への所属証明 $h_x$ に対して適用される。$x$ は $I.\mathrm{excCore}$ の外にあり、素数 $\ell\ge7$ は P2、P5 および P6 を満たす。$L=I.\mathrm{localData}(x,h_x)$ とする。P2 は各 $w\in L.\mathrm{bad}$ で $\ell\nmid L.\mathrm{hv}(w)$ を要求する。P5 は $L.\mathrm{p}(w)\notin\{2,\ell\}$ を満たす $w\in L.\mathrm{bad}$ の存在を要求する。P6 は、任意の所属証明と素数性の証明について、mod $\ell$ 表現の像が $\mathrm{SL}_2(\mathbb Z/\ell\mathbb Z)$ を含むことを要求する。これらの入力について `P := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl` と定める。供給関数は `LT : LocalTheory.{u,v} P.data.Kt` と `TL : ThetaLocalData P.data LT` を、`TowerArithmetic P.data LT (TL.withBadChars P.qPilotInputs)` とともに与える。 [点ごとの供給関数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveConcreteExistence.lean:40)

$D=P.\mathrm{data}$、$d_{\mathrm{mod}}=[F_{\mathrm{mod}}:\mathbb Q]$、$S=(\mathrm{TL.withBadChars}\,P.\mathrm{qPilotInputs}).\mathrm{dst}$ とする。$S$ は $\{2,3,5,\ell\}$、q-pilot の悪い剰余標数、および $D.Kt$ で $\mathbb Q$ 上分岐する有限素点の剰余標数の和集合である。この体の塔の算術条件は同じデータについて次の三つの評価を要求する。 [指定された素数と局所不同イデアルの項](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:29) · [体の塔の算術条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173)

- R4 は、$D.Kt$ の各有限素点で $p-2<e$ ならば $p\le552960d_{\mathrm{mod}}\ell$ と $\log e\le-3+4\log(552960d_{\mathrm{mod}}\ell)$ を要求する。$p$ はその剰余標数であり、$e$ は $\mathbb Q$ 上の分岐指数である。仮定の減算は $\mathbb N$ で行う。
- ステップ (ii) は $\sum_{p\in S}\mathrm{LT.logDK}(p)\le\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})+D.\mathrm{logConductorDeg}+2\log\ell+21$ を要求する。$\mathrm{LT.logDK}(p)$ は、$D.Kt$ で $p$ の上にある各有限素点の重みと正規化した不同イデアルの指数と $\log p$ の積を足したものである。
- ステップ (iii) は $\sum_{p\in S}\log p\le2d_{\mathrm{mod}}\bigl(\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})+D.\mathrm{logConductorDeg}\bigr)+5+\log\ell$ を要求する。

結論は `ConcreteThetaDataExistence I` である。上記の条件と P3 を満たす点と素数の各組に対して、存在の証拠を与える。P3 は、$L.\mathrm{p}(w)=\ell$ を満たす各 $w\in L.\mathrm{bad}$ で $L.\mathrm{hv}(w)<\sqrt{I.\mathrm{h}(x)}$ を要求する。ここでは Tate 位数を実数として扱う。証拠は $P.\mathrm{data}$、供給された `LT`、`TL.withBadChars P.qPilotInputs`、および $P.\mathrm{qPilotInputs}$ であり、対応する体の塔の算術条件を伴う。結論は $D.\ell=\ell$ と $D.\mathrm{dmod}\le d$ を与え、具体的なデータの q-pilot の対数を $L.\mathrm{heightOther}(2,\ell)$ に等置する。さらに点の不同イデアル量を三脚体の正規化した不同イデアルの対数次数に等置し、点の導手量の下界 $D.\mathrm{logConductorDeg}$ と上界 $D.\mathrm{logConductorDeg}+\log(2\ell)$ を与える。 [P7 の量化とフィールド](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:36) · [存在の証拠](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveConcreteExistence.lean:54)

## MCP-CI

The archived leaf checks and review succeeded against the recorded Lean inputs. The review reports `propext`, `Classical.choice`, and `Quot.sound` for both declarations, with `no_sorryAx = true`. [Pointwise data leaf check ci-021698-b8725f13](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021698-b8725f13-result.json) · [P7 assembly leaf check ci-021734-e798309d](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021734-e798309d-result.json) · [Review ci-021743-f33906a6](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021743-f33906a6-result.json)
