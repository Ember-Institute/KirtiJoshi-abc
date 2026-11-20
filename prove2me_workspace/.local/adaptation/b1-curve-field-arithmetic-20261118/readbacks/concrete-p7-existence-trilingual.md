# Concrete P7 existence / 具体 P7 存在性 / 具体的な P7 の存在

## English

### `ConcreteThetaDataExistence.toThetaDataExistence`

Fix a height theory $T$, a compactly bounded set parameter $K:T.\mathrm{CBS}$, a natural number $d$, and `I : Corollary22Inputs T K d`. Fix anabelian geometry `AG` and tempered geometry `TG` over it. The theorem converts a proof of `ConcreteThetaDataExistence I` into `ThetaDataExistence IsConcrete I`. Both propositions apply to every tripodal point $x$ with a membership proof $h_x$ in $T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$, outside $I.\mathrm{excCore}$, and every prime $\ell\ge7$ with the following conditions. Put $L=I.\mathrm{localData}(x,h_x)$. Its finite bad index set is $L.\mathrm{bad}$, with local heights $L.\mathrm{hv}$ and residue characteristics $L.\mathrm{p}$. [Concrete premise](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:36) · [General conclusion](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean:112)

- P2 requires $\ell\nmid L.\mathrm{hv}(w)$ at each $w\in L.\mathrm{bad}$.
- P3 requires $(L.\mathrm{hv}(w):\mathbb R)<\sqrt{I.\mathrm{h}(x)}$ at each $w\in L.\mathrm{bad}$ with $L.\mathrm{p}(w)=\ell$.
- P5 requires some $w\in L.\mathrm{bad}$ with $L.\mathrm{p}(w)\notin\{2,\ell\}$.
- P6 requires the proposition $I.\mathrm{SL2Image}(x,\ell)$ supplied in $I$.

For these inputs the premise gives witnesses $D$, `LT : LocalTheory.{u,v} D.Kt`, `TL : ThetaLocalData D LT`, `QI : QPilotInputs D`, and `TA : TowerArithmetic D LT TL`. Here $D$ is initial theta data for `AG` and `TG`, and $D.Kt$ is its torsion field. The q-pilot input `QI` gives finiteness of the bad places in $D.F$ above the selected bad moduli places and positive residue degree at each finite place of $D.F$. The tower arithmetic gives R4 and steps (ii) and (iii) for the same $D$, `LT`, and `TL`. The premise also gives the six comparisons below. Write $X=\mathrm{concreteVariantData}(D,LT,TL,QI)$ and $D_0,C_0$ for the normalized log different and conductor degrees of $D$'s tripodal field. The bundle $X$ has initial data $D$, the q-pilot from `QI`, and the right-hand-side data from `TL`. The value $X.\mathrm{dmod}$ is the degree of the field of moduli over $\mathbb Q$. [Concrete data and predicate](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:24) · [Tower arithmetic](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173)

$$
\begin{gathered}
X.\ell=\ell,\qquad X.\mathrm{dmod}\le d,\qquad
X.\mathrm{qPilot.logQ}=L.\mathrm{heightOther}(2,\ell),\\
T.\mathrm{logDiff}(T.\mathrm{tripod},x)=D_0,\\
C_0\le T.\mathrm{logCond}(T.\mathrm{tripod},x)\le C_0+\log(2\ell).
\end{gathered}
$$

The q-pilot logarithm sums $(f_w/[D.F:\mathbb Q])\operatorname{qOrder}(w)\log p_w$ over the selected bad places of $D.F$, where $f_w$ is the residue degree and $p_w$ the residue characteristic. The term $L.\mathrm{heightOther}(2,\ell)$ sums $L.\mathrm{hv}(w)L.\mathrm{f}(w)\log L.\mathrm{p}(w)$ over $w\in L.\mathrm{bad}$ with $L.\mathrm{p}(w)\notin\{2,\ell\}$ and divides by $L.\mathrm{deg}$. The invariant $D_0$ is the log absolute norm of the different ideal divided by the tripodal field degree. The invariant $C_0$ sums the log norms of the tripodal finite places below some selected bad place of $D.F$ and divides by the same degree. [Local height term](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts.lean:31) · [Normalized degrees](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

The theorem supplies $X$ and its invariants $\mathrm{inv}=\mathrm{TL.invariants}(QI)$ as the existential witnesses. The predicate `IsConcrete X` asserts equality with a concrete bundle for some $D$, `LT`, `TL`, and `QI`. Here the same inputs witness that equality. The theorem passes the six comparisons to the output, with $\mathrm{inv.logDtpd}=D_0$ and $\mathrm{inv.logFtpd}=C_0$. It also supplies `Theorem110Certificate inv` and `Nonempty inv.LocalEstimate`. The certificate records $7\le X.\ell$, membership in $\mathrm{inv.dst}$ for every residue characteristic in the q-pilot's bad-place support, and steps (ii) and (iii). With $S=\mathrm{inv.dst}$ these steps give $\sum_{p\in S}\mathrm{LT.logDK}(p)\le D_0+C_0+2\log\ell+21$ and $\sum_{p\in S}\log p\le2X.\mathrm{dmod}(D_0+C_0)+5+\log\ell$. The local estimate is `TA.localEstimate` on the same invariants. It gives a hull region containing the theta-pilot for every capsule and rational place. At a nondistinguished prime this region is the integral region. It bounds the packet log-volume at the distinguished primes and at infinity, and gives monotonicity on hull regions. [Witness construction](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:55) · [Certificate fields](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Invariants.lean:240) · [Local estimate fields](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_LogVolumeBound.lean:116)

### `CurveInputs.concreteThetaDataExistence`

Fix a height theory $T$, a compactly bounded set parameter $K:T.\mathrm{CBS}$, a natural number $d$, anabelian geometry `AG`, and tempered geometry `TG` over it. Take `CI : CurveInputs.{u} T AG K d` and `anab : AnabelianExistence AG TG`. The geometric input supplies an orbicurve over the canonical inclusion of the moduli field into the torsion field and a witness of local geometric data for that orbicurve, given the global and admissible-prime data, Tate family, and universal core condition. The theorem takes the following three providers. [Geometric input](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutInitialThetaData.lean:26) · [Provider quantifiers](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveConcreteExistence.lean:24)

- For every `D : InitialThetaData AG TG`, `LTp D` gives `LocalTheory.{u,v} D.Kt`.
- For every such $D$ and every `LT : LocalTheory.{u,v} D.Kt`, `TLp D LT` gives `ThetaLocalData D LT`.
- For every such $D$, `LT`, and `TL : ThetaLocalData D LT`, `TAp D LT TL` gives `TowerArithmetic D LT TL`.

Let $I=\mathrm{CI.toCorollary22Inputs}$. The conclusion `ConcreteThetaDataExistence I` applies to every $x$ with membership proof $h_x$ in $T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ and $x\notin I.\mathrm{excCore}$. For each prime $\ell\ge7$, take $L=I.\mathrm{localData}(x,h_x)$ and assume P2, P3, P5, and P6. P2 requires the integer Tate orders at all the selected curve's places of multiplicative reduction to be indivisible by $\ell$. P3 requires every such order at residue characteristic $\ell$ to be less than $\sqrt{I.\mathrm{h}(x)}$ as a real number. P5 requires one such place with residue characteristic outside $\{2,\ell\}$. P6 requires that for every membership and primality proof, the image of the associated mod-$\ell$ representation contain $\mathrm{SL}_2(\mathbb Z/\ell\mathbb Z)$. The exceptional set records points for which some membership proof gives a curve that fails the universal core condition. This condition requires the sign quotient of the once-punctured curve to give a core after each base change along an embedding into a characteristic-zero field. [Concrete P7 quantifiers](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:36) · [Curve inputs and image predicate](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:136)

The construction obtains the initial theta data $D$ of that point and prime, the q-pilot input `QI`, and the six comparisons from `CI.exists_initialThetaData`. This use of the curve constructor requires the point and prime conditions with P2, P5, and P6. It takes `LT := LTp D`, `TL := TLp D LT`, and the tower arithmetic `TAp D LT TL` as the remaining witnesses. Put $X=\mathrm{concreteVariantData}(D,LT,TL,QI)$. The q-pilot input certifies finiteness of the selected bad places and positive residue degrees in the field of definition of $D$. The conclusion gives these comparisons, with the prime and the moduli field degree of $X$ taken from $D$.

$$
\begin{gathered}
X.\ell=\ell,\qquad X.\mathrm{dmod}\le d,\qquad
X.\mathrm{qPilot.logQ}=L.\mathrm{heightOther}(2,\ell),\\
T.\mathrm{logDiff}(T.\mathrm{tripod},x)=D_0,\\
C_0\le T.\mathrm{logCond}(T.\mathrm{tripod},x)\le C_0+\log(2\ell).
\end{gathered}
$$

Here $L.\mathrm{heightOther}(2,\ell)$ sums the local terms $L.\mathrm{hv}(w)L.\mathrm{f}(w)\log L.\mathrm{p}(w)$ over the bad places of residue characteristic outside $\{2,\ell\}$ and divides by $L.\mathrm{deg}$. The quantities $D_0$ and $C_0$ are the normalized log different and conductor degrees of the tripodal field. [Curve constructor and comparisons](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutPointThetaData.lean:73) · [Witnesses](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveConcreteExistence.lean:31)

The arithmetic witness uses $S=\mathrm{TL.dst}$, the union of $\{2,3,5,\ell\}$, `TL.badChars`, and the residue characteristics of finite places ramified over $\mathbb Q$ in $D.Kt$. It gives R4 for each finite place of $D.Kt$, with residue characteristic $p$, absolute ramification index $e$, and natural subtraction $p-2$. Its other fields give steps (ii) and (iii) over the same $S$. Here $d_{\mathrm{mod}}=D.\mathrm{dmod}$ and $\mathrm{LT.logDK}(p)$ is the contribution of $p$ to the normalized different degree of $D.Kt$.

$$
\begin{aligned}
p-2<e &\ \Longrightarrow\ \bigl(p\le552960d_{\mathrm{mod}}\ell
\ \land\ \log e\le-3+4\log(552960d_{\mathrm{mod}}\ell)\bigr),\\
\sum_{p\in S}\mathrm{LT.logDK}(p)&\le D_0+C_0+2\log\ell+21,\\
\sum_{p\in S}\log p&\le2d_{\mathrm{mod}}(D_0+C_0)+5+\log\ell .
\end{aligned}
$$

[Distinguished primes and local different term](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:29) · [Three arithmetic fields](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173)

## 简体中文

### `ConcreteThetaDataExistence.toThetaDataExistence`

固定高度理论 $T$、紧致有界子集参数 $K:T.\mathrm{CBS}$、自然数 $d$ 和 `I : Corollary22Inputs T K d`，以及远 Abel 几何 `AG` 与其缓和几何 `TG`。定理将 `ConcreteThetaDataExistence I` 的证明转为 `ThetaDataExistence IsConcrete I`。两个命题都量化于三脚架上的每个点 $x$ 及其在 $T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ 中的成员资格证明 $h_x$，其中 $x$ 在 $I.\mathrm{excCore}$ 外，并量化于满足以下条件的每个素数 $\ell\ge7$。令 $L=I.\mathrm{localData}(x,h_x)$。它的坏处指标有限集为 $L.\mathrm{bad}$，局部高度为 $L.\mathrm{hv}$，剩余特征为 $L.\mathrm{p}$。 [具体存在性前提](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:36) · [一般存在性结论](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean:112)

- P2 要求每个 $w\in L.\mathrm{bad}$ 满足 $\ell\nmid L.\mathrm{hv}(w)$。
- P3 要求每个满足 $L.\mathrm{p}(w)=\ell$ 的 $w\in L.\mathrm{bad}$ 满足 $(L.\mathrm{hv}(w):\mathbb R)<\sqrt{I.\mathrm{h}(x)}$。
- P5 要求存在 $w\in L.\mathrm{bad}$，使得 $L.\mathrm{p}(w)\notin\{2,\ell\}$。
- P6 要求 $I$ 所给的命题 $I.\mathrm{SL2Image}(x,\ell)$ 成立。

在这些输入下，前提给出见证 $D$、`LT : LocalTheory.{u,v} D.Kt`、`TL : ThetaLocalData D LT`、`QI : QPilotInputs D` 和 `TA : TowerArithmetic D LT TL`。$D$ 是关于 `AG` 和 `TG` 的初始 Θ 数据，$D.Kt$ 是其挠点域。供 q-pilot 使用的 `QI` 给出 $D.F$ 中位于模域所选坏处上方的坏处的有限性，以及 $D.F$ 中每个有限处的剩余次数正性。塔算术在同一 $D$、`LT`、`TL` 上给出 R4 及步骤 (ii)、(iii)。前提还给出下列六项关系。记 $X=\mathrm{concreteVariantData}(D,LT,TL,QI)$。$D_0,C_0$ 分别是 $D$ 的三脚架域的归一化不同理想对数次数和导子对数次数。数据 $X$ 的初始数据为 $D$，q-pilot 来自 `QI`，右端数据来自 `TL`。$X.\mathrm{dmod}$ 是模域在 $\mathbb Q$ 上的次数。 [具体数据与谓词](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:24) · [塔算术](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173)

$$
\begin{gathered}
X.\ell=\ell,\qquad X.\mathrm{dmod}\le d,\qquad
X.\mathrm{qPilot.logQ}=L.\mathrm{heightOther}(2,\ell),\\
T.\mathrm{logDiff}(T.\mathrm{tripod},x)=D_0,\\
C_0\le T.\mathrm{logCond}(T.\mathrm{tripod},x)\le C_0+\log(2\ell).
\end{gathered}
$$

q-pilot 的对数在 $D.F$ 的所选坏处对 $(f_w/[D.F:\mathbb Q])\operatorname{qOrder}(w)\log p_w$ 求和，其中 $f_w$ 是剩余次数，$p_w$ 是剩余特征。$L.\mathrm{heightOther}(2,\ell)$ 对 $L.\mathrm{bad}$ 中满足 $L.\mathrm{p}(w)\notin\{2,\ell\}$ 的项 $L.\mathrm{hv}(w)L.\mathrm{f}(w)\log L.\mathrm{p}(w)$ 求和，再除以 $L.\mathrm{deg}$。$D_0$ 是不同理想的绝对范数取对数后除以三脚架域次数。$C_0$ 对位于 $D.F$ 某个所选坏处下方的三脚架域有限处求对数范数之和，再除以同一个次数。 [局部高度项](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts.lean:31) · [归一化对数次数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

定理给出 $X$ 和 $\mathrm{inv}=\mathrm{TL.invariants}(QI)$ 作为存在见证。谓词 `IsConcrete X` 要求 $X$ 等于某组 $D$、`LT`、`TL`、`QI` 构成的具体数据。这里用同一组输入见证该等式。结论保留上述六项关系，其中 $\mathrm{inv.logDtpd}=D_0$，$\mathrm{inv.logFtpd}=C_0$。它还给出 `Theorem110Certificate inv` 和 `Nonempty inv.LocalEstimate`。证书记录 $7\le X.\ell$、q-pilot 坏处支持中每个处的剩余特征属于 $\mathrm{inv.dst}$，以及步骤 (ii)、(iii)。记 $S=\mathrm{inv.dst}$，这两步给出 $\sum_{p\in S}\mathrm{LT.logDK}(p)\le D_0+C_0+2\log\ell+21$ 和 $\sum_{p\in S}\log p\le2X.\mathrm{dmod}(D_0+C_0)+5+\log\ell$。局部估计为同一不变量上的 `TA.localEstimate`。它为每个标签集和有理处给出包含 Θ-pilot 的包络区域。在指定素数以外，该区域等于整区域。局部估计给出指定素数和无穷处的分量积包对数体积界，以及包络区域间的单调性。 [见证构造](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:55) · [证书字段](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Invariants.lean:240) · [局部估计字段](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_LogVolumeBound.lean:116)

### `CurveInputs.concreteThetaDataExistence`

固定高度理论 $T$、紧致有界子集参数 $K:T.\mathrm{CBS}$、自然数 $d$，以及远 Abel 几何 `AG` 和其缓和几何 `TG`。取 `CI : CurveInputs.{u} T AG K d` 和 `anab : AnabelianExistence AG TG`。几何输入接收全局数据、可容许素数数据、Tate 族和普遍核心条件，在模域到挠点域的典范包含下给出一条轨形曲线及依赖于该曲线的局部几何数据见证。定理接收以下三个供给器。 [几何输入](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutInitialThetaData.lean:26) · [供给器量词](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveConcreteExistence.lean:24)

- 对每个 `D : InitialThetaData AG TG`，`LTp D` 给出 `LocalTheory.{u,v} D.Kt`。
- 对每个这样的 $D$ 和每个 `LT : LocalTheory.{u,v} D.Kt`，`TLp D LT` 给出 `ThetaLocalData D LT`。
- 对每个这样的 $D$、`LT` 和每个 `TL : ThetaLocalData D LT`，`TAp D LT TL` 给出 `TowerArithmetic D LT TL`。

令 $I=\mathrm{CI.toCorollary22Inputs}$。结论 `ConcreteThetaDataExistence I` 适用于 $T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ 中的每个点 $x$ 及其成员资格证明 $h_x$，其中 $x\notin I.\mathrm{excCore}$。对每个素数 $\ell\ge7$，取 $L=I.\mathrm{localData}(x,h_x)$，并假设 P2、P3、P5、P6。P2 要求所选曲线的每个乘法约化处的整数 Tate 阶均不被 $\ell$ 整除。P3 要求上述处中剩余特征为 $\ell$ 的每个处的 Tate 阶视为实数后严格小于 $\sqrt{I.\mathrm{h}(x)}$。P5 要求至少一个这样的乘法约化处的剩余特征在 $\{2,\ell\}$ 外。P6 要求对每个成员资格证明和素性证明，相应模 $\ell$ 表示的像均包含二阶特殊线性群 $\mathrm{SL}_2(\mathbb Z/\ell\mathbb Z)$。核心例外集记录存在成员资格证明且相应曲线不满足普遍核心条件的点。该条件要求沿定义域到特征零域的每个嵌入作基变换后，去掉一个点的曲线按符号对合所得的商给出其核心。 [具体 P7 量词](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:36) · [曲线输入与像谓词](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:136)

构造从 `CI.exists_initialThetaData` 取得同一点和素数的初始 Θ 数据 $D$、q-pilot 输入 `QI` 和六项关系。该处调用曲线构造使用点和素数的条件以及 P2、P5、P6。其余见证取自 `LT := LTp D`、`TL := TLp D LT` 及 `TAp D LT TL`。令 $X=\mathrm{concreteVariantData}(D,LT,TL,QI)$。q-pilot 输入给出 $D$ 的定义数域中所选坏处的有限性及各有限处剩余次数的正性。结论给出下列关系，其中 $X$ 的素数和模域次数取自 $D$。

$$
\begin{gathered}
X.\ell=\ell,\qquad X.\mathrm{dmod}\le d,\qquad
X.\mathrm{qPilot.logQ}=L.\mathrm{heightOther}(2,\ell),\\
T.\mathrm{logDiff}(T.\mathrm{tripod},x)=D_0,\\
C_0\le T.\mathrm{logCond}(T.\mathrm{tripod},x)\le C_0+\log(2\ell).
\end{gathered}
$$

$L.\mathrm{heightOther}(2,\ell)$ 对剩余特征在 $\{2,\ell\}$ 外的坏处求局部项 $L.\mathrm{hv}(w)L.\mathrm{f}(w)\log L.\mathrm{p}(w)$ 的和，再除以 $L.\mathrm{deg}$。$D_0,C_0$ 分别为三脚架域的归一化不同理想对数次数和导子对数次数。 [曲线构造与比较关系](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutPointThetaData.lean:73) · [见证](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveConcreteExistence.lean:31)

算术见证使用 $S=\mathrm{TL.dst}$，即 $\{2,3,5,\ell\}$、`TL.badChars` 和 $D.Kt$ 中在 $\mathbb Q$ 上分歧的有限处的剩余特征的并集。R4 对 $D.Kt$ 的每个有限处适用，其中 $p$ 为剩余特征、$e$ 为绝对分歧指数，$p-2$ 是自然数减法。其余字段给出对同一 $S$ 的步骤 (ii)、(iii)。这里 $d_{\mathrm{mod}}=D.\mathrm{dmod}$，$\mathrm{LT.logDK}(p)$ 是 $p$ 对 $D.Kt$ 的归一化不同理想对数次数的贡献。

$$
\begin{aligned}
p-2<e &\ \Longrightarrow\ \bigl(p\le552960d_{\mathrm{mod}}\ell
\ \land\ \log e\le-3+4\log(552960d_{\mathrm{mod}}\ell)\bigr),\\
\sum_{p\in S}\mathrm{LT.logDK}(p)&\le D_0+C_0+2\log\ell+21,\\
\sum_{p\in S}\log p&\le2d_{\mathrm{mod}}(D_0+C_0)+5+\log\ell .
\end{aligned}
$$

[指定素数与局部不同理想项](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:29) · [三个算术字段](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173)

## 日本語

### `ConcreteThetaDataExistence.toThetaDataExistence`

高さ理論 $T$、コンパクト有界集合のパラメータ $K:T.\mathrm{CBS}$、自然数 $d$、および `I : Corollary22Inputs T K d` を固定する。遠アーベル幾何学 `AG` と、その緩和幾何学 `TG` を固定する。定理は `ConcreteThetaDataExistence I` の証明から `ThetaDataExistence IsConcrete I` を与える。二つの命題は、$T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ に属する三脚の各点 $x$ とその所属証明 $h_x$ に対して述べられる。$x$ は $I.\mathrm{excCore}$ の外にあるものとし、次の条件を満たす各素数 $\ell\ge7$ を取る。$L=I.\mathrm{localData}(x,h_x)$ とし、その悪い素点の添字の有限集合を $L.\mathrm{bad}$、局所高さを $L.\mathrm{hv}$、剰余標数を $L.\mathrm{p}$ とする。 [具体的な存在の仮定](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:36) · [一般の存在の結論](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean:112)

- P2 は、各 $w\in L.\mathrm{bad}$ で $\ell\nmid L.\mathrm{hv}(w)$ を要求する。
- P3 は、$L.\mathrm{p}(w)=\ell$ を満たす各 $w\in L.\mathrm{bad}$ で $(L.\mathrm{hv}(w):\mathbb R)<\sqrt{I.\mathrm{h}(x)}$ を要求する。
- P5 は、$L.\mathrm{p}(w)\notin\{2,\ell\}$ を満たす $w\in L.\mathrm{bad}$ の存在を要求する。
- P6 は、$I$ で与えられた命題 $I.\mathrm{SL2Image}(x,\ell)$ を要求する。

これらの入力について、仮定は $D$、`LT : LocalTheory.{u,v} D.Kt`、`TL : ThetaLocalData D LT`、`QI : QPilotInputs D`、および `TA : TowerArithmetic D LT TL` を与える。$D$ は `AG` および `TG` に関する初期 Θ データであり、$D.Kt$ はそのねじれ点体である。q-pilot の入力 `QI` は、モジュライ体の指定された悪い素点の上にある $D.F$ の悪い素点の有限性と、$D.F$ の各有限素点の剰余次数の正値性を与える。体の塔の算術条件は同じ $D$、`LT`、`TL` について R4 とステップ (ii)、(iii) を与える。仮定は次の六つの関係も与える。$X=\mathrm{concreteVariantData}(D,LT,TL,QI)$ とする。$D_0,C_0$ はそれぞれ $D$ の三脚体の正規化した不同イデアルの対数次数と導手の対数次数である。$X$ は初期データ $D$、`QI` から得た q-pilot、および `TL` から得た右辺のデータを含む。$X.\mathrm{dmod}$ はモジュライ体の $\mathbb Q$ 上の次数である。 [具体的なデータと述語](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:24) · [体の塔の算術条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173)

$$
\begin{gathered}
X.\ell=\ell,\qquad X.\mathrm{dmod}\le d,\qquad
X.\mathrm{qPilot.logQ}=L.\mathrm{heightOther}(2,\ell),\\
T.\mathrm{logDiff}(T.\mathrm{tripod},x)=D_0,\\
C_0\le T.\mathrm{logCond}(T.\mathrm{tripod},x)\le C_0+\log(2\ell).
\end{gathered}
$$

q-pilot の対数は、$D.F$ の指定された悪い素点にわたる $(f_w/[D.F:\mathbb Q])\operatorname{qOrder}(w)\log p_w$ の和である。$f_w$ は剰余次数、$p_w$ は剰余標数である。$L.\mathrm{heightOther}(2,\ell)$ は、$L.\mathrm{bad}$ のうち $L.\mathrm{p}(w)\notin\{2,\ell\}$ を満たす項 $L.\mathrm{hv}(w)L.\mathrm{f}(w)\log L.\mathrm{p}(w)$ の和を $L.\mathrm{deg}$ で割った値である。$D_0$ は不同イデアルの絶対ノルムの対数を三脚体の次数で割った値である。$C_0$ は、$D.F$ の指定された悪い素点の下にある三脚体の有限素点の対数ノルムを足し、同じ次数で割った値である。 [局所高さの項](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts.lean:31) · [正規化した対数次数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

定理は $X$ と $\mathrm{inv}=\mathrm{TL.invariants}(QI)$ を存在の証拠として与える。述語 `IsConcrete X` は、ある $D$、`LT`、`TL`、`QI` から作る具体的なデータと $X$ が等しいことを要求する。ここでは同じ入力でこの等式を証明する。結論は上の六つの関係を保ち、$\mathrm{inv.logDtpd}=D_0$、$\mathrm{inv.logFtpd}=C_0$ となる。`Theorem110Certificate inv` と `Nonempty inv.LocalEstimate` も与える。証明書は $7\le X.\ell$、q-pilot の悪い素点の台に属する各素点の剰余標数が $\mathrm{inv.dst}$ に属すること、およびステップ (ii)、(iii) を記録する。$S=\mathrm{inv.dst}$ とすると、これらのステップは $\sum_{p\in S}\mathrm{LT.logDK}(p)\le D_0+C_0+2\log\ell+21$ と $\sum_{p\in S}\log p\le2X.\mathrm{dmod}(D_0+C_0)+5+\log\ell$ を与える。局所評価は同じ不変量に対する `TA.localEstimate` である。各カプセルと有理素点について Θ-pilot を含む包絡領域を与える。指定された素数以外の素数では、その領域は整領域に等しい。指定された素数と無限素点でのパケット対数体積の上界、および包絡領域の間の単調性を与える。 [存在の証拠の構成](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:55) · [証明書のフィールド](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Invariants.lean:240) · [局所評価のフィールド](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_LogVolumeBound.lean:116)

### `CurveInputs.concreteThetaDataExistence`

高さ理論 $T$、コンパクト有界集合のパラメータ $K:T.\mathrm{CBS}$、自然数 $d$、遠アーベル幾何学 `AG`、およびその緩和幾何学 `TG` を固定する。`CI : CurveInputs.{u} T AG K d` と `anab : AnabelianExistence AG TG` を取る。幾何学的な入力は、大域データ、許容素数のデータ、Tate 族、および普遍的なコア条件を受け取り、モジュライ体からねじれ点体への標準包含の上で、軌道曲線とその曲線に従属する局所幾何データの存在を与える。定理は次の三つの供給関数を取る。 [幾何学的な入力](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutInitialThetaData.lean:26) · [供給関数の量化](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveConcreteExistence.lean:24)

- 各 `D : InitialThetaData AG TG` に対し、`LTp D` は `LocalTheory.{u,v} D.Kt` を与える。
- このような各 $D$ と各 `LT : LocalTheory.{u,v} D.Kt` に対し、`TLp D LT` は `ThetaLocalData D LT` を与える。
- このような各 $D$、`LT`、および各 `TL : ThetaLocalData D LT` に対し、`TAp D LT TL` は `TowerArithmetic D LT TL` を与える。

$I=\mathrm{CI.toCorollary22Inputs}$ とする。結論 `ConcreteThetaDataExistence I` は、$T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ に属する各点 $x$ とその所属証明 $h_x$ に適用される。$x\notin I.\mathrm{excCore}$ とする。各素数 $\ell\ge7$ について $L=I.\mathrm{localData}(x,h_x)$ とし、P2、P3、P5、P6 を仮定する。P2 は選んだ曲線が乗法的還元を持つ各素点で、整数の Tate 位数が $\ell$ で割り切れないことを要求する。P3 は、そのうち剰余標数が $\ell$ の各素点で、Tate 位数を実数とみなした値が $\sqrt{I.\mathrm{h}(x)}$ より小さいことを要求する。P5 は、剰余標数が $\{2,\ell\}$ の外にある乗法的還元の素点の存在を要求する。P6 は各所属証明と各素数性の証明に対応する mod $\ell$ 表現の像が $\mathrm{SL}_2(\mathbb Z/\ell\mathbb Z)$ を含むことを要求する。コアの例外集合には、対応する曲線が普遍的なコア条件を満たさないような所属証明が存在する点が入る。この条件は、標数零の体への各埋め込みに沿って底変換した後に、一点を除いた曲線の符号の対合による商がそのコアを与えることを要求する。 [具体的な P7 の量化](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:36) · [曲線の入力と像の述語](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:136)

構成は `CI.exists_initialThetaData` から、その点と素数の初期 Θ データ $D$、q-pilot の入力 `QI`、および六つの関係を得る。この曲線の構成には、点と素数の条件に加えて P2、P5、P6 を用いる。残りの証拠には `LT := LTp D`、`TL := TLp D LT`、および `TAp D LT TL` を取る。$X=\mathrm{concreteVariantData}(D,LT,TL,QI)$ とする。q-pilot の入力は、$D$ の定義体で指定された悪い素点の有限性と、各有限素点の剰余次数の正値性を与える。結論は次の関係を与える。$X$ の素数とモジュライ体の次数は $D$ から取る。

$$
\begin{gathered}
X.\ell=\ell,\qquad X.\mathrm{dmod}\le d,\qquad
X.\mathrm{qPilot.logQ}=L.\mathrm{heightOther}(2,\ell),\\
T.\mathrm{logDiff}(T.\mathrm{tripod},x)=D_0,\\
C_0\le T.\mathrm{logCond}(T.\mathrm{tripod},x)\le C_0+\log(2\ell).
\end{gathered}
$$

$L.\mathrm{heightOther}(2,\ell)$ は、剰余標数が $\{2,\ell\}$ の外にある悪い素点について局所項 $L.\mathrm{hv}(w)L.\mathrm{f}(w)\log L.\mathrm{p}(w)$ を足し、$L.\mathrm{deg}$ で割った値である。$D_0,C_0$ はそれぞれ、三脚体の正規化した不同イデアルの対数次数と導手の対数次数である。 [曲線の構成と比較](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutPointThetaData.lean:73) · [存在の証拠](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveConcreteExistence.lean:31)

算術条件の証拠は $S=\mathrm{TL.dst}$ を用いる。これは $\{2,3,5,\ell\}$、`TL.badChars`、および $D.Kt$ で $\mathbb Q$ 上分岐する有限素点の剰余標数の和集合である。R4 は $D.Kt$ の各有限素点に適用される。$p$ は剰余標数、$e$ は絶対分岐指数であり、$p-2$ は自然数の減算である。残りのフィールドは同じ $S$ についてステップ (ii)、(iii) を与える。ここで $d_{\mathrm{mod}}=D.\mathrm{dmod}$ とし、$\mathrm{LT.logDK}(p)$ は $D.Kt$ の正規化した不同イデアルの対数次数への $p$ の寄与である。

$$
\begin{aligned}
p-2<e &\ \Longrightarrow\ \bigl(p\le552960d_{\mathrm{mod}}\ell
\ \land\ \log e\le-3+4\log(552960d_{\mathrm{mod}}\ell)\bigr),\\
\sum_{p\in S}\mathrm{LT.logDK}(p)&\le D_0+C_0+2\log\ell+21,\\
\sum_{p\in S}\log p&\le2d_{\mathrm{mod}}(D_0+C_0)+5+\log\ell .
\end{aligned}
$$

[指定された素数と局所不同イデアルの項](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:29) · [三つの算術フィールド](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173)

## 消费者与存档回执

`ConcreteThetaDataExistence.toThetaDataExistence` 由 `canonicalCorollary22HighHeightEstimate_of_source` 直接调用。存档审查也将它传入 `I.c2`，使用 `IsConcrete X` 的等式把假设的具体数据 Corollary 3.12 变体应用到同一个 $X$。随后 `I.c2` 将算术证书、局部估计及该变体传给 `inv.theorem110`。 [规范入口](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCanonicalCorollary22.lean:55) · [审查调用](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/ReviewConcreteExistence.lean:35) · [推论 2.2 消费点](/home/admin-wsl/Coq/abc/prove2me_workspace/Theorems/Thm_AbcAdaptation_Reference_Iut_Corollary22Inputs_c2.lean:210)

`CurveInputs.concreteThetaDataExistence` 提供同一种具体存在性前提。仓库内按名称直接引用它的是存档审查的 `#check` 与 `#print axioms`。来源 P7 的具体实例调用 `concreteThetaDataExistence_of_localArithmetic`，以该点所选初始数据的局部算术形成见证。 [供给器审查](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/ReviewConcreteExistence.lean:17) · [来源 P7 组装](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodP7.lean:95)

| Lean 源码 | 现行 SHA-256 | 存档回执 |
| --- | --- | --- |
| `Source_ReferenceIutConcreteExistence.lean` | `e1e8fba4df2d83e8dd7a602af500122bf5a2654c23091fa6898bf07c9e9cf74f` | [产物检查 ci-021390-964c6d68](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021390-964c6d68-result.json) |
| `Source_ReferenceIutCurveConcreteExistence.lean` | `4efe580fb10d983030cd1edbc7c541f85c9a2f3ed4594efc8c68f97fe02810fb` | [现行模块叶检查 ci-021734-e798309d](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021734-e798309d-result.json) |

存档审查 `ci-021440-f6c510e9` 对这两条声明均只报告 `propext`、`Classical.choice` 和 `Quot.sound`，且 `no_sorryAx = true`。审查中的供给器模块 SHA-256 为 `6be153f264aa99f3c49b5d16e856d137f1e4532d01896d56668047ebd6451b55`。从现行文件移去新增的坏剩余特征模块导入和逐点版声明块，得到该旧散列，核实供给器版声明和证明的文本与审查输入逐字节相同。现行模块的直接公理审查 `ci-021743-f33906a6` 的相关目标是逐点版 `concreteThetaDataExistence_of_pointwise`。这些回执的运行模式为独占工作区、无快照，退出码为 $0$。 [转换与供给器审查 ci-021440-f6c510e9](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021440-f6c510e9-result.json) · [旧供给器产物检查 ci-021418-6ae2447f](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021418-6ae2447f-result.json) · [逐点版审查 ci-021743-f33906a6](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021743-f33906a6-result.json) · [来源台账](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md:321)
