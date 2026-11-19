# The normalized different bound and tower arithmetic

## English

### `logDifferentDeg_torsionField_le`

Let $F$ be a number field and $E/F$ an elliptic Weierstrass curve. Let $\overline F$ be a field with an $F$-algebra structure in the same Lean universe as $F$. Write $F_{\mathrm{mod}}=\mathbb Q(j(E))$ and $F_{\mathrm{tpd}}=\operatorname{tripodalFieldOf}(F,E)$. The latter is the subfield of $F$ generated over $\mathbb Q$ by $j(E)$ and the $x$-coordinates of the affine $F$-rational points killed by $2$. Take a set `VBad` of finite places of $F_{\mathrm{mod}}$ and `Pr : AdmissiblePrimeData F E Fbar VBad`. Use the prime $\ell$ from `Pr.ℓ` and let $K$ be the carrier of `Pr.torsionField`, the fixed field of the kernel of the supplied representation in $\overline F$. Assume that $K$ is a number field. [Parameters](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerDifferent.lean:26) · [Local facts](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerLocalFacts.lean:124)

Assume `H : TowerLocalFacts E VBad Pr` and that `badPlacesOver F E VBad` is finite. That set is the set of finite places of $F$ that lie above some member of `VBad`. Then

$$
\operatorname{logDifferentDeg}(K)
\le \operatorname{logDifferentDeg}(F_{\mathrm{tpd}})
+\operatorname{logConductorDegOf}(F,E,\texttt{VBad})+2\log\ell+21.
$$

For a number field $L$, $\operatorname{logDifferentDeg}(L)$ is $\log N(\mathfrak D_{L/\mathbb Q})/[L:\mathbb Q]$, using the absolute norm of the different ideal. The term `logConductorDegOf F E VBad` sums $\log N(\mathfrak p)$ over the finite places of $F_{\mathrm{tpd}}$ below some member of `badPlacesOver F E VBad`. It divides the sum by $[F_{\mathrm{tpd}}:\mathbb Q]$. All logarithms are real natural logarithms. [Normalizations](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24) · [Local theorem](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerDifferent.lean:162) · [Pinned iut theorem](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tower/Different.lean#L390)

### `towerArithmetic_of_localFacts`

Fix `AG : AnabelianGeometry.{u}` and `TG : TemperedGeometry AG`. Take `D : InitialThetaData AG TG`, `LT : LocalTheory.{u,v} D.Kt`, and `TL : ThetaLocalData D LT`. Use $F=D.F$, $E=D.E$, `VBad = D.VBad`, and `Pr = D.prime` in the notation above. Thus $K=D.Kt$, and $d_{\mathrm{mod}}=[F_{\mathrm{mod}}:\mathbb Q]$ is `D.dmod`. The data $D$ supply the field and curve instances, including the number-field instance on $K$. [Initial theta data](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Basic.lean:106) · [Torsion field and local data](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:41)

Assume the following hypotheses for these data.

- `H : TowerLocalFacts D.E D.VBad D.prime`.
- `he2 : RelRamIdxModLeTwo D.E D.VBad`. At each finite place of $F_{\mathrm{tpd}}$ over a member of `D.VBad`, the relative ramification index over $F_{\mathrm{mod}}$ is at most $2$.
- The extension $F_{\mathrm{tpd}}/F_{\mathrm{mod}}$ is Galois.
- $[F_{\mathrm{tpd}}:F_{\mathrm{mod}}]\le 6$.
- $[F:\mathbb Q]\le 552960\,[F_{\mathrm{tpd}}:\mathbb Q]$.
- `badPlacesOver D.F D.E D.VBad` is finite.
- For each $p$ in `TL.badChars`, some finite place $w$ in `badPlacesOver D.F D.E D.VBad` has residue characteristic $p$.

The theorem gives `TowerArithmetic D LT TL` with the following three bounds. The finite set `TL.dst` is the union of $\{2,3,5,\ell\}$, `TL.badChars`, and `LT.ramifiedChars`. The last set consists of residue characteristics at finite places of $K$ whose absolute ramification index differs from $1$. [Assembly hypotheses](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerArithmetic.lean:27) · [Relative ramification](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerLocalFacts.lean:116) · [Distinguished primes](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:62)

**(R4).** For each finite place $v$ of $K$, write $p_v$ for its residue characteristic and $e_v$ for its absolute ramification index. If $p_v-2<e_v$ with subtraction in $\mathbb N$, then

$$
p_v\le 552960\,d_{\mathrm{mod}}\ell,\qquad
\log e_v\le -3+4\log(552960\,d_{\mathrm{mod}}\ell).
$$

**Step (ii).** The same `LT` supplies `LT.logDK p`, the contribution of the rational prime $p$ to the normalized different degree. The bound is

$$
\sum_{p\in\texttt{TL.dst}}\operatorname{LT.logDK}(p)
\le \operatorname{logDifferentDeg}(F_{\mathrm{tpd}})
+\operatorname{logConductorDegOf}(F,E,\texttt{VBad})+2\log\ell+21.
$$

**Step (iii).** The sum over the same `TL.dst` satisfies

$$
\sum_{p\in\texttt{TL.dst}}\log p
\le 2d_{\mathrm{mod}}\bigl(\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})
+\operatorname{logConductorDegOf}(F,E,\texttt{VBad})\bigr)+5+\log\ell.
$$

The proof of Step (ii) uses $\sum_{p\in\texttt{TL.dst}}\operatorname{LT.logDK}(p)=\operatorname{logDifferentDeg}(K)$ and applies the first theorem with `D.prime`, `H`, and the same finiteness proof. [Three fields](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173) · [Local contribution](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:34) · [Different-degree identity](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteDifferentDegree.lean:126) · [Pinned iut theorem](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tower/Main.lean#L42)

## 中文

### `logDifferentDeg_torsionField_le`

设 $F$ 为数域，$E/F$ 为 Weierstrass 椭圆曲线。设 $\overline F$ 为带有 $F$-代数结构的域，与 $F$ 属于同一 Lean 宇宙层级。记 $F_{\mathrm{mod}}=\mathbb Q(j(E))$，$F_{\mathrm{tpd}}=\operatorname{tripodalFieldOf}(F,E)$。后者是 $F$ 中由 $j(E)$ 与 $E$ 上被 $2$ 消去的仿射 $F$-有理点的横坐标在 $\mathbb Q$ 上生成的子域。取 $F_{\mathrm{mod}}$ 的有限位集合 `VBad` 以及 `Pr : AdmissiblePrimeData F E Fbar VBad`。令 $\ell$ 为 `Pr.ℓ`，令 $K$ 为 `Pr.torsionField` 的载体，即给定表示的核在 $\overline F$ 中的不动域。假设 $K$ 为数域。 [参数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerDifferent.lean:26) · [局部条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerLocalFacts.lean:124)

假设 `H : TowerLocalFacts E VBad Pr` 成立，并且 `badPlacesOver F E VBad` 是有限集合。该集合由 $F$ 中位于某个 `VBad` 成员上方的有限位组成。则

$$
\operatorname{logDifferentDeg}(K)
\le \operatorname{logDifferentDeg}(F_{\mathrm{tpd}})
+\operatorname{logConductorDegOf}(F,E,\texttt{VBad})+2\log\ell+21.
$$

对任意数域 $L$，$\operatorname{logDifferentDeg}(L)$ 等于 $\log N(\mathfrak D_{L/\mathbb Q})/[L:\mathbb Q]$，其中 $N$ 为不同理想的绝对范数。导子项 `logConductorDegOf F E VBad` 对 $F_{\mathrm{tpd}}$ 中位于某个 `badPlacesOver F E VBad` 成员下方的有限位求 $\log N(\mathfrak p)$ 之和，再除以 $[F_{\mathrm{tpd}}:\mathbb Q]$。所有对数均为实自然对数。 [归一化定义](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24) · [本地定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerDifferent.lean:162) · [固定版本的 iut 定理](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tower/Different.lean#L390)

### `towerArithmetic_of_localFacts`

固定 `AG : AnabelianGeometry.{u}` 和 `TG : TemperedGeometry AG`。取 `D : InitialThetaData AG TG`、`LT : LocalTheory.{u,v} D.Kt` 和 `TL : ThetaLocalData D LT`。在上述记号中，令 $F=D.F$、$E=D.E$、`VBad = D.VBad`、`Pr = D.prime`。于是 $K=D.Kt$，且 $d_{\mathrm{mod}}=[F_{\mathrm{mod}}:\mathbb Q]$ 即 `D.dmod`。域和曲线的实例由 $D$ 给出，其中包括 $K$ 的数域实例。 [初始 theta 数据](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Basic.lean:106) · [挠点域与局部数据](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:41)

对这些数据作如下假设。

- `H : TowerLocalFacts D.E D.VBad D.prime`。
- `he2 : RelRamIdxModLeTwo D.E D.VBad`。$F_{\mathrm{tpd}}$ 的每个有限位若位于某个 `D.VBad` 成员上方，则相对于 $F_{\mathrm{mod}}$ 的分歧指数至多为 $2$。
- $F_{\mathrm{tpd}}/F_{\mathrm{mod}}$ 是 Galois 扩张。
- $[F_{\mathrm{tpd}}:F_{\mathrm{mod}}]\le 6$。
- $[F:\mathbb Q]\le 552960\,[F_{\mathrm{tpd}}:\mathbb Q]$。
- `badPlacesOver D.F D.E D.VBad` 是有限集合。
- 对 `TL.badChars` 中的每个 $p$，存在 `badPlacesOver D.F D.E D.VBad` 中的有限位 $w$，其剩余特征为 $p$。

定理给出 `TowerArithmetic D LT TL`，包含以下三个界。有限集合 `TL.dst` 是 $\{2,3,5,\ell\}$、`TL.badChars` 和 `LT.ramifiedChars` 的并集。最后一个集合由 $K$ 中绝对分歧指数异于 $1$ 的有限位的剩余特征组成。 [组装假设](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerArithmetic.lean:27) · [相对分歧](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerLocalFacts.lean:116) · [素数集合](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:62)

**(R4)** 对 $K$ 的每个有限位 $v$，记 $p_v$ 为其剩余特征，$e_v$ 为其绝对分歧指数。若在 $\mathbb N$ 中作减法有 $p_v-2<e_v$，则

$$
p_v\le 552960\,d_{\mathrm{mod}}\ell,\qquad
\log e_v\le -3+4\log(552960\,d_{\mathrm{mod}}\ell).
$$

**步骤 (ii)** 同一个 `LT` 给出有理素数 $p$ 对归一化不同理想次数的贡献 `LT.logDK p`。不等式为

$$
\sum_{p\in\texttt{TL.dst}}\operatorname{LT.logDK}(p)
\le \operatorname{logDifferentDeg}(F_{\mathrm{tpd}})
+\operatorname{logConductorDegOf}(F,E,\texttt{VBad})+2\log\ell+21.
$$

**步骤 (iii)** 在同一个 `TL.dst` 上的求和满足

$$
\sum_{p\in\texttt{TL.dst}}\log p
\le 2d_{\mathrm{mod}}\bigl(\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})
+\operatorname{logConductorDegOf}(F,E,\texttt{VBad})\bigr)+5+\log\ell.
$$

步骤 (ii) 的证明使用 $\sum_{p\in\texttt{TL.dst}}\operatorname{LT.logDK}(p)=\operatorname{logDifferentDeg}(K)$，再以 `D.prime`、`H` 和同一个有限性证明应用前一定理。 [三个字段](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173) · [局部贡献](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:34) · [不同理想次数等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteDifferentDegree.lean:126) · [固定版本的 iut 定理](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tower/Main.lean#L42)

## 日本語

### `logDifferentDeg_torsionField_le`

$F$ を数体とし、$E/F$ を Weierstrass 楕円曲線とする。$\overline F$ を $F$-代数構造を持つ体とする。$F$ と $\overline F$ は同じ Lean 宇宙階層に属する。$F_{\mathrm{mod}}=\mathbb Q(j(E))$、$F_{\mathrm{tpd}}=\operatorname{tripodalFieldOf}(F,E)$ と書く。後者は、$j(E)$ と、$2$ 倍が零になる $E$ のアフィンな $F$-有理点の $x$ 座標が $\mathbb Q$ 上生成する $F$ の部分体である。$F_{\mathrm{mod}}$ の有限素点の集合 `VBad` と `Pr : AdmissiblePrimeData F E Fbar VBad` を取る。$\ell$ を `Pr.ℓ` とし、`Pr.torsionField` の台となる体を $K$ とする。これは与えられた表現の核による $\overline F$ の固定体である。$K$ は数体と仮定する。 [引数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerDifferent.lean:26) · [局所条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerLocalFacts.lean:124)

`H : TowerLocalFacts E VBad Pr` と `badPlacesOver F E VBad` の有限性を仮定する。この集合は、`VBad` のいずれかの元の上にある $F$ の有限素点からなる。このとき次が成り立つ。

$$
\operatorname{logDifferentDeg}(K)
\le \operatorname{logDifferentDeg}(F_{\mathrm{tpd}})
+\operatorname{logConductorDegOf}(F,E,\texttt{VBad})+2\log\ell+21.
$$

数体 $L$ について、$\operatorname{logDifferentDeg}(L)$ はディファレントの絶対ノルムを用いた $\log N(\mathfrak D_{L/\mathbb Q})/[L:\mathbb Q]$ である。導手の項 `logConductorDegOf F E VBad` は、`badPlacesOver F E VBad` のいずれかの元の下にある $F_{\mathrm{tpd}}$ の有限素点について $\log N(\mathfrak p)$ を足し、その和を $[F_{\mathrm{tpd}}:\mathbb Q]$ で割ったものである。対数はすべて実数の自然対数である。 [正規化の定義](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24) · [ローカルの定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerDifferent.lean:162) · [固定リビジョンの iut の定理](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tower/Different.lean#L390)

### `towerArithmetic_of_localFacts`

`AG : AnabelianGeometry.{u}` と `TG : TemperedGeometry AG` を固定する。`D : InitialThetaData AG TG`、`LT : LocalTheory.{u,v} D.Kt`、`TL : ThetaLocalData D LT` を取る。上の記号で $F=D.F$、$E=D.E$、`VBad = D.VBad`、`Pr = D.prime` とおく。このとき $K=D.Kt$ であり、$d_{\mathrm{mod}}=[F_{\mathrm{mod}}:\mathbb Q]$ は `D.dmod` である。$K$ の数体インスタンスを含め、体と曲線のインスタンスは $D$ が与える。 [初期 theta データ](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Basic.lean:106) · [ねじれ点体と局所データ](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:41)

これらのデータに対して次を仮定する。

- `H : TowerLocalFacts D.E D.VBad D.prime`。
- `he2 : RelRamIdxModLeTwo D.E D.VBad`。`D.VBad` のいずれかの元の上にある $F_{\mathrm{tpd}}$ の各有限素点で、$F_{\mathrm{mod}}$ に対する相対分岐指数は $2$ 以下である。
- $F_{\mathrm{tpd}}/F_{\mathrm{mod}}$ は Galois 拡大である。
- $[F_{\mathrm{tpd}}:F_{\mathrm{mod}}]\le 6$。
- $[F:\mathbb Q]\le 552960\,[F_{\mathrm{tpd}}:\mathbb Q]$。
- `badPlacesOver D.F D.E D.VBad` は有限である。
- `TL.badChars` の各 $p$ について、`badPlacesOver D.F D.E D.VBad` に属し剰余標数が $p$ である有限素点 $w$ が存在する。

定理は次の三つの評価を持つ `TowerArithmetic D LT TL` を与える。有限集合 `TL.dst` は $\{2,3,5,\ell\}$、`TL.badChars`、`LT.ramifiedChars` の和集合である。最後の集合は、絶対分岐指数が $1$ と異なる $K$ の有限素点の剰余標数からなる。 [組み立ての仮定](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerArithmetic.lean:27) · [相対分岐](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerLocalFacts.lean:116) · [素数の集合](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:62)

**(R4)** $K$ の各有限素点 $v$ に対して、剰余標数を $p_v$、絶対分岐指数を $e_v$ と書く。$\mathbb N$ の減法で $p_v-2<e_v$ が成り立つならば、次が成り立つ。

$$
p_v\le 552960\,d_{\mathrm{mod}}\ell,\qquad
\log e_v\le -3+4\log(552960\,d_{\mathrm{mod}}\ell).
$$

**ステップ (ii)** 同じ `LT` は、正規化したディファレントの次数への有理素数 $p$ の寄与 `LT.logDK p` を与える。不等式は次の通りである。

$$
\sum_{p\in\texttt{TL.dst}}\operatorname{LT.logDK}(p)
\le \operatorname{logDifferentDeg}(F_{\mathrm{tpd}})
+\operatorname{logConductorDegOf}(F,E,\texttt{VBad})+2\log\ell+21.
$$

**ステップ (iii)** 同じ `TL.dst` 上の和について次が成り立つ。

$$
\sum_{p\in\texttt{TL.dst}}\log p
\le 2d_{\mathrm{mod}}\bigl(\operatorname{logDifferentDeg}(F_{\mathrm{tpd}})
+\operatorname{logConductorDegOf}(F,E,\texttt{VBad})\bigr)+5+\log\ell.
$$

ステップ (ii) の証明では $\sum_{p\in\texttt{TL.dst}}\operatorname{LT.logDK}(p)=\operatorname{logDifferentDeg}(K)$ を用い、`D.prime`、`H`、同じ有限性の証明を使って最初の定理を適用する。 [三つのフィールド](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173) · [局所的な寄与](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:34) · [ディファレントの次数の等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteDifferentDegree.lean:126) · [固定リビジョンの iut の定理](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tower/Main.lean#L42)
