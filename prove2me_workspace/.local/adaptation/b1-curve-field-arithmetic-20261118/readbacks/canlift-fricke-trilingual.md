# Fricke 迹恒等式 · Fricke trace identity · Fricke の跡恒等式

| 简体中文 | English | 日本語 |
| --- | --- | --- |
| 交换子 | commutator | 交換子 |
| 矩阵迹 | matrix trace | 行列の跡 |
| 边配对矩阵 | edge-pairing matrix | 辺同一視の行列 |
| 可公度子 | commensurator | commensurator |
| Vieta 对合 | Vieta involution | Vieta 対合 |

## 交换子与迹 · The commutator and the traces · 交換子と跡

**简体中文**　设 $R$ 为交换环，$A,B\in\mathrm{SL}_2(R)$，记 $x=\operatorname{tr}A$、$y=\operatorname{tr}B$、$z=\operatorname{tr}(AB)$。按 $[A,B]=ABA^{-1}B^{-1}$ 的次序，Fricke 恒等式给出

$$\operatorname{tr}[A,B]=x^2+y^2+z^2-xyz-2.$$

展开矩阵条目，以伴随矩阵表示行列式为一的矩阵的逆，再代入 $\det A=\det B=1$，即可证明该恒等式。因此 $\operatorname{tr}[A,B]=-2$ 等价于 $x^2+y^2+z^2=xyz$。将第一个生成元改为 $A^{-1}$ 时，三个迹变为 $(x,y,xy-z)$。 [固定上游的 Fricke 证明](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fricke.lean#L54)

**English**　Let $R$ be a commutative ring and let $A,B\in\mathrm{SL}_2(R)$. Set $x=\operatorname{tr}A$, $y=\operatorname{tr}B$, and $z=\operatorname{tr}(AB)$. Use the commutator order $[A,B]=ABA^{-1}B^{-1}$. Fricke's identity gives $\operatorname{tr}[A,B]=x^2+y^2+z^2-xyz-2$. Expand the matrix entries, express the inverses as adjugates, and use $\det A=\det B=1$. Thus $\operatorname{tr}[A,B]=-2$ if and only if $x^2+y^2+z^2=xyz$. Replacing the first generator with $A^{-1}$ changes the three traces to $(x,y,xy-z)$. [Pinned Fricke proof](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fricke.lean#L54)

**日本語**　可換環 $R$ と $A,B\in\mathrm{SL}_2(R)$ を取る。$x=\operatorname{tr}A$、$y=\operatorname{tr}B$、$z=\operatorname{tr}(AB)$ と置く。交換子を $[A,B]=ABA^{-1}B^{-1}$ とすると、Fricke の恒等式により $\operatorname{tr}[A,B]=x^2+y^2+z^2-xyz-2$ が成り立つ。行列の成分を展開し、逆行列を余因子行列の転置で表して、$\det A=\det B=1$ を用いればよい。したがって $\operatorname{tr}[A,B]=-2$ と $x^2+y^2+z^2=xyz$ は同値である。第一生成元を $A^{-1}$ に置き換えると、三つの跡は $(x,y,xy-z)$ となる。 [固定した上流の Fricke の証明](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fricke.lean#L54)

## 格覆盖上的严格迹界 · Strict trace bounds for the lattice covering · 格子被覆に対する跡の厳密な下界

**简体中文**　设 $t\in\mathbb H$，$U$ 为 `LatticeComplementCover (periodPair t)`，取其边配对矩阵 $A=A(U)$、$B=B(U)$。本地 `Peripheral.trace_commutator` 和 `Peripheral.trace_A_ne_zero` 给出 $\operatorname{tr}[A,B]=-2$ 和 $x\ne0$。Fricke 关系说明 $xyz=x^2+y^2+z^2>0$，所以每个迹均非零。若 $x^2\le4$，则 $|x|\le2$ 且 $xyz\le2|y||z|\le y^2+z^2$，与 $x^2>0$ 矛盾。轮换坐标即得 $x^2,y^2,z^2>4$。稠密性判据使用 $x^2>4$、$y\ne0$ 和 $\operatorname{tr}[A,B]\ne2$。这些条件都来自同一个覆盖的边配对矩阵。 [上游迹界](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fuchsian/Commensurator.lean#L73) · [本地格覆盖交换子迹](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeCommutatorTrace.lean:262) · [格覆盖迹界草稿](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftFrickeSquaredTraces.lean:51)

**English**　Let $t\in\mathbb H$ and let $U$ have type `LatticeComplementCover (periodPair t)`. Use its edge-pairing matrices $A=A(U)$ and $B=B(U)$. The local proofs give $\operatorname{tr}[A,B]=-2$ and $x\ne0$. The Fricke equation gives $xyz=x^2+y^2+z^2>0$, so each trace is nonzero. If $x^2\le4$, then $|x|\le2$ and $xyz\le2|y||z|\le y^2+z^2$. This contradicts $x^2>0$. Apply the same argument to each trace to obtain $x^2,y^2,z^2>4$. The density criterion uses $x^2>4$, $y\ne0$, and $\operatorname{tr}[A,B]\ne2$ for the matrices from $U$. [Pinned strict bound](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fuchsian/Commensurator.lean#L73) · [Local lattice commutator trace](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeCommutatorTrace.lean:262) · [Lattice bound draft](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftFrickeSquaredTraces.lean:51)

**日本語**　$t\in\mathbb H$ と `LatticeComplementCover (periodPair t)` 型の $U$ を取り、その辺同一視の行列を $A=A(U)$、$B=B(U)$ とする。局所証明により $\operatorname{tr}[A,B]=-2$ と $x\ne0$ が成り立つ。Fricke の方程式から $xyz=x^2+y^2+z^2>0$ であり、三つの跡はいずれも零でない。$x^2\le4$ ならば $|x|\le2$ で、$xyz\le2|y||z|\le y^2+z^2$ となり、$x^2>0$ に矛盾する。各座標に同じ議論を適用すると $x^2,y^2,z^2>4$ を得る。稠密性の判定条件は、同じ被覆 $U$ の行列について $x^2>4$、$y\ne0$、$\operatorname{tr}[A,B]\ne2$ を用いる。 [固定した上流の跡の下界](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fuchsian/Commensurator.lean#L73) · [格子被覆の交換子の跡](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeCommutatorTrace.lean:262) · [格子被覆に対する下界の草稿](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftFrickeSquaredTraces.lean:51)

## 整数约化的输入 · Inputs to the integer reduction · 整数への帰着の入力

**简体中文**　若 $X=x^2,Y=y^2,Z=z^2$ 均为整数，将 Fricke 关系平方即得 $(X+Y+Z)^2=XYZ$。Vieta 对合把第三个整数改为 $XY-2(X+Y+Z)+Z$，对应于新生成元对 $(A^{-1},B)$。Takeuchi 约化对同一个生成子群使用这些变换。它需要子群的所有元素都有整数平方迹，从而每一轮新生成元的平方迹仍可取为整数。 [Vieta 对合](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Takeuchi.lean#L84) · [整数转换](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Takeuchi.lean#L109) · [约化定理](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Takeuchi.lean#L317)

**English**　Suppose $X=x^2$, $Y=y^2$, and $Z=z^2$ are integers. Square the Fricke equation to obtain $(X+Y+Z)^2=XYZ$. The Vieta involution replaces the third integer with $XY-2(X+Y+Z)+Z$. This comes from the generator pair $(A^{-1},B)$. Takeuchi's reduction applies these moves within the same generated subgroup. It requires integral squared traces for every group element. This gives integral squared traces for each new pair of generators. [Vieta involution](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Takeuchi.lean#L84) · [Integer conversion](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Takeuchi.lean#L109) · [Reduction theorem](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Takeuchi.lean#L317)

**日本語**　$X=x^2$、$Y=y^2$、$Z=z^2$ がすべて整数であるとする。Fricke の方程式の両辺を平方すると $(X+Y+Z)^2=XYZ$ を得る。Vieta 対合は第三の整数を $XY-2(X+Y+Z)+Z$ に移す。これは生成元の組 $(A^{-1},B)$ に対応する。竹内の簡約では、同一の生成部分群の中でこれらの変換を用いる。部分群の各元の跡の平方が整数であるという仮定により、新しい生成元の組でも跡の平方は整数になる。 [Vieta 対合](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Takeuchi.lean#L84) · [整数への移行](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Takeuchi.lean#L109) · [簡約定理](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Takeuchi.lean#L317)

## Source correspondence

| Local declaration or call | Pinned source | Correspondence |
| --- | --- | --- |
| `Fricke.tr_commutator`, `Fricke.tr_commutator_eq_neg_two_iff` | [Fricke.lean](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fricke.lean#L69) | Same statements over a commutative ring and same determinant identities. |
| `Fricke.tr_inv`, `Fricke.tr_mul_comm`, `Fricke.tr_inv_mul` | [Fricke.lean](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fricke.lean#L46) | Same trace rules for the Nielsen moves in `Realizes.swap`, `Realizes.cycle`, and `Realizes.flip`. |
| `Peripheral.fricke_trace_relation` and `Peripheral.traces_sq_gt_four` | [Commensurator.lean](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fuchsian/Commensurator.lean#L103) | Specialization to the generators of the lattice covering. The strict bound uses `abs_le_of_sq_le_sq` for the absolute value estimate. |
| `closure_commensurator_dense_of_relIndex_eq_zero` | [Commensurator.lean](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fuchsian/Commensurator.lean#L61) | The lattice wrapper uses the strict first trace bound and nonzero second trace. The index criterion uses the covolume of the signed deck group. [Reviewed consumer](/tmp/mcp-ci/01a1f575-a867-75d1-9ba5-04ce946763c8/discreteness_source/Source_ReferenceIutCanLiftDenseCommensurator.lean:54) |
| `Fricke.tr_pow`, `Fricke.exists_int_sq_tr_of_rat_of_int_pow` | [Fricke.lean](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fricke.lean#L98) · [ArithTraces.lean](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/ArithTraces.lean#L232) | Power trace draft. Mathlib's rescaled Chebyshev polynomials provide the Vieta–Lucas sequence. The integer conclusion uses a rational squared trace and a positive power with integer trace. |

The pinned chain uses dense-commensurator integrality to get the hypothesis of `takeuchi_one_infty_of_int`. The resulting generating pair is then matched with Takeuchi's four groups. `TheoremG` uses the nonexceptional \(j\)-invariant to exclude that case. [Dense integrality and reduction](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L639) · [Nonexceptional \(j\) in Theorem G](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/TheoremG.lean#L252)

This readback uses the source statements and the local drafts. MCP-CI verification belongs to the integrated workspace.
