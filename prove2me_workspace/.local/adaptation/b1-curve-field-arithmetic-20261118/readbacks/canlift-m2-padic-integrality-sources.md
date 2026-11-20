# CanLift 中从 p 进范数界到整数迹平方

固定来源为 `lana-agents/orbicurve-cores` 的 `61616dcd77fbe45c083a8ebfa7cc80728f86e841`。

## 本地证明与调用

- `M2.exists_int_of_padicNorm_le_one` 的陈述与上游相同。若既约分母不为一，取它的最小素因子 $p$。既约性保证分子的 $p$ 进范数为一，分母的 $p$ 进范数严格介于零与一之间。Mathlib 的范数除法公式使原有理数的 $p$ 进范数严格大于一。 [上游证明](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L289) · [本地证明](../../../../Solutions/Source_ReferenceIutCanLiftPadicIntegrality.lean#L16)
- `M2.trace_sq_eq_of_rational_rep` 直接接收 $g=cM$ 的矩阵等式，$g\in\mathrm{SL}_2(\mathbb R)$，$c\in\mathbb R$，$M\in\mathrm{Mat}_2(\mathbb Q)$。由 $c^2\det M=1$ 和迹的线性性，得到 $(\operatorname{tr}g)^2=(\operatorname{tr}M)^2/\det M$。上游 `trace_sq_eq` 对 `IsRatMul` 选取的代表元使用同一等式。 [上游矩阵恒等式](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L428) · [本地证明](../../../../Solutions/Source_ReferenceIutCanLiftPadicSquaredTraces.lean#L26)
- `M2.exists_int_sq_tr_of_padicNorm_le_one` 对比值应用有理数整性，再将整数强制转换到 $\mathbb R$。`M2.takeuchi_one_infty_of_padicNorm_le_one` 把这一步应用于同一生成子群的各个元素，消去 `Takeuchi.takeuchi_one_infty_of_int` 的整数迹平方前提。其结论保留生成子群相等、新交换子的迹为 $-2$，以及四组精确的迹平方。 [上游整性组装](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L546) · [本地桥接](../../../../Solutions/Source_ReferenceIutCanLiftPadicSquaredTraces.lean#L45) · [本地 Nielsen 约化](../../../../Solutions/Source_ReferenceIutCanLiftNielsenDescent.lean#L192)

## 固定来源的证明依赖

1. `exists_normal_form` 以交换子迹为 $-2$ 和第一个生成元的迹非零为输入。它通过 Nielsen 变换、符号和 $\mathrm{GL}_2(\mathbb R)$ 共轭得到正参数 $x,y,z$，Fricke 方程和三个严格三角不等式。`margulisDenseOneInfty` 把稠密性传给该正规形的可公度子。 [正规形](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fuchsian/OneInftyLattice.lean#L348) · [稠密性的传递](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L595)
2. `sq_fixed_of_dense` 对每个环嵌入 $\sigma\colon\mathbb R\to\mathbb C$ 构造可公度子在 $\mathbb P^1(\mathbb C)$ 上的作用。`goodLattice_normal`、`nonElem_of` 和 `unbounded_complex` 供应 `commensurator_superrigidity` 的格、非初等性与无界性条件。作用的连续延拓和 `complex_rigidity` 保证 $\sigma$ 固定 $x^2,y^2,z^2$。`sq_rat_of_dense` 使用 `exists_ringHom_real_complex_ne` 推出这三个平方均为有理数。 [复数步骤](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L224) · [非有理数的嵌入](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/ForMathlib/ComplexEmbedding.lean#L84)
3. `isRatMul_of_mem` 从这三个有理平方给出正规形生成群中每个元素的有理矩阵代表。`isRatMul_of_mem_commensurator` 使用共轭矩阵条目在迹域中的结果，将有理代表扩展到可公度子。`rep_unique` 和 `aP_smul` 证明不同有理代表产生相同的射影作用。`actsOn_aP` 给出其乘法相容性。 [群内有理代表](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Rational.lean#L143) · [代表的唯一性](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L340) · [p 进作用](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L371)
4. `padicNorm_trace_sq_le_one` 固定一个素数和一个正规形群元素。若该比值的范数大于一，`Padic.exists_degenerate_limit` 用 Hensel 引理证明该元素的幂使 $(0,1,\infty)$ 的像趋于有重复点的三元组。由此得到 `Unbounded`。`commensurator_superrigidity` 以同一 `GoodLattice` 和非初等作用作连续延拓。`padic_contradiction` 用实数中趋向零的 $2/p^n$ 和其在 $\mathbb Q_p$ 中的范数得到矛盾。 [p 进范数界](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L449) · [三元组极限](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/PadicUnbounded.lean#L119) · [不相容的连续性](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Unipotent.lean#L213)
5. `trace_sq_int_of_dense` 对每个群元素合用有理代表、各素数处的范数界、有理数整性和迹平方恒等式。`margulisDenseOneInfty` 利用迹平方在共轭与改符号下不变，将结果搬回初始生成子群，然后调用 `takeuchi_one_infty_of_int` 与 `exists_conj_of_takeuchiSq`。 [正规形整性](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L546) · [回传与分类](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L639)

`commensurator_superrigidity` 的核心调用依次是 `GoodLattice.exists_boundaryKernel`、`triple_null_of_unbounded`、`exists_pointMap_of_triple_null`、`ae_ne_of_equivariant`、`equivariant_commensurator` 和 `exists_extension`。局部桥接的 `hrep` 仍需上述有理代表、每个素数处的范数界，以及回到实际群的传递步骤。 [超刚性证明](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Superrigidity.lean#L54)

## English

If a rational number has a reduced denominator greater than one, choose a prime divisor of that denominator. Coprimality gives a numerator norm of one and a denominator norm strictly between zero and one. The quotient therefore has p-adic norm greater than one. When every prime norm is at most one, the denominator is one and the number is an integer.

If g in SL₂(ℝ) is a real scalar multiple of a rational matrix R, the determinant condition makes the square of that scalar times det R equal to one. The square of the trace of g is therefore the real image of (tr R)²/det R. Bounds on this rational quotient at every prime give an integer squared trace. Applying the result to each element of the generated subgroup supplies the integrality premise in the Nielsen reduction.

## 日本語

有理数の既約分母が一より大きければ、その分母を割る素数を一つ取る。互いに素であることから、分子のその素数での進ノルムは一であり、分母の進ノルムは零より大きく一より小さい。したがって商の進ノルムは一を超える。すべての素数で進ノルムが一以下なら、分母は一であり、もとの数は整数である。

SL₂(ℝ) の行列 g が有理行列 R の実数倍であるとき、行列式が一なので、比例係数の二乗と det R の積は一である。したがって g のトレースの二乗は有理数 (tr R)²/det R の実数への像である。この商の進ノルムがすべての素数で一以下なら、トレースの二乗は整数である。生成部分群の全要素にこの結論を適用すると、Nielsen の簡約に必要な整数性が得られる。
