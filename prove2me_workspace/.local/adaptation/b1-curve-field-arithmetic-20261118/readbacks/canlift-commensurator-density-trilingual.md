# CanLift 2.7 的格生成群可公度子稠密性

## 中文

取 $t\in\mathbb H$，令 $U$ 为相应的格补集覆盖。记 $A=A(U)$、$B=B(U)$，并令 $\Gamma=\langle A,B\rangle\subseteq\mathrm{SL}_2(\mathbb R)$。Lean 中的 `Subgroup.closure {A, B}` 表示代数生成的子群。若 `Γ.relIndex (commensurator Γ) = 0`，即 $\Gamma$ 在其可公度子中有无限指数，则 `closure_commensurator_dense_of_relIndex_eq_zero` 给出 $\operatorname{Comm}(\Gamma)$ 在实矩阵拓扑下稠密。这是上游 `commensurator_dense`（M1）在这组格生成元上的结论。 [格生成元定理][local-dense] · [上游 M1][upstream-m1]

上游 M1 以任意子群 $\Gamma$ 的 `HasFiniteCovolume Γ` 为前提。上游后续用 Fricke 正规形证明一次穿孔环面群的有限余体积。对离散超群 $\Delta$，上游的指数估计先取 $\Delta\cap(\Gamma\cup(-\Gamma))$，以处理在 $\mathbb H$ 上作用相同的两种符号。本地证明在带符号的甲板群 $\Gamma^{\pm}=U.\mathrm{deckGroup}=\langle\Gamma,-I\rangle$ 上使用同一面积估计。紧部和尖点竖带给出一个与 $\Gamma^{\pm}$ 的每条轨道相交的有限双曲面积可测集 $F$。由于 $-I\in\Gamma^{\pm}$，可直接对 $\Gamma^{\pm}$ 在离散超群中的陪集平移一个正面积小球。$N$ 个不同陪集给出面积 $N\operatorname{vol}(B_0)$，而覆盖估计将它界在 $2\operatorname{vol}(F)$ 以下。 [上游正规形的余体积][upstream-normal-covolume] · [上游离散超群指数][upstream-covolume] · [本地有限余体积][local-covolume] · [本地离散超群指数][local-index]

添加中心元 $-I$ 后，$\Gamma$ 在 $\Gamma^{\pm}$ 中仍有有限指数。两者可公度，因而有同一个可公度子。若这个可公度子离散，本地指数定理先给出 $\Gamma^{\pm}$ 在其中有有限指数，再传回 $\Gamma$。因此无限指数排除单位元在可公度子中孤立，供稠密性判据取趋于 $I$ 的非单位元序列。 [可公度性与指数传递][local-commensurable] · [格生成元的离散情形][local-index-lattice] · [稠密性判据][local-criterion]

本地的边配对给出 $\operatorname{tr}(ABA^{-1}B^{-1})=-2$ 和 $\operatorname{tr}(A)\ne0$。对 $x=\operatorname{tr}A$、$y=\operatorname{tr}B$、$z=\operatorname{tr}(AB)$，Fricke 恒等式给出 $x^2+y^2+z^2=xyz$。若 $|x|\le2$，则 $xyz\le2|y||z|\le y^2+z^2$，这与 $x\ne0$ 矛盾。交换 $x,y$ 同样可得 $y^2>4$，因为 $y=0$ 会迫使 $x=0$。`traces_sq_gt_four` 给出这些界。稠密性判据使用 $x^2>4$、$y\ne0$ 和交换子的迹不等于 $2$。 [边配对的迹][local-lattice-traces] · [Fricke 恒等式][local-fricke] · [本地平方迹的界][local-trace-bounds] · [上游迹估计][upstream-fricke-bound]

本地对角化引理保留上游的显式换基矩阵。若 $A$ 的特征值为 $\lambda,\mu$，换基后的 $B$ 的两个非对角项为 $b,c$，则交换子的迹减去 $2$ 等于 $-bc(\lambda-\mu)^2$。因此 $bc\ne0$。适当平方 $A$ 或 $A^{-1}$ 得到 $D=\operatorname{diag}(\ell,\ell^{-1})$，其中 $\ell>1$。若趋于 $I$ 的序列最终为对角矩阵，则其两个对角项最终不相等。换基后的 $B$ 的迹非零，故它至少有一个非零的对角项。用它共轭可得到具有非零非对角项的子序列。随后用 $D$ 的幂共轭，对非对角项缩放并取极限，得到任意小的非零幺幂参数。闭加法子群的稠密性给出整个单参数幺幂子群。再取共轭得到另一方向，而上下两个幺幂子群生成整个 $\mathrm{SL}_2(\mathbb R)$。换回原基即得稠密性。 [对角化与迹公式][local-diagonal] · [幺幂极限与生成][local-unipotents] · [上游稠密性证明][upstream-density]

有限指数一侧已有从格均匀化传到其他均匀化的指数等价，并由有限指数构造复数域 CanLift 所需的不变多项式。无限指数一侧所得的稠密性对应上游 `M2.margulisDenseOneInfty` 的输入，该定理用它推出算术性。 [均匀化之间的传递][local-uniformization-index] · [有限指数与不变多项式][local-index-polynomial] · [上游 M2][upstream-m2]

## English

Take $t\in\mathbb H$ and the corresponding lattice-complement cover $U$. Put $A=A(U)$, $B=B(U)$, and $\Gamma=\langle A,B\rangle\subseteq\mathrm{SL}_2(\mathbb R)$. In Lean, `Subgroup.closure {A, B}` is the algebraically generated subgroup. An index value of zero means that $\Gamma$ has infinite index in its commensurator. In this case, `closure_commensurator_dense_of_relIndex_eq_zero` gives density of $\operatorname{Comm}(\Gamma)$ in the real matrix topology. This is the conclusion of the pinned `commensurator_dense` theorem (M1) for these lattice generators. [Local lattice theorem][local-dense] · [Pinned M1][upstream-m1]

The pinned M1 theorem takes `HasFiniteCovolume Γ` for a general subgroup $\Gamma$. The pinned proof derives this input for once-punctured torus groups through the Fricke normal form. For a discrete overgroup $\Delta$, its index proof uses $\Delta\cap(\Gamma\cup(-\Gamma))$ to account for the two signs that act identically on $\mathbb H$. The local proof uses the same area bound on the signed deck group $\Gamma^{\pm}=U.\mathrm{deckGroup}=\langle\Gamma,-I\rangle$. The compact part and a vertical cusp strip give a measurable set $F$ of finite hyperbolic area that meets each $\Gamma^{\pm}$-orbit. Since $-I\in\Gamma^{\pm}$, the packing proof can use cosets of $\Gamma^{\pm}$ directly. Translates of a small ball $B_0$ for $N$ distinct cosets have total area $N\operatorname{vol}(B_0)$. The cover bounds this area by $2\operatorname{vol}(F)$. [Pinned normal form and covolume][upstream-normal-covolume] · [Pinned index bound][upstream-covolume] · [Local finite covolume][local-covolume] · [Local index bound][local-index]

Adjoining the central $-I$ gives a finite extension of $\Gamma$. The two subgroups are commensurable and have the same commensurator. If their commensurator is discrete, the area argument first gives finite index for $\Gamma^{\pm}$. The finite extension gives finite index for $\Gamma$ in that same group. Infinite index thus excludes an isolated identity in the commensurator. The density proof uses this fact to take a sequence of nonidentity elements that tends to $I$. [Commensurability and index transfer][local-commensurable] · [Discrete lattice case][local-index-lattice] · [Density criterion][local-criterion]

The local side pairings give $\operatorname{tr}(ABA^{-1}B^{-1})=-2$ and $\operatorname{tr}(A)\ne0$. With $x=\operatorname{tr}A$, $y=\operatorname{tr}B$, and $z=\operatorname{tr}(AB)$, the Fricke identity gives $x^2+y^2+z^2=xyz$. If $|x|\le2$, then $xyz\le2|y||z|\le y^2+z^2$, which contradicts $x\ne0$. If $y=0$, the same identity forces $x=0$. Interchanging $x$ and $y$ gives $y^2>4$. The local theorem `traces_sq_gt_four` gives these bounds. The pinned criterion uses $x^2>4$, $y\ne0$, and commutator trace different from $2$. [Side-pairing traces][local-lattice-traces] · [Fricke identity][local-fricke] · [Local squared trace bounds][local-trace-bounds] · [Pinned trace bound][upstream-fricke-bound]

The diagonalization lemma keeps the explicit change of basis from the pinned proof. Let $\lambda,\mu$ be the eigenvalues of $A$ and $b,c$ the off-diagonal entries of $B$ after this change of basis. The commutator trace minus $2$ equals $-bc(\lambda-\mu)^2$, so $bc\ne0$. Squaring the diagonal form of $A$ or its inverse gives $D=\operatorname{diag}(\ell,\ell^{-1})$ with $\ell>1$. If the sequence is eventually diagonal, its diagonal entries eventually differ. The transformed $B$ has nonzero trace, so at least one of its diagonal entries is nonzero. Conjugation by this matrix gives a subsequence with a nonzero off-diagonal entry. Conjugation by powers of $D$ rescales the entries and gives arbitrarily small nonzero unipotent parameters in the limit. The closed additive subgroup of these parameters is therefore all of $\mathbb R$. Further conjugation gives the other unipotent direction. The two unipotent subgroups generate $\mathrm{SL}_2(\mathbb R)$, so the original subgroup is dense. [Diagonalization and trace formula][local-diagonal] · [Unipotent limits and generators][local-unipotents] · [Pinned density proof][upstream-density]

In the finite-index case, the local proof transfers the index between uniformizations and constructs the invariant polynomial for the complex CanLift theorem. In the infinite-index case, this density conclusion is the input to the pinned `M2.margulisDenseOneInfty` theorem, which derives arithmeticity. [Index across uniformizations][local-uniformization-index] · [Finite index and invariant polynomial][local-index-polynomial] · [Pinned M2][upstream-m2]

## 日本語

$t\in\mathbb H$ を取り、対応する格子の補集合の被覆を $U$ とする。$A=A(U)$、$B=B(U)$、$\Gamma=\langle A,B\rangle\subseteq\mathrm{SL}_2(\mathbb R)$ とおく。Lean の `Subgroup.closure {A, B}` は二つの行列が代数的に生成する部分群を表す。`Γ.relIndex (commensurator Γ) = 0` は、$\Gamma$ がその commensurator の中で無限指数を持つことを表す。このとき `closure_commensurator_dense_of_relIndex_eq_zero` により、$\operatorname{Comm}(\Gamma)$ は実行列の位相で稠密である。これは、固定版の `commensurator_dense`（M1）の結論を格子の生成元に適用したものである。 [格子の生成元に対する定理][local-dense] · [固定版の M1][upstream-m1]

固定版の M1 は、一般の部分群 $\Gamma$ に `HasFiniteCovolume Γ` を仮定する。固定版はこの仮定を、一点を除いたトーラスの群に対して Fricke 標準形から示す。離散上位群 $\Delta$ に対する指数の証明では、$\mathbb H$ 上で同じ作用を持つ二つの符号を扱うため、$\Delta\cap(\Gamma\cup(-\Gamma))$ を用いる。ローカルの証明は、同じ面積評価を符号付き被覆変換群 $\Gamma^{\pm}=U.\mathrm{deckGroup}=\langle\Gamma,-I\rangle$ に適用する。コンパクト部分とカスプの縦帯から、$\Gamma^{\pm}$ のすべての軌道と交わる有限双曲面積の可測集合 $F$ が得られる。$-I\in\Gamma^{\pm}$ なので、$\Gamma^{\pm}$ の剰余類で小球 $B_0$ を移すことができる。異なる $N$ 個の剰余類から得られる面積は $N\operatorname{vol}(B_0)$ であり、被覆による評価はこれを $2\operatorname{vol}(F)$ 以下に抑える。 [固定版の標準形と余体積][upstream-normal-covolume] · [固定版の指数評価][upstream-covolume] · [ローカルの有限余体積][local-covolume] · [ローカルの指数評価][local-index]

中心元 $-I$ を加えると $\Gamma$ の有限拡大が得られる。二つの部分群は通約可能であり、同じ commensurator を持つ。その commensurator が離散ならば、面積評価によりまず $\Gamma^{\pm}$ の指数が有限となる。有限拡大を通じて、同じ commensurator での $\Gamma$ の指数も有限となる。したがって指数が無限ならば単位元は孤立せず、稠密性の証明では $I$ に収束する単位元以外の列を取ることができる。 [通約可能性と指数の移行][local-commensurable] · [格子の場合の離散性と指数][local-index-lattice] · [稠密性の判定][local-criterion]

辺の貼り合わせは $\operatorname{tr}(ABA^{-1}B^{-1})=-2$ と $\operatorname{tr}(A)\ne0$ を与える。$x=\operatorname{tr}A$、$y=\operatorname{tr}B$、$z=\operatorname{tr}(AB)$ とおくと、Fricke の恒等式から $x^2+y^2+z^2=xyz$ が従う。$|x|\le2$ ならば $xyz\le2|y||z|\le y^2+z^2$ となり、$x\ne0$ に矛盾する。$y=0$ とすれば同じ恒等式から $x=0$ が従うため、$x$ と $y$ を入れ替えて $y^2>4$ も得られる。`traces_sq_gt_four` がこれらの下限を与える。固定版の判定に用いる条件は、$x^2>4$、$y\ne0$、および交換子のトレースが $2$ と異なることである。 [辺の貼り合わせのトレース][local-lattice-traces] · [Fricke の恒等式][local-fricke] · [ローカルのトレース平方の下限][local-trace-bounds] · [固定版のトレース評価][upstream-fricke-bound]

対角化には固定版と同じ明示的な基底変換を用いる。$A$ の固有値を $\lambda,\mu$、基底変換後の $B$ の非対角成分を $b,c$ とすると、交換子のトレースから $2$ を引いた値は $-bc(\lambda-\mu)^2$ である。したがって $bc\ne0$ となる。$A$ の対角形またはその逆行列を二乗すると、$\ell>1$ を満たす $D=\operatorname{diag}(\ell,\ell^{-1})$ が得られる。$I$ に収束する列が途中から対角行列だけからなるとき、十分後の項の二つの対角成分は相異なる。基底変換後の $B$ のトレースは非零なので、その対角成分のうち少なくとも一つは非零である。この行列で共役を取ると、非零の非対角成分を持つ部分列が得られる。$D$ のべきによる共役で成分を拡大または縮小し、極限を取ることで、絶対値がいくらでも小さい非零のユニポテント行列のパラメータが得られる。これらのパラメータの閉加法部分群は $\mathbb R$ 全体である。さらに共役を取ると、もう一方の向きのユニポテント部分群も得られる。上下のユニポテント部分群が $\mathrm{SL}_2(\mathbb R)$ を生成するので、元の部分群は稠密である。 [対角化とトレース公式][local-diagonal] · [ユニポテント行列の極限と生成][local-unipotents] · [固定版の稠密性の証明][upstream-density]

指数が有限の場合は、一意化の間で指数を移し、複素数上の CanLift の証明に必要な不変多項式を構成する。指数が無限の場合に得られる稠密性は、固定版で算術性を導く `M2.margulisDenseOneInfty` の入力となる。 [一意化の間での指数の移行][local-uniformization-index] · [有限指数と不変多項式][local-index-polynomial] · [固定版の M2][upstream-m2]

[local-dense]: ../../../../Solutions/Source_ReferenceIutCanLiftDenseCommensurator.lean
[local-covolume]: ../../../../Solutions/Source_ReferenceIutCanLiftLatticeCovolume.lean#L114
[local-index]: ../../../../Solutions/Source_ReferenceIutCanLiftDiscreteOvergroupIndex.lean#L202
[local-commensurable]: ../../../../Solutions/Source_ReferenceIutCanLiftCommensuratorIndex.lean#L34
[local-index-lattice]: ../../../../Solutions/Source_ReferenceIutCanLiftDiscreteOvergroupIndex.lean#L293
[local-criterion]: ../../../../Solutions/Source_ReferenceIutCanLiftDenseCriterion.lean
[local-lattice-traces]: ../../../../Solutions/Source_ReferenceIutCanLiftLatticeCommutatorTrace.lean#L262
[local-fricke]: ../../../../Solutions/Source_ReferenceIutCanLiftFricke.lean#L77
[local-trace-bounds]: ../../../../Solutions/Source_ReferenceIutCanLiftFrickeSquaredTraces.lean
[local-diagonal]: ../../../../Solutions/Source_ReferenceIutCanLiftHyperbolicDiagonalization.lean#L94
[local-unipotents]: ../../../../Solutions/Source_ReferenceIutCanLiftDenseUnipotents.lean
[local-uniformization-index]: ../../../../Solutions/Source_ReferenceIutCanLiftCommensuratorIndex.lean#L56
[local-index-polynomial]: ../../../../Solutions/Source_ReferenceIutCanLiftUniformizationGrowth.lean#L129
[upstream-m1]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fuchsian/Commensurator.lean#L62
[upstream-covolume]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fuchsian/Covolume.lean#L223
[upstream-normal-covolume]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fuchsian/OneInftyLattice.lean#L387
[upstream-fricke-bound]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fuchsian/Commensurator.lean#L74
[upstream-density]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Fuchsian/DenseCriterion.lean#L82
[upstream-m2]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L595
