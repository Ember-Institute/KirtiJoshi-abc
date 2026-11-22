# Joshi III Form 2 的素数阈值与 P7 数据

## 数值下界

Joshi III 的 Form 2 逐处使用加权体积，并沿用 Form 1 的估计。Form 1 将平方指数的比较交给 Joshi II Theorem 9.2.1。按 III §4.5 选第 \(m=(\ell-1)/2\) 坐标为标准点，归一化指数为 \(j^2/m^2\)。对 \(m>0\)，
\[
m-\sum_{j=1}^m(j/m)^2=\frac{(m-1)(4m+1)}{6m}.
\]
当底数 \(a\) 为标准 Tate 根范数且 \(0<a<1\) 时，\(m\ge2\) 给出 \(a^{\sum_j(j/m)^2}>a^m\)。因此这一步统一适用于奇素数 \(\ell\ge5\)。原 `c2` 的 \(\ell\ge7\) 已满足。 [Form 2](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3617>) · [Form 1 的引用](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3473>) · [Joshi II 的估计](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex#L1151>) · [Lean 的加权比较](../joshi-ii-square-logs/Source_JoshiIINormalizedSquareLogs.lean#L64)

III 先固定 \(X,C,L\)。给定 \(\ell\) 后才有核的固定域 \(L'=L(C[\ell])\) 和 \(L'\) 上的代表处。Form 2 写出的 \(\ell\gg0\) 未指明阈值对曲线的依赖，也未量化紧有界族。上面的数值阈值与这些对象无关。式 (9.9.4) 的底数下标印为 \(1\)，而 \(j^2/m^2\) 对应第 \(m\) 个坐标。该坐标选择和赋值换算已有独立核对。 [初始数据的量化](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L1023>) · [第 \(m\) 个标准坐标](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L1229>) · [坐标与范数核对](../joshi-iii-representative-product/paper-weight-crosscheck.md)

## 同一素数的算术与几何前提

原 c2 从 \([\sqrt h,10\delta\sqrt h\log(2\delta h)]\) 选出同一个素数，其中 \(\delta=552960d\)。P2 要求坏处阶数与 \(\ell\) 互素，P3 控制剩余特征为 \(\ell\) 的阶数，P5 给出一处远离 \(2\ell\) 的乘法约化位，P6 给出包含 \(\mathrm{SL}_2\) 的像。P7 用 \(X.\ell=\ell\) 将这一个素数与初始数据绑定。 [原 c2 选择](../../../../../refer/iut/Iut/Implication/Corollary22.lean#L440) · [原 c2 调用 P7](../../../../../refer/iut/Iut/Implication/Corollary22.lean#L528)

P7 的 \(F,E,K_t\) 对应 III 的 \(L,C,L'\)。\(F\) 含 \(\sqrt{-1}\)，所以没有实嵌入。`six_torsion_rational`、`galois_deg_prime` 和 `sl_le_range` 分别给出全 \(6\)-挠点、模域上次数与 \(\ell\) 互素的 Galois 扩张和大像。`torsionField` 定义为实际挠点表示之核的固定域。`ValuationSection` 沿模域有限处和无限处选择上方代表元。`qroot_pow` 在所选坏处给出 \(2\ell\) 次根关系。 [全局条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField.lean#L220) · [素数条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_AdmissiblePrime.lean#L189) · [固定域](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_AdmissiblePrime.lean#L234) · [截面](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_LocalConditions.lean#L209) · [Tate 根](../../../../Solutions/Source_ReferenceIutThetaLocalData.lean#L114)

III 的 holomorphoid 命题将几何上的 \(C-\{O\}\) 识别为 Strict Belyi Type。P7 的 `AnabelianGeometry.oncePunctured` 是相应接口。把论文的 adelic Ansatz 应用于实际 P7 仍需将论文的穿孔曲线、完备化和代表处识别到这个接口。Form 2 使用每个 untilt 上的 \(H^1_e\) 比较和由比较值生成的张量格。其对接还需要该格在对应 theta locus 包络中的包含，以及同一个包络的 `LocalEstimate`。现有普通对数的范数恒等式解决了标准点的数值计算。 [Strict Belyi](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L955>) · [P7 穿孔曲线接口](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Orbicurve.lean#L130) · [Form 2 的包络包含](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3624>) · [Bloch–Kato 比较核对](../joshi-iii-representative-product/bloch-kato-comparison.md)

## 坏处与 Tate 除子的指标

III §3 从模域的奇剩余特征 split multiplicative 处及所选上方代表处构造 \(\underline{\mathbb V}^{odd,ss}\)。IV 的 `\initassumptions` 直接引用 III 的初始数据，IV §4 的 Tate 除子按模域上奇剩余特征的坏半稳定处拉回，并明确区分基变换后新出现的乘法处。P7 的 `VBadOf ℓ` 取在 \(F\) 上方乘法约化的模域处并删去 \(2,\ell\) 上的处。其 `qPilot.logQ` 等于 `heightOther 2 ℓ`。因此逐处比较需要识别各 P7 代表处在论文约化与截面约定下的 Tate 根和局部因子，之后才能在 P7 指标上取积。 [III 的坏处定义](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L1006>) · [III 的代表处](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L1030>) · [IV 的引用](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 4.tex#L412>) · [IV 的 Tate 除子支持](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 4.tex#L1506>) · [P7 集合](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean#L55) · [P7 高度等式](../../../../Solutions/Source_ReferenceIutQPilot.lean#L58)

IV 的 `pr:basic-ramification-data` 第 (2) 项另断言 \(C/L\) 在 \(2\ell\) 上为好或加性约化。它前列的好约化条件作用在 \(2\ell\) 之外。IV 的素数引理同样只给出 \(\ell\) 上的阶数界，存在定理的证明只要求有一处乘法约化远离 \(2\ell\)。原 c2 对 \(\ell\) 上的高度贡献用 \(\sqrt h\log\ell\) 估计。因而用 IV 的约化断言消去这些处需要另给出该断言在具体 P7 数据上的证明。Form 2 的逐处证明也允许直接在 P7 所需代表处验证比较和包络，按这些处组装右端。 [IV 的约化假设](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 4.tex#L1411>) · [IV 的约化命题](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 4.tex#L1430>) · [IV 的素数引理](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 4.tex#L1977>) · [原 c2 的高度估计](../../../../../refer/iut/Iut/Implication/Corollary22.lean#L482) · [Form 2 的逐处估计](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3630>)

仅从 `LocalHeightData` 的约束无法加强窗口以避开全部坏剩余特征。取度数为 \(1\)，对每个 \(p\le R\) 设一个坏处及 \(h_v=f_v=1\)，则 \(h=\theta(R)\)。固定 \(\delta\) 时，Chebyshev 上下界给出 \(h\to\infty\) 且 \(10\delta\sqrt h\log(2\delta h)<R\) 对充分大的 \(R\) 成立。原窗口中的素数都在该坏集合中，仍满足 P2、P3，且有远离 \(2\ell\) 的坏处。该例验证的是抽象素数选择能保证的范围。 [局部数据约束](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection.lean#L81) · [原选择的排除集](../../../../Theorems/Thm_AbcAdaptation_Reference_Iut_LocalHeightData_exists_prime_selection.lean#L150)

## 逐点到逐族的 Lean 对接

Lean 将原供应按点写成 `PaperRHSSupplyAtPoint`。每个可用点 \(x\) 若有供应下界 \(N_x\) 和上界 \(N_x\le N(K,d)\)，`PaperRHSSupplyAtLeast.of_pointwise` 由 \(N_x\le N(K,d)\le X.\ell\) 得到供应，传入同一个 \(\ell\)、P2、P3、P5、P6 的参数、具体 P7 数据及 \(X.\ell=\ell\)。原 `h312` 仍接收 `Paper X` 与族级素数下界。族级消费者借 Northcott 排除 \(h\le N(K,d)^2\) 的点，再由 c2 的窗口得 \(N(K,d)\le\sqrt h\le\ell\)。 [Lean 草稿](Source_TripodCanonicalCorollary22PaperRHS.lean#L15) · [窗口使用下界](Corollary22Inputs_c2.lean#L236) · [族级消费者](Source_TripodCanonicalCorollary22PrimeBound.lean#L47)

仅给出逐点存在的 \(N_x\) 时，族级消费者缺少统一的上界。如果能在高高度域证出 \(N_x\le\sqrt{h(x)}\)，原窗口也会给出 \(N_x\le\ell\)，这一路径需要固定点的 c2 消费接口。若供应和比较均能以 \(\ell\ge7\) 直接证明，现有下界已经给出所需的族级条件。论文供应和比较由对应构造给出。 [逐点调用的位置](Corollary22Inputs_c2.lean#L242)
