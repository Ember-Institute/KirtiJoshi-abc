# P7 选定处的主单位 Kummer 类

对每个坏模域处 `w`，取 `s := D.localData.sect.sectFin w`。其有限完成域是 `LocalCompletion.completionAt D.Kt s`。设 `p` 为 `s` 的剩余特征，`r := TL.qroot s`。Joshi III 以 `1 + p* · r` 的相容 `pⁿ` 次根塔构造上同调类。Lean 用这个主单位和该有限完成域的代数闭包调用 `LocalKummer.Rational.kummerHom`，取值为连续 Galois 上同调 `H¹(G, ℚₚ(1))`。 [论文的主单位与根塔](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3191>) · [Kummer 映射](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalKummerImageLogarithm.lean#L39)

`ambientLog_unit` 将环境对数限制到主单位生成的饱和子空间。已有主单位校准在该类上给出 `padicLog (1 + p* · r)`，小球上的 `smallLogUnit_log` 给出同一普通对数的校准。将对数值乘以 `p*⁻¹` 即得 `paperNormalizedQRootLog`。 [环境对数](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalCompletionAmbientKummerLog.lean#L32) · [主单位校准](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalKummerLogShell.lean#L57) · [小球校准](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalKummerSmallLogLift.lean#L29) · [归一化目标](../../../../Solutions/Source_ReferenceIutCor312RepresentativeComparisonLog.lean#L21)

`log_normalized_sectionKummerLogProduct_eq_sum_finite_packetVol` 将这些归一化对数按 `sectFin` 代入原乘积定理。这里沿用选定处的标准 `ℂₚ` 范数、平方指数和模域处权重。 [有限处乘积消费者](../../../../Solutions/Source_ReferenceIutCor312RepresentativeComparisonLog.lean#L73)

论文的 `H¹ₑ` 成员资格及实际 Bloch–Kato 逆指数映射对该类的数值等式仍是独立开放义务。 [成员资格](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3199>) · [Bloch–Kato 对数等式](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3221>)
