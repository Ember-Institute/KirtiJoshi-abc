# English

For a curve selected by the provider, let $w$ be a finite place, $p_w$ its residue characteristic, and $f_w$ its residue degree. At a place of multiplicative reduction, let $n_w$ be the normalized order of the chosen Tate parameter $q_w$. The norm of the Tate curve's $j$-invariant is the inverse of the norm of $q_w$. Its $j$-invariant agrees with that of the selected curve in the completion, so the local contribution to the finite height of $j$ is $n_w f_w \log p_w$.

The provider supplies stable reduction. At a finite place outside the multiplicative locus, a good model has discriminant of norm one and $c_4$ of norm at most one. Since $j=c_4^3/\Delta$ is invariant under the change of model, its absolute value there is at most one and its positive logarithm is zero.

Mochizuki's *Arithmetic Elliptic Curves in General Position*, §3, Definition 3.3, gives the arithmetic degree of the $q$ object. The two local formulas above are read back from `refer/iut/Iut/Tripod/Height.lean:558,572`; the paper reference supplies the context for the $q$ contribution.

# 简体中文

设 $w$ 是供应数据所选曲线的一个有限处，$p_w$ 是剩余特征，$f_w$ 是剩余次数。在乘法约化处，记所选 Tate 参数 $q_w$ 的规范化阶为 $n_w$。相应 Tate 曲线的 $j$ 不变量范数是 $q_w$ 的范数的倒数，且该不变量在完备化中与所选曲线的 $j$ 不变量相等。因此这一处对 $j$ 的有限高度贡献为 $n_w f_w\log p_w$。

供应数据保证稳定约化。对非乘法约化的有限处，良好模型的判别式范数等于一，$c_4$ 的范数至多为一。变量变换不改变 $j=c_4^3/\Delta$，所以 $j$ 在该处的绝对值至多为一，正部对数为零。望月新一《处于一般位置的算术椭圆曲线》第 3 节定义 3.3 给出了 $q$ 对象的算术次数；上述两条局部公式以形式代码为准。

# 日本語

供給データが選ぶ曲線の有限素点を $w$ とし、その剰余標数を $p_w$、剰余次数を $f_w$ とする。乗法的還元をもつ素点では、選んだ Tate パラメータ $q_w$ の正規化された位数を $n_w$ とする。対応する Tate 曲線の $j$ 不変量のノルムは $q_w$ のノルムの逆数であり、この不変量は完備化において元の曲線の $j$ 不変量と一致する。したがって、この素点における有限部分の高さへの寄与は $n_w f_w\log p_w$ である。

供給データは安定還元を与える。乗法的還元をもたない有限素点では、良いモデルの判別式のノルムは一、$c_4$ のノルムは一以下である。$j=c_4^3/\Delta$ はモデルの変換で変わらないため、その絶対値は一以下となり、対数の正部分は零である。望月新一の *Arithmetic Elliptic Curves in General Position* 第 3 節定義 3.3 は $q$ 対象の算術次数を与える。ここで述べた二つの局所公式は形式コードに基づく。
