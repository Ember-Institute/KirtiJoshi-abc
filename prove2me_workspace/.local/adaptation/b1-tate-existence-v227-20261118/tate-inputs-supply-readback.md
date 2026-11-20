# English

Let $E$ be an elliptic curve over a number field $F$ and $w$ a finite place of multiplicative reduction. A change of variables gives a model for which $c_4$ has norm one and the discriminant has norm less than one over the completion $F_w$. The discriminant is nonzero, so the norm of $j=c_4^3/\Delta$ is greater than one. The $j$-invariant is unchanged by the change of variables. Since $F_w$ has characteristic zero, $12$ is nonzero there and the Tate parameter existence theorem supplies a parameter whose Tate curve has this $j$-invariant. The local uniformizer existence theorem supplies a uniformizer of $F_w$. The definition records these two choices and their two defining properties at every such place.

Paper context: Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position*, §3, pp. 14–15, describes the local field with surjective valuation and split multiplicative reduction; see the existing verified `GenEll-local-setting` quotation in the uniformizer evidence. The four-field construction and the argument through the $j$-invariant follow the Lean sources listed in the source ledger. The construction proves the matching equality of $j$-invariants and does not supply a curve isomorphism.

# 简体中文

设 $E$ 是数域 $F$ 上的椭圆曲线，$w$ 是一个乘法约化的有限处。变量变换给出一个模型，在完备化 $F_w$ 上，其 $c_4$ 的范数等于一，判别式的范数小于一。判别式非零，所以 $j=c_4^3/\Delta$ 的范数大于一。变量变换不改变 $j$ 不变量。由于 $F_w$ 的特征为零，其中的 $12$ 非零；由 Tate 参数存在性定理，可取一个参数，使相应 Tate 曲线的 $j$ 不变量等于原曲线的 $j$ 不变量在 $F_w$ 中的像。另由局部存在性定理选取 $F_w$ 的素元。定义在每个这样的处记录这两个选择及各自满足的性质。

论文背景：望月新一《处于一般位置的算术椭圆曲线》第 3 节第 14–15 页讨论了带满射离散赋值和分裂乘法约化的局部情形。四字段的构造依据来源台账中的形式代码；所得结论给出 $j$ 不变量相等。

# 日本語

$E$ を数体 $F$ 上の楕円曲線とし、$w$ を乗法的還元をもつ有限素点とする。変数変換により、完備化 $F_w$ において $c_4$ のノルムが一、判別式のノルムが一未満となるモデルが得られる。判別式は零でないため、$j=c_4^3/\Delta$ のノルムは一より大きい。変数変換によって $j$ 不変量は変わらない。$F_w$ は標数零なので $12$ は零でなく、Tate パラメータの存在定理から、もとの曲線と同じ $j$ 不変量をもつ Tate 曲線のパラメータを選べる。また、局所的な存在定理から $F_w$ の素元を選べる。この定義は各有限素点における二つの選択とそれぞれの性質を記録する。

論文上の背景は、望月新一の *Arithmetic Elliptic Curves in General Position* 第 3 節、14–15 頁にある。そこでは全射な離散付値をもつ局所体と分裂乗法的還元の場合が扱われる。四つの成分の構成は出典台帳に示した形式コードに従い、$j$ 不変量の一致を与える。
