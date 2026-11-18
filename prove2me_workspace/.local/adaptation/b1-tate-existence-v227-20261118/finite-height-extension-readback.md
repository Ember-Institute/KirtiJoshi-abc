# English

Let $K/k$ be an extension of number fields and $y\in k$. At a finite place $w$ of $K$ above $v$ of $k$, the absolute value of the image of $y$ equals $|y|_v^{e(w/v)f(w/v)}$, where $e$ is the relative ramification index and $f$ is the relative residue degree. The positive logarithm therefore scales by this local degree. For each $v$, the sum of the local degrees over the places above it is $[K:k]$. Grouping the nonzero summands by the place below gives $h_{\mathrm{fin},K}(y)=[K:k]h_{\mathrm{fin},k}(y)$. Dividing by the absolute field degree yields the same normalized value in either field.

The formal proof follows `Iut/Tripod/Height.lean:150–237` and `Iut/Concrete/ThetaLocalConstruct/Ordp.lean:155–275`. Mochizuki's *Arithmetic Elliptic Curves in General Position*, Definition 3.3, supplies the context of the arithmetic degree compared with finite height in the next theorem.

# 简体中文

设 $K/k$ 是数域扩张，$y\in k$。对 $K$ 中位于 $k$ 的有限处 $v$ 上方的有限处 $w$，$y$ 的像在 $w$ 处的绝对值等于 $|y|_v^{e(w/v)f(w/v)}$，其中 $e$ 是相对分歧指数，$f$ 是相对剩余次数。因此，正部对数按相对局部次数缩放。固定 $v$ 后，所有上方有限处的相对局部次数之和是 $[K:k]$。将非零项按下方有限处分组，得到 $h_{\mathrm{fin},K}(y)=[K:k]h_{\mathrm{fin},k}(y)$。各自除以绝对数域次数后，规范化的有限高度相同。

形式证明来自 `Iut/Tripod/Height.lean:150–237` 和 `Iut/Concrete/ThetaLocalConstruct/Ordp.lean:155–275`。望月新一《处于一般位置的算术椭圆曲线》定义 3.3 提供下一定理所比较的算术次数背景。

# 日本語

$K/k$ を数体の拡大とし、$y\in k$ とする。$k$ の有限素点 $v$ の上にある $K$ の有限素点 $w$ では、$y$ の像の絶対値は $|y|_v^{e(w/v)f(w/v)}$ に等しい。ここで $e$ は相対分岐指数、$f$ は相対剰余次数である。したがって対数の正部分には相対局所次数が掛かる。固定した $v$ の上にある有限素点について相対局所次数を足すと、拡大次数 $[K:k]$ になる。零でない項を下の素点ごとにまとめると、$h_{\mathrm{fin},K}(y)=[K:k]h_{\mathrm{fin},k}(y)$ を得る。それぞれを絶対拡大次数で割ると、正規化した値は一致する。

形式証明は `Iut/Tripod/Height.lean:150–237` と `Iut/Concrete/ThetaLocalConstruct/Ordp.lean:155–275` に従う。次の定理で比較する算術次数については、望月新一の *Arithmetic Elliptic Curves in General Position* 定義 3.3 を参照。
