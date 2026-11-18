# English

Let $e:F\simeq F'$ be an isomorphism of number fields. The induced isomorphism of rings of integers matches their nonzero prime ideals, and hence their finite places. Membership in powers of the matched ideals agrees under this map, so the corresponding valuations agree. The two residue quotient rings have the same cardinality, so the absolute norms of the matched ideals agree as well. Thus the absolute value of $e(y)$ at a transported finite place equals that of $y$ at the original place. Reindexing the sum of positive logarithms gives $h_{\mathrm{fin},F'}(e(y))=h_{\mathrm{fin},F}(y)$.

The formal proof follows `Iut/Tripod/Height.lean:110`. Mochizuki's *Arithmetic Elliptic Curves in General Position*, Definition 3.3, gives the context of the arithmetic degree compared with finite height later in the chain.

# 简体中文

设 $e:F\simeq F'$ 是数域同构。它诱导两个整数环之间的同构，将非零素理想逐一对应，因此也将有限处逐一对应。相应素理想的各次幂具有相同的成员关系，所以相应赋值一致。两个剩余商环的元素个数也相同，故相应素理想的绝对范数相等。因此 $e(y)$ 在对应有限处的绝对值等于 $y$ 在原有限处的绝对值。对正部对数之和重新编号，就得到 $h_{\mathrm{fin},F'}(e(y))=h_{\mathrm{fin},F}(y)$。

形式证明来自 `Iut/Tripod/Height.lean:110`。望月新一《处于一般位置的算术椭圆曲线》定义 3.3 提供后续比较所用算术次数的背景。

# 日本語

$e:F\simeq F'$ を数体の同型とする。誘導される整数環の同型によって非零素イデアルが一対一に対応し、したがって有限素点も一対一に対応する。対応する素イデアルの各冪への所属が保たれるため、付値は一致する。また、剰余環の濃度が等しいので、素イデアルの絶対ノルムも一致する。このため、対応する有限素点での $e(y)$ の絶対値は、元の素点での $y$ の絶対値に等しい。対数の正部分の和を取り直すと、$h_{\mathrm{fin},F'}(e(y))=h_{\mathrm{fin},F}(y)$ を得る。

形式証明は `Iut/Tripod/Height.lean:110` に従う。後続の比較で用いる算術次数については、望月新一の *Arithmetic Elliptic Curves in General Position* 定義 3.3 を参照。
