# The quadratic Weierstrass model and its normalization rings

Upstream Pi1 revision `ca7def953193f861a462aa0831eec8f0a31ff69f`. Adapted source SHA-256 `eafce0edb4ab89f884764c7ca43428f6651a6d1e5d4ef0256e1d9e864e0bcb8a`. The MCP-CI leaf check and the build with Lean object output both exited with code 0 and reported four warnings each. [Adapted source](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L2) · [Leaf check ci-022869-50e2e5b4](../receipts/round-ci-022869-50e2e5b4-result.json) · [Leaf build ci-022876-b4db7b99](../receipts/round-ci-022876-b4db7b99-result.json)

## English

Let $E$ be a Weierstrass curve over $k$, with coefficients $a_1,a_2,a_3,a_4,a_6$, and let $t\in\Omega$ for a field extension $\Omega/k$. Write the coefficients in $\Omega$ via the given embedding. Evaluating the Weierstrass equation at $X=t$ gives $y^2+B_E(t)y=C_E(t)$ with

$$
B_E(t)=a_1t+a_3,\qquad C_E(t)=t^3+a_2t^2+a_4t+a_6.
$$

Both expressions lie in $k(t)$. In a tower $k\subseteq K\subseteq\Omega$, the expressions for $E$ and for its base change to $K$ have the same values in $\Omega$. This follows from the compatibility of the coefficient maps. [Coefficient formulas](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L29) · [Membership in the rational base](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L36) · [Constant extension](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L54)

Assume $E$ is elliptic. If $t$ is transcendental over $k$ and $y$ solves the equation above, then $(t,y)$ is a nonsingular affine point. Evaluation at that point gives a function-field embedding $j:k(E)\hookrightarrow\Omega$ sending $x_E$ to $t$ and $y_E$ to $y$. In characteristic zero, any such $k$-algebra embedding has transcendental $t=j(x_E)$, and $y=j(y_E)$ satisfies the equation. The image field is $N=k(t)(y)$. Each element of the affine coordinate ring has the form $p(x_E)+q(x_E)y_E$ for $p,q\in k[X]$. Evaluating these expressions and their fractions gives elements of $N$. The image also contains $t$ and $y$, so it contains all of $N$. [Existence of the embedding](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L71) · [Transcendence and equation](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L92) · [Image field](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L134) · [Pi1 field isomorphism](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/EllipticSubfield.lean#L172)

For the normalization rings, keep the characteristic-zero assumptions and the embedding $j$. The unsigned level-one ring `coverCoordinateRing E 1 ⊥ false` identifies with the integral closure of $k[t]$ in $N$. The map `unsignedQuadraticModelEquiv` transports the integral closure over $k[X]$ using the field isomorphism induced by $j$ and the compatible evaluation $k[X]\simeq k[t]$. The signed ring `coverCoordinateRing E 1 ⊥ true` identifies with the bottom normalization ring $k[t]$ via `signedQuadraticModelEquiv`. [Unsigned isomorphism](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L183) · [Signed isomorphism](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L190) · [Pi1 normalization isomorphism](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/EllipticSubfield.lean#L184)

The theorem `quadraticModelEquiv_square` identifies the original signed-to-unsigned map with the inclusion from $k[t]$ into its integral closure in $N$. To prove the equality, represent a signed-ring element by $p\in k[X]$. The route through the unsigned ring and the route through the bottom normalization both give $p(t)$ in $\Omega$. The embedding of the normalization into $\Omega$ is injective, so the two ring maps agree. [Original polynomial square](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/GenuineSignedBaseNormalizationRing.lean#L114) · [Adapted square](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L226) · [Pi1 polynomial compatibility](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/EllipticSubfield.lean#L370)

MCP-CI review `ci-022884-1f96e82a` printed only `propext`, `Classical.choice`, and `Quot.sound` for `exists_functionField_embedding_of_quadratic`, `unsignedQuadraticModelEquiv`, `signedQuadraticModelEquiv`, and `quadraticModelEquiv_square`. [Review source](../ReviewCanLiftRealizationAndQuadraticModel.lean#L12) · [Review receipt](../receipts/round-ci-022884-1f96e82a-result.json)

## 中文

设 $E$ 为 $k$ 上的 Weierstrass 曲线，系数为 $a_1,a_2,a_3,a_4,a_6$。取域扩张 $\Omega/k$ 和 $t\in\Omega$，通过给定嵌入将系数视为 $\Omega$ 中的元素。在 $X=t$ 处求值，Weierstrass 方程成为 $y^2+B_E(t)y=C_E(t)$，其中

$$
B_E(t)=a_1t+a_3,\qquad C_E(t)=t^3+a_2t^2+a_4t+a_6.
$$

两个表达式均属于 $k(t)$。在域塔 $k\subseteq K\subseteq\Omega$ 中，$E$ 和它在 $K$ 上的基变换给出的这两个表达式在 $\Omega$ 中取值相同。这由系数映射相容得到。 [系数公式](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L29) · [有理底域中的归属](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L36) · [常数扩张](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L54)

假设 $E$ 是椭圆曲线。若 $t$ 在 $k$ 上超越且 $y$ 满足上述方程，则 $(t,y)$ 是非奇异仿射点。在该点求值得到函数域嵌入 $j:k(E)\hookrightarrow\Omega$，将 $x_E$ 送到 $t$、$y_E$ 送到 $y$。在特征零下，任意这样的 $k$-代数嵌入都使 $t=j(x_E)$ 在 $k$ 上超越，且 $y=j(y_E)$ 满足方程。像域为 $N=k(t)(y)$。仿射坐标环的每个元素都可写成 $p(x_E)+q(x_E)y_E$，其中 $p,q\in k[X]$。对这些表达式及其分式求值得到 $N$ 中的元素。像域也包含 $t$ 与 $y$，所以包含整个 $N$。 [嵌入的存在性](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L71) · [超越性与方程](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L92) · [像域](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L134) · [Pi1 的域同构](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/EllipticSubfield.lean#L172)

对于归一化环，保留特征零条件及嵌入 $j$。一级无符号环 `coverCoordinateRing E 1 ⊥ false` 与 $k[t]$ 在 $N$ 中的整闭包同构。`unsignedQuadraticModelEquiv` 利用 $j$ 诱导的函数域同构及相容的求值同构 $k[X]\simeq k[t]$，传递 $k[X]$ 上的整闭包。有符号环 `coverCoordinateRing E 1 ⊥ true` 通过 `signedQuadraticModelEquiv` 与底域的归一化环 $k[t]$ 同构。 [无符号同构](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L183) · [有符号同构](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L190) · [Pi1 的归一化环同构](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/EllipticSubfield.lean#L184)

定理 `quadraticModelEquiv_square` 将原先从有符号环到无符号环的映射识别为 $k[t]$ 到其在 $N$ 中的整闭包的包含映射。证明把有符号环的元素表示为 $p\in k[X]$。经过无符号环的路径与经过底域归一化环的路径都给出 $\Omega$ 中的 $p(t)$。归一化环嵌入 $\Omega$ 是单射，因此两个环映射相等。 [原多项式方块](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/GenuineSignedBaseNormalizationRing.lean#L114) · [适配方块](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L226) · [Pi1 的多项式相容性](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/EllipticSubfield.lean#L370)

MCP-CI 审查 `ci-022884-1f96e82a` 对 `exists_functionField_embedding_of_quadratic`、`unsignedQuadraticModelEquiv`、`signedQuadraticModelEquiv` 和 `quadraticModelEquiv_square` 各自仅列出公理 `propext`、`Classical.choice` 和 `Quot.sound`。 [审查源码](../ReviewCanLiftRealizationAndQuadraticModel.lean#L12) · [审查回执](../receipts/round-ci-022884-1f96e82a-result.json)

## 日本語

$E$ を係数 $a_1,a_2,a_3,a_4,a_6$ を持つ $k$ 上の Weierstrass 曲線とする。体の拡大 $\Omega/k$ と $t\in\Omega$ を取り、係数は与えられた埋め込みで $\Omega$ に移す。Weierstrass 方程式を $X=t$ で評価すると $y^2+B_E(t)y=C_E(t)$ となる。ここで

$$
B_E(t)=a_1t+a_3,\qquad C_E(t)=t^3+a_2t^2+a_4t+a_6
$$

である。二つの式はいずれも $k(t)$ に属する。体の塔 $k\subseteq K\subseteq\Omega$ において、$E$ とその $K$ への基底変換で得られる式の値は $\Omega$ で一致する。これは係数の写像の両立性から従う。 [係数の式](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L29) · [有理関数体への所属](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L36) · [定数体の拡大](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L54)

$E$ を楕円曲線とする。$t$ が $k$ 上超越的で $y$ が上の方程式を満たすならば、$(t,y)$ は非特異なアフィン点である。この点での評価から、$x_E$ を $t$ に、$y_E$ を $y$ に移す関数体の埋め込み $j:k(E)\hookrightarrow\Omega$ を得る。標数零では、任意のこのような $k$-代数埋め込みに対し $t=j(x_E)$ は $k$ 上超越的で、$y=j(y_E)$ は方程式を満たす。像の体は $N=k(t)(y)$ である。アフィン座標環の各元は $p,q\in k[X]$ により $p(x_E)+q(x_E)y_E$ と書ける。これらの式とその商を評価すると $N$ の元を得る。像の体は $t$ と $y$ を含むので、$N$ 全体を含む。 [埋め込みの存在](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L71) · [超越性と方程式](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L92) · [像の体](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L134) · [Pi1 の体の同型](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/EllipticSubfield.lean#L172)

正規化環については標数零と埋め込み $j$ を仮定する。レベル $1$ の符号なしの環 `coverCoordinateRing E 1 ⊥ false` は $k[t]$ の $N$ における整閉包と同型である。`unsignedQuadraticModelEquiv` は $j$ が誘導する関数体の同型と、それに両立する評価による同型 $k[X]\simeq k[t]$ を使って $k[X]$ 上の整閉包を移す。符号付きの環 `coverCoordinateRing E 1 ⊥ true` は `signedQuadraticModelEquiv` により基礎体の正規化環 $k[t]$ と同型である。 [符号なしの同型](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L183) · [符号付きの同型](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L190) · [Pi1 の正規化環の同型](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/EllipticSubfield.lean#L184)

定理 `quadraticModelEquiv_square` は、符号付きの環から符号なしの環への写像を、$k[t]$ からその $N$ における整閉包への包含と同一視する。証明では符号付きの環の元を $p\in k[X]$ で表す。符号なしの環を経由しても、基礎体の正規化環を経由しても、$\Omega$ における像は $p(t)$ である。正規化環の $\Omega$ への埋め込みが単射なので、二つの環の写像は一致する。 [元の多項式の図式](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/GenuineSignedBaseNormalizationRing.lean#L114) · [適応版の図式](../../../../Solutions/Source_ReferenceIutCanLiftQuadraticModel.lean#L226) · [Pi1 の多項式の両立性](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/EllipticSubfield.lean#L370)

MCP-CI レビュー `ci-022884-1f96e82a` は、`exists_functionField_embedding_of_quadratic`、`unsignedQuadraticModelEquiv`、`signedQuadraticModelEquiv`、`quadraticModelEquiv_square` の公理としてそれぞれ `propext`、`Classical.choice`、`Quot.sound` だけを出力した。 [レビューのソース](../ReviewCanLiftRealizationAndQuadraticModel.lean#L12) · [レビュー結果](../receipts/round-ci-022884-1f96e82a-result.json)
