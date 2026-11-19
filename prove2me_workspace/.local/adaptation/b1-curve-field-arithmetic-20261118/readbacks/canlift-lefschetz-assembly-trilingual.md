# Lefschetz reduction for CanLift 2.7

## English

For an elliptic Weierstrass curve $E$, use `IsCoreOf` for the property that `normalizationPresentation E 1 ⊥ true` is a core of `normalizationPresentation E 1 ⊥ false`. Both presentations use level one and the trivial subgroup. The property requires a common cover of the two presentations and a unique cover to the `true` presentation from every presentation that has a common cover with the `false` presentation. For every elliptic Weierstrass curve over a characteristic-zero field in `Type`, `CanLift27.{0}` asserts this property when the $j$-invariant avoids $0$, $1728$, $488095744/125$, and $1556068/81$, viewed in that field. `CanLift27Complex` asserts the same property over $\mathbb C$. [Definition of a core](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L26) · [CanLift propositions and exceptional values](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L104)

The theorem `canLift27_of_complex_of_descent` derives `CanLift27.{0}` from `hcomplex : CanLift27Complex` and two geometric hypotheses. [Theorem signature](../../../../Solutions/Source_ReferenceIutCanLiftLefschetzAssembly.lean#L69)

1. `hdescend` applies to an embedding $f\colon k\hookrightarrow K$ of characteristic-zero fields and an elliptic Weierstrass curve $E/k$. The core property for the coefficientwise base change $E_K=E.\mathrm{map}(f)$ implies the core property for $E$. [Pi1 descent along an embedding](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L838)
2. `hsubfield` applies to an elliptic Weierstrass curve $E/K$ with $K$ algebraically closed of characteristic zero. For every countable algebraically closed subfield $L\subseteq K$, consider every elliptic Weierstrass curve $W/L$ whose coefficientwise base change to $K$ equals $E$. If the core property holds for every such $W$, it holds for $E$. [Pi1 step over countable subfields](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/LefschetzMain.lean#L114)

The module proves that every countable field $L$ of characteristic zero embeds in $\mathbb C$. It sends a transcendence basis of $L$ over $\mathbb Q$ into one for $\mathbb C$ over $\mathbb Q$, then extends the resulting map using algebraic closedness of $\mathbb C$. It also proves that the four exclusions on $j$ hold for a curve if and only if they hold after mapping its coefficients along a characteristic-zero field embedding. The $j$-invariant and the rational values map along the embedding, and injectivity gives the reverse implication for equality with each rational value. [Complex embedding](../../../../Solutions/Source_ReferenceIutCanLiftLefschetzAssembly.lean#L22) · [Preservation of the exclusions](../../../../Solutions/Source_ReferenceIutCanLiftLefschetzAssembly.lean#L51) · [Pi1 embedding](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/EmbedComplex.lean#L19)

For a curve $E/k$ in `CanLift27.{0}`, take $K$ to be an algebraic closure of $k$ and form $E_K$. For each $W/L$ in `hsubfield` for $E_K$, the exclusions on $j(E_K)$ hold for $W$ and hence for its base change along an embedding $L\hookrightarrow\mathbb C$. Apply `hcomplex` to that complex curve and `hdescend` to recover the property for $W$. Now `hsubfield` gives the property for $E_K$, and `hdescend` along $k\hookrightarrow K$ gives it for $E$. [Lefschetz proof](../../../../Solutions/Source_ReferenceIutCanLiftLefschetzAssembly.lean#L78) · [Pi1 assembly](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/LefschetzMain.lean#L280)

MCP-CI leaf build `ci-021420-ca43813b` passed with exit code 0 and five tactic-suggestion warnings. The receipt records the source SHA-256 beginning with `d487fc0f95ff`. [Leaf receipt](../receipts/round-ci-021420-ca43813b-result.json)

## 中文

对 Weierstrass 椭圆曲线 $E$，核心性质是指 `normalizationPresentation E 1 ⊥ true` 是 `normalizationPresentation E 1 ⊥ false` 的核心，即这两个表示满足 `IsCoreOf`。两种表示都取一级与平凡子群。核心性质要求两种表示具有共同覆盖，且对每个与 `false` 表示有共同覆盖的表示，到 `true` 表示的覆盖存在且唯一。`CanLift27.{0}` 断言此性质对 `Type` 中每个特征零域上的曲线成立，条件是 $j$ 不等于 $0$、$1728$、$488095744/125$ 和 $1556068/81$ 在该域中的像。`CanLift27Complex` 是同一性质在 $\mathbb C$ 上的断言。 [核心定义](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L26) · [CanLift 命题和例外值](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L104)

定理 `canLift27_of_complex_of_descent` 由 `hcomplex : CanLift27Complex` 与两项几何假设推出 `CanLift27.{0}`。 [定理签名](../../../../Solutions/Source_ReferenceIutCanLiftLefschetzAssembly.lean#L69)

1. `hdescend` 适用于特征零域嵌入 $f\colon k\hookrightarrow K$ 和 Weierstrass 椭圆曲线 $E/k$。沿 $f$ 逐项映射系数所得的曲线 $E_K=E.\mathrm{map}(f)$ 若具有核心性质，则 $E$ 也具有该性质。 [Pi1 沿嵌入的下降](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L838)
2. `hsubfield` 适用于特征零代数闭域 $K$ 上的 Weierstrass 椭圆曲线 $E/K$。对每个可数代数闭子域 $L\subseteq K$，考虑每条将系数扩到 $K$ 后等于 $E$ 的 Weierstrass 椭圆曲线 $W/L$。若每条这样的 $W$ 都具有核心性质，则 $E$ 也具有该性质。 [Pi1 的可数子域步骤](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/LefschetzMain.lean#L114)

此模块证明每个特征零可数域 $L$ 都能嵌入 $\mathbb C$。先把 $L$ 在 $\mathbb Q$ 上的一组超越基嵌入 $\mathbb C$ 在 $\mathbb Q$ 上的一组超越基，再利用 $\mathbb C$ 的代数闭性延拓所得映射。模块还证明，沿特征零域嵌入映射曲线系数前后，避开四个 $j$ 例外值的条件等价。域嵌入映射 $j$ 不变量和各有理值，其单射性保证映射后相等可推出原来相等。 [复嵌入](../../../../Solutions/Source_ReferenceIutCanLiftLefschetzAssembly.lean#L22) · [例外值条件的保持](../../../../Solutions/Source_ReferenceIutCanLiftLefschetzAssembly.lean#L51) · [Pi1 嵌入](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/EmbedComplex.lean#L19)

对 `CanLift27.{0}` 中的曲线 $E/k$，取 $k$ 的代数闭包 $K$ 并扩系数得到 $E_K$。对 `hsubfield` 中给出 $E_K$ 的每条 $W/L$，$j(E_K)$ 避开例外值的条件传给 $W$，也传给沿 $L\hookrightarrow\mathbb C$ 扩系数得到的曲线。对该复曲线应用 `hcomplex`，再用 `hdescend` 得到 $W$ 的核心性质。接着用 `hsubfield` 得到 $E_K$ 的核心性质，最后沿 $k\hookrightarrow K$ 用 `hdescend` 得到 $E$ 的核心性质。 [Lefschetz 证明](../../../../Solutions/Source_ReferenceIutCanLiftLefschetzAssembly.lean#L78) · [Pi1 组合定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/LefschetzMain.lean#L280)

MCP-CI 叶构建 `ci-021420-ca43813b` 通过，退出码为 0，有五条 tactic 建议警告。回执所载源文件 SHA-256 以 `d487fc0f95ff` 开头。 [叶构建回执](../receipts/round-ci-021420-ca43813b-result.json)

## 日本語

楕円 Weierstrass 曲線 $E$ に対し、`normalizationPresentation E 1 ⊥ true` が `normalizationPresentation E 1 ⊥ false` の核であることを、`IsCoreOf` で表す。どちらの表示もレベル 1 と自明部分群を用いる。この性質は二つの表示が共通被覆をもち、`false` の表示と共通被覆をもつ任意の表示から `true` の表示への被覆がただ一つ存在することを要求する。`CanLift27.{0}` は、`Type` に属する任意の標数零の体上で、曲線の $j$ 不変量が $0$、$1728$、$488095744/125$、$1556068/81$ のその体における像を避ける場合に、この性質が成り立つと主張する。`CanLift27Complex` は同じ性質を $\mathbb C$ 上で主張する。 [核の定義](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L26) · [CanLift の命題と例外値](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L104)

定理 `canLift27_of_complex_of_descent` は `hcomplex : CanLift27Complex` と二つの幾何学的仮定から `CanLift27.{0}` を導く。 [定理の型](../../../../Solutions/Source_ReferenceIutCanLiftLefschetzAssembly.lean#L69)

1. `hdescend` は標数零の体の埋め込み $f\colon k\hookrightarrow K$ と楕円 Weierstrass 曲線 $E/k$ に適用できる。各係数を $f$ で移して得る $E_K=E.\mathrm{map}(f)$ が核の性質を満たせば、$E$ もその性質を満たす。 [Pi1 の埋め込みに沿った降下](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L838)
2. `hsubfield` は標数零の代数閉体 $K$ 上の楕円 Weierstrass 曲線 $E/K$ に適用できる。各可算な代数閉部分体 $L\subseteq K$ について、係数を $K$ に移すと $E$ になる楕円 Weierstrass 曲線 $W/L$ をすべて考える。このような $W$ がすべて核の性質を満たせば、$E$ もその性質を満たす。 [Pi1 の可算部分体による段階](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/LefschetzMain.lean#L114)

このモジュールは標数零の可算体 $L$ が $\mathbb C$ に埋め込めることを示す。$L$ の $\mathbb Q$ 上の超越基底を $\mathbb C$ の $\mathbb Q$ 上の超越基底に埋め込み、$\mathbb C$ の代数閉性を使って得られた写像を延長する。さらに、標数零の体の埋め込みに沿って曲線の係数を移す前後で、$j$ 不変量が四つの例外値を避ける条件は同値であることを示す。$j$ 不変量と各有理数は埋め込みで移り、埋め込みの単射性によって移した先での等号からもとの等号が従う。 [複素数体への埋め込み](../../../../Solutions/Source_ReferenceIutCanLiftLefschetzAssembly.lean#L22) · [例外値の条件の保存](../../../../Solutions/Source_ReferenceIutCanLiftLefschetzAssembly.lean#L51) · [Pi1 の埋め込み](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/EmbedComplex.lean#L19)

`CanLift27.{0}` の対象である曲線 $E/k$ を取り、$k$ の代数閉包を $K$ として $E_K$ をつくる。`hsubfield` で $E_K$ のもとになる各 $W/L$ について、$j(E_K)$ が例外値を避ける条件は $W$ に移り、さらに $L\hookrightarrow\mathbb C$ に沿って係数を移した曲線にも成り立つ。その複素曲線に `hcomplex` を適用し、`hdescend` で $W$ の核の性質を得る。次に `hsubfield` で $E_K$ の核の性質を得て、最後に $k\hookrightarrow K$ に沿って `hdescend` を適用し、$E$ の核の性質を得る。 [Lefschetz の証明](../../../../Solutions/Source_ReferenceIutCanLiftLefschetzAssembly.lean#L78) · [Pi1 の組み立て定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/LefschetzMain.lean#L280)

MCP-CI のリーフビルド `ci-021420-ca43813b` は終了コード 0 で成功し、タクティクの提案に関する警告が 5 件あった。ビルド結果に記録されたソースの SHA-256 は `d487fc0f95ff` で始まる。 [リーフビルド結果](../receipts/round-ci-021420-ca43813b-result.json)
