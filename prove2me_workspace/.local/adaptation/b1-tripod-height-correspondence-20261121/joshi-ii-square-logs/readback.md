# Formal statement readback

## English

In the numerical statements, \(m\) is a natural number. Lean uses indices \(j=0,\ldots,m-1\). The formulas below use the labels \(k=j+1\) and real division.

- **\(\texttt{sum\_normalized\_squares}\).** For each \(m>0\), the following equality holds.
  \[
  \sum_{k=1}^m (k/m)^2=\frac{(m+1)(2m+1)}{6m}.
  \]
- **\(\texttt{sum\_normalized\_square\_root\_logs}\).** For each \(m>0\) and each real number \(a\), put \(L=a/(2(2m+1))\). Then
  \[
  \sum_{k=1}^m (k/m)^2 L=\frac{1}{12}(1+1/m)a.
  \]
- **\(\texttt{root\_log\_bound\_lt\_sum\_normalized\_square\_root\_logs}\).** For each \(m\ge2\) and each real number \(a<0\), put \(L=a/(2(2m+1))\). Then
  \[
  mL<\sum_{k=1}^m (k/m)^2 L.
  \]
- **\(\texttt{weighted\_root\_log\_sum\_lt\_normalized\_average}\).** Let \(S\) be a finite set of elements of any type \(\iota\). Let \(w,L:\iota\to\mathbb R\) be any functions. If \(m\ge2\) and \(Q=\sum_{v\in S}w(v)L(v)<0\), then
  \[
  Q<\frac1m\sum_{k=1}^m\sum_{v\in S}w(v)(k/m)^2 L(v).
  \]

For the concrete construction, take any anabelian geometry \(AG\) and a tempered geometry \(TG\) over \(AG\). Fix initial theta data \(D\), a local theory \(LT\) over its torsion field \(K_t\), and local theta data \(TL\) over \(D,LT\). Take q-pilot inputs \(QI\) for \(D\). Write \(F\) for the base field, \(M=\mathbb Q(j(E))\) for the moduli field, and \(\ell\) for the prime in \(D\). Set \(m=\lfloor(\ell-1)/2\rfloor\). Write \(S\) for the bad moduli places from \(QI\) and \(s(v)\) for the representative in \(K_t\) from \(D\). Put \(d_v=[(K_t)_{s(v)}:M_v]\), \(n=[M:\mathbb Q]\), and \(L_v=\log\|\mathrm{TL.qroot}(s(v))\|\). Use the \(M\)-algebra structure on \(K_t\) stored in \(D\). Write \(X\) for the concrete variant data from \(D,LT,TL,QI\).

- **\(\texttt{normalizedWitnessLogAverage}\).** The function returns
  \[
  A=\frac1m\sum_{k=1}^m\sum_{v\in S}\frac{(k/m)^2 L_v}{d_v n}.
  \]
- **\(\texttt{qPilot\_lhs\_lt\_normalizedWitnessLogAverage}\).** Suppose the stored algebra map \(M\to K_t\) equals the composite of the inclusions \(M\to F\to K_t\). Then the signed q-pilot logarithm of \(X\) is strictly less than \(A\).
- **\(\texttt{corollary312Variant\_of\_normalizedWitnessLogAverage\_le\_rhs}\).** Assume the same algebra-map equality. If \(A\le X.\mathrm{rhsData.rhs}\), then \(X.\mathrm{qPilot.lhs}\le X.\mathrm{rhsData.rhs}\). The right side is the procession-normalized log volume of the hull in \(X\).

## 简体中文

数值陈述中的 \(m\) 是自然数。Lean 的下标为 \(j=0,\ldots,m-1\)。下列公式使用标签 \(k=j+1\) 和实数除法。

- **\(\texttt{sum\_normalized\_squares}\)**。对每个 \(m>0\)，有
  \[
  \sum_{k=1}^m (k/m)^2=\frac{(m+1)(2m+1)}{6m}.
  \]
- **\(\texttt{sum\_normalized\_square\_root\_logs}\)**。给定任意 \(m>0\) 和实数 \(a\)，令 \(L=a/(2(2m+1))\)。则
  \[
  \sum_{k=1}^m (k/m)^2 L=\frac{1}{12}(1+1/m)a.
  \]
- **\(\texttt{root\_log\_bound\_lt\_sum\_normalized\_square\_root\_logs}\)**。给定任意 \(m\ge2\) 和实数 \(a<0\)，令 \(L=a/(2(2m+1))\)。则
  \[
  mL<\sum_{k=1}^m (k/m)^2 L.
  \]
- **\(\texttt{weighted\_root\_log\_sum\_lt\_normalized\_average}\)**。给定任意类型 \(\iota\) 的有限集 \(S\) 以及任意函数 \(w,L:\iota\to\mathbb R\)。若 \(m\ge2\) 且 \(Q=\sum_{v\in S}w(v)L(v)<0\)，则
  \[
  Q<\frac1m\sum_{k=1}^m\sum_{v\in S}w(v)(k/m)^2 L(v).
  \]

对具体构造，给定任意远阿贝尔几何 \(AG\) 和其上的缓和几何 \(TG\)。固定初始 \(\theta\) 数据 \(D\)、其扭点域 \(K_t\) 上的局部理论 \(LT\) 和对应 \(D,LT\) 的局部 \(\theta\) 数据 \(TL\)。给定 \(D\) 的 \(q\) 导引输入 \(QI\)。以 \(F\) 表示基域、\(M=\mathbb Q(j(E))\) 表示模域，并以 \(\ell\) 表示 \(D\) 中的素数。令 \(m=\lfloor(\ell-1)/2\rfloor\)。以 \(S\) 表示 \(QI\) 给出的坏模域处，以 \(s(v)\) 表示 \(D\) 给出的 \(K_t\) 中代表处。令 \(d_v=[(K_t)_{s(v)}:M_v]\)、\(n=[M:\mathbb Q]\) 和 \(L_v=\log\|\mathrm{TL.qroot}(s(v))\|\)。使用 \(D\) 保存的 \(K_t\) 上的 \(M\)-代数结构。以 \(X\) 表示由 \(D,LT,TL,QI\) 构成的具体变体数据。

- **\(\texttt{normalizedWitnessLogAverage}\)**。该函数的值为
  \[
  A=\frac1m\sum_{k=1}^m\sum_{v\in S}\frac{(k/m)^2 L_v}{d_v n}.
  \]
- **\(\texttt{qPilot\_lhs\_lt\_normalizedWitnessLogAverage}\)**。若保存的代数映射 \(M\to K_t\) 等于包含映射 \(M\to F\to K_t\) 的复合，则 \(X\) 的带符号 \(q\) 导引对数严格小于 \(A\)。
- **\(\texttt{corollary312Variant\_of\_normalizedWitnessLogAverage\_le\_rhs}\)**。假定同一代数映射等式。若 \(A\le X.\mathrm{rhsData.rhs}\)，则 \(X.\mathrm{qPilot.lhs}\le X.\mathrm{rhsData.rhs}\)。右端是 \(X\) 中包络按行列归一化的对数体积。

## 日本語

数値に関する各命題で、\(m\) は自然数とする。Lean の添字は \(j=0,\ldots,m-1\) である。以下の式ではラベル \(k=j+1\) と実数の除算を用いる。

- **\(\texttt{sum\_normalized\_squares}\)**。任意の \(m>0\) に対して、次の等式が成り立つ。
  \[
  \sum_{k=1}^m (k/m)^2=\frac{(m+1)(2m+1)}{6m}.
  \]
- **\(\texttt{sum\_normalized\_square\_root\_logs}\)**。任意の \(m>0\) と実数 \(a\) に対し、\(L=a/(2(2m+1))\) とおく。このとき、
  \[
  \sum_{k=1}^m (k/m)^2 L=\frac{1}{12}(1+1/m)a.
  \]
- **\(\texttt{root\_log\_bound\_lt\_sum\_normalized\_square\_root\_logs}\)**。任意の \(m\ge2\) と実数 \(a<0\) に対し、\(L=a/(2(2m+1))\) とおく。このとき、
  \[
  mL<\sum_{k=1}^m (k/m)^2 L.
  \]
- **\(\texttt{weighted\_root\_log\_sum\_lt\_normalized\_average}\)**。任意の型 \(\iota\) の有限集合 \(S\) と任意の関数 \(w,L:\iota\to\mathbb R\) をとる。\(m\ge2\) かつ \(Q=\sum_{v\in S}w(v)L(v)<0\) ならば、
  \[
  Q<\frac1m\sum_{k=1}^m\sum_{v\in S}w(v)(k/m)^2 L(v).
  \]

具体的な構成では、任意の遠アーベル幾何 \(AG\) とその上の緩和幾何 \(TG\) をとる。初期 \(\theta\) データ \(D\)、その捩れ点体 \(K_t\) 上の局所理論 \(LT\)、および \(D,LT\) に対する局所 \(\theta\) データ \(TL\) を固定する。\(D\) に対する \(q\)-パイロットの入力 \(QI\) をとる。基礎体を \(F\)、モジュライ体を \(M=\mathbb Q(j(E))\)、\(D\) の素数を \(\ell\) と書く。\(m=\lfloor(\ell-1)/2\rfloor\) とおく。\(QI\) が与えるモジュライ体の悪い場所の集合を \(S\)、\(D\) が選ぶ \(K_t\) の代表場所を \(s(v)\) と書く。\(d_v=[(K_t)_{s(v)}:M_v]\)、\(n=[M:\mathbb Q]\)、\(L_v=\log\|\mathrm{TL.qroot}(s(v))\|\) とおく。\(D\) に記録された \(K_t\) の \(M\)-代数構造を用いる。\(D,LT,TL,QI\) から構成される具体的な変種のデータを \(X\) と書く。

- **\(\texttt{normalizedWitnessLogAverage}\)**。この関数の値は
  \[
  A=\frac1m\sum_{k=1}^m\sum_{v\in S}\frac{(k/m)^2 L_v}{d_v n}
  \]
  である。
- **\(\texttt{qPilot\_lhs\_lt\_normalizedWitnessLogAverage}\)**。記録された代数写像 \(M\to K_t\) が包含写像 \(M\to F\to K_t\) の合成に等しいと仮定する。このとき \(X\) の符号付き \(q\)-パイロット対数は \(A\) より真に小さい。
- **\(\texttt{corollary312Variant\_of\_normalizedWitnessLogAverage\_le\_rhs}\)**。同じ代数写像の等式を仮定する。\(A\le X.\mathrm{rhsData.rhs}\) ならば \(X.\mathrm{qPilot.lhs}\le X.\mathrm{rhsData.rhs}\) が成り立つ。右辺は \(X\) の包の行列正規化対数体積である。
