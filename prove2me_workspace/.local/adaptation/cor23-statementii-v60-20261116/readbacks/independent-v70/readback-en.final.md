# Mathematical readback of statementII_of_cor312

This edition presents the independent English readback by gpt-6.1-sol. It describes the theorem type and the definitions used in its inputs and conclusion. [Frozen English readback](readback-en.md)

The original reader received the theorem stub. The current proof has the identical signature and uses Corollary22Inputs.c2 to derive StatementII from the five inputs below. The archived audit records the standard Lean axioms propext, Classical.choice, and Quot.sound. [Lean theorem](../../../../../Theorems/Thm_AbcAdaptation_Reference_Iut_statementII_of_cor312.lean#L81) · [Archive manifest](../../archive-v81/manifest.json) · [Axiom audit](../../../cor23-canonical-v81-20261116/actual/canonical-audit.json)

Fix the implicit parameters: a height-theory structure $T$; an anabelian-geometry interface $AG$ at universe level $u$; a tempered-geometry interface $TG$ over this same $AG$; and a predicate $P$ on the type $V$ of `Corollary312VariantData` for these fixed interfaces, with universe parameters $u,v$. These are parameters, not structures whose existence the conclusion establishes. The height theory and the local-height index types also have their implicit universe levels. No additional external type-class assumptions occur in the theorem signature; field, number-field, topology, group, and related structures needed inside the data are carried by the respective interfaces and bundles.

Write $Y=T.\mathrm{Pt}(T.\mathrm{tripod})$, $S_K=T.\mathrm{cbsSet}(K)$, $D_d=T.\mathrm{ptLE}(T.\mathrm{tripod},d)$, and $A_{K,d}=S_K∩D_d$. Write $H,Δ,κ:Y→ℝ$ for `htCan`, `logDiff`, and `logCond` evaluated at the tripod. The height-theory structure supplies abstract curve and point types, two predicates named `Hyperbolic` and `DivisorFree`, a distinguished tripod satisfying the first predicate, and subsets `ptLE` and `ptEQ` satisfying $\mathrm{ptLE}(X,0)=∅$ and $\mathrm{ptLE}(X,n+1)=\mathrm{ptLE}(X,n)∪\mathrm{ptEQ}(X,n+1)$. Its type $T.\mathrm{CBS}$ and map `cbsSet` give the objects labelled compactly bounded subsets and their underlying subsets of $Y$. No topology, support map, fixed set of primes, or field-degree interpretation is imposed on this abstract height-theory interface.

The explicit inputs, in order, are the following five objects.

1. A family $I$ assigning an object $I_{K,d}$ of `Corollary22Inputs T K d` to **every** $K∈T.\mathrm{CBS}$ and $d∈ℕ$.
2. A family $ex$ assigning a proof of `ThetaDataExistence P` for **that same** $I_{K,d}$ to every $K,d$.
3. An object $cheb$ of `ChebyshevBound`.
4. An object $pnt$ of `PrimeCountingBound`.
5. A proof $h312$ that **every** $X∈V$ satisfying $P(X)$ satisfies `Corollary312Variant X`.

The last input is a universal conditional claim on the $P$-restricted family. It does not assert the variant inequality for arbitrary $X$ without $P(X)$, nor the existence of any $X$.

For clarity, all the requirements of the first two input types are expanded below. Fix $K,d$ and put $J=I_{K,d}$. The object $J$ contains a function $h:Y→ℝ$ and, for every $x∈Y$ and witness $hx:x∈A_{K,d}$, local data $L_{x,hx}$. Such local data consist of an index type, a finite subset $B_L$ of indices, natural-number-valued functions $p_v,a_v,f_v$, and a natural number $n_L≥1$. For $v∈B_L$, $p_v$ is prime and $a_v,f_v≥1$; for every natural number $q$, the sum of $f_v$ over $v∈B_L$ with $p_v=q$ is at most $n_L$. For any selected subset $B'$ of $B_L$, write

$$
F_L(B')=\frac{\sum_{v∈B'}a_v f_v\log p_v}{n_L},\quad
H_L=F_L(B_L),\quad H_L^{=q}=F_L(\{v∈B_L:p_v=q\}),\quad
H_L^{≠a,b}=F_L(\{v∈B_L:p_v≠a\text{ and }p_v≠b\}).
$$

The local data in $J$ satisfy $H_{L_{x,hx}}=h(x)$ and $n_{L_{x,hx}}≤552960d$. In addition, $h/6$ and $H$ bound each other up to real additive constants on all of $S_K$: there exist real constants $c_1,c_2$ such that every $x∈S_K$ satisfies $h(x)/6≤H(x)+c_1$ and $H(x)≤h(x)/6+c_2$. These constants are uniform on $S_K$. For each real $R$, the set $\{x∈A_{K,d}:h(x)≤R\}$ is finite.

The remaining fields of $J$ are a real number $B≥0$, a real number $t$ with no sign requirement, predicates $Cyc(x,ℓ)$ and $SL(x,ℓ)$ on $Y×ℕ$, and a subset $E⊆Y$. They satisfy the following requirements, where $L=L_{x,hx}$ whenever $x∈A_{K,d}$.

- $H_L^{=2}≤B$ for every such $x,hx$.
- For every such $x,hx$ and every natural prime $ℓ≥7$, if $ℓ$ divides none of the $a_v$ for $v∈B_L$ and $Cyc(x,ℓ)$ holds, then $((ℓ-2)/24)(h(x)-H_L^{=2})≤2\log ℓ+t$. Here $ℓ-2$ is subtraction after casting $ℓ$ to a real number.
- For every such $x,hx$ and natural prime $ℓ≥5$, if $ℓ$ divides none of these $a_v$, $Cyc(x,ℓ)$ fails, and some $v∈B_L$ satisfies $p_v≠2$ and $p_v≠ℓ$, then $SL(x,ℓ)$ holds.
- $E∩A_{K,d}$ is finite. The predicates $Cyc,SL$ and the subset $E$ are specified data; their names impose no further geometric interpretation.

For this exact $J$, the proof supplied by $ex(K,d)$ asserts the following. For every $x∈Y$ and witness $hx:x∈A_{K,d}$, if $x∉E$, then for every natural prime $ℓ≥7$ such that

- $ℓ$ divides none of the $a_v$ for $v∈B_L$;
- $a_v<\sqrt{h(x)}$ for every $v∈B_L$ with $p_v=ℓ$;
- some $v∈B_L$ has $p_v≠2$ and $p_v≠ℓ$;
- $SL(x,ℓ)$ holds,

there exist $X∈V$ and $inv∈\mathrm{Theorem110Invariants}(X)$ satisfying **all** of

$$
P(X),\quad \mathrm{Theorem110Certificate}(inv),\quad
\mathrm{Nonempty}(inv.\mathrm{LocalEstimate}),\quad
ℓ_X=ℓ,\quad d_X≤d,
$$
$$
Q_X=H_L^{≠2,ℓ},\qquad
Δ(x)=D_{inv},\qquad F_{inv}≤κ(x)≤F_{inv}+\log(2ℓ).
$$

Here $ℓ_X=X.\mathrm{data}.ℓ$, $d_X=[ℚ(E.j):ℚ]$ computed inside the number field carried by $X$, $Q_X=X.\mathrm{qPilot}.\mathrm{logQ}$, $D_{inv}=inv.\mathrm{logDtpd}$, and $F_{inv}=inv.\mathrm{logFtpd}$. These witnesses can depend on $K,d,x,hx,ℓ$ and the preceding hypotheses. The requirement is conditional on those hypotheses; it provides no data for a point or prime failing them. It neither constructs geometry for every height theory automatically nor supplies an unrestricted existence theorem for all bundles.

The invariants in these witnesses comprise a natural number $e$ with $1≤e≤d_X$, nonnegative reals $D_{inv},F_{inv}$, a finite set $Z$ of natural primes, and a function $b:ℕ→ℝ$ with $b(p)≥0$ for every $p$ and $b(p)=0$ outside $Z$. Put $e^*=552960e$, $m=\log(e^*ℓ_X)$, $ι_p=1$ if $p≤e^*ℓ_X$ and $0$ otherwise, and let $Q_X(p)$ be the part of $Q_X$ with residue characteristic $p$. The certificate requires $ℓ_X≥7$, that the residue characteristic of every place in the finite bad-place set of the $q$-pilot belong to $Z$, and

$$
\sum_{p∈Z}b(p)≤D_{inv}+F_{inv}+2\log ℓ_X+21,\qquad
\sum_{p∈Z}\log p≤2d_X(D_{inv}+F_{inv})+5+\log ℓ_X.
$$

The type $inv.\mathrm{LocalEstimate}$ supplies, for every position $i$ in the bundle's finite increasing family of label sets and every rational place $r$, a subset $U_{i,r}$ of the corresponding product of components. This subset belongs to the specified family of hull regions and contains the theta-pilot region. At a finite rational prime $p∉Z$ it equals the specified integral region. At $p∈Z$, its packet log-volume is at most

$$
n_i b(p)-\frac{(n_i-1)^2}{2ℓ_X}Q_X(p)+\log p+4n_i mι_p,
$$

where $n_i$ is the cardinality of the label set at position $i$ and the subtraction in this formula is real subtraction. At the infinite rational place its packet log-volume is at most $n_i\log π$. The same object supplies monotonicity of packet log-volume whenever both sets are hull regions in the sense of the component-product presentation and one is contained in the other. `Nonempty` requires the existence of such an object, without selecting one in the proposition.

The bundle type $V$ consists of initial theta data relative to the fixed interfaces, $q$-pilot data, and right-hand-side data, with the hypotheses carried by those structures. In particular its arithmetic data include a number field, an algebraic closure, an elliptic Weierstrass curve, the specified global, prime, Tate, orbicurve and local data; its volume data include component rings and topologies, specified integral regions, a finite family of increasing finite label sets, a container, real log-volume functions, a hull system, and a supplied theta-pilot region. None of these objects is inferred solely from the abstract predicates in $T$; their connection to $x$ is exactly the equalities and bounds required of the witnesses above.

More explicitly, $Q_X$ is the sum, over the finite bad-place set of its $q$-pilot, of $w_v q_v\log p_v$, where the weights $w_v$ are positive on that set and $q_v$ is its supplied normalized order. The variant inequality assumed through $h312$ is precisely

$$
-\frac{Q_X}{2ℓ_X}≤R_X,
$$

where $R_X$ is the average, over the positions in the specified label-set family, of the sum over rational places of the packet log-volume of the hull of the theta-pilot region. The hull is least among the specified hull regions containing that region, for the admissible inputs in question. The family is required to be the standard family of length $(ℓ_X-1)/2$, with natural-number subtraction and division; $ℓ_X$ is a prime at least $5$ in the bundle type. The volume and hull data are inputs satisfying their stated interface laws; the theorem does not generate the theta-pilot region by an unstated procedure. In particular the variant inequality has the direction displayed above, between real numbers.

Finally, $cheb$ supplies a real threshold $ξ≥5$ with $(2/3)z≤θ(z)≤2z$ for every real $z≥ξ$, where $θ$ is the imported Chebyshev theta function. The object $pnt$ supplies a real threshold $η>1$ such that $π(\lfloor z\rfloor_{ℕ})≤3z/(2\log z)$ for every real $z≥η$, where $π$ is the natural-number prime-counting function and the floor is the natural-number floor. These are explicit input certificates, independent of $K,d$; this theorem signature does not discharge them.

With **all five** explicit inputs supplied, the asserted conclusion is $T.\mathrm{StatementII}$. Expanded, for every $d∈ℕ$, every $ε∈ℝ$ with $ε>0$, and then every $K∈T.\mathrm{CBS}$, there exists $C∈ℝ$ such that for every $x∈Y$,

$$
x∈A_{K,d}\quad⇒\quad H(x)≤(1+ε)(Δ(x)+κ(x))+C.
$$

The constant is uniform in $x$, and can depend on $d,ε,K$ and the fixed parameters and supplied inputs. Neither $C>0$ nor $C≥0$ is required. There is no requirement $d>0$; $d=0$ gives an empty restricted domain by the height-theory law. No finiteness of $D_d$ is asserted by its finite natural-number index. The conclusion requires only this upper bound, not a reverse bound or a bound on an absolute difference. The two universal families and the three other inputs together imply this conclusion.
