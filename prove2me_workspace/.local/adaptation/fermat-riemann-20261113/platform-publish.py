from pathlib import Path
import ast,json,hashlib,importlib.util,urllib.request,urllib.error,uuid,time
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/fermat-riemann-20261113'
s=importlib.util.spec_from_file_location('p2m_api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(s);s.loader.exec_module(api)
ENV='0df444a360eaa60ab8c11dca51a86af692955474';ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5';pre='AbcAdaptation.Tripod.Fermat.Proper.'
def save(name,data):(b/name).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
protocol=(w/'.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
for node in ast.parse(protocol).body:
 if isinstance(node,ast.FunctionDef) and node.name in ['publish','verify']:exec(compile(ast.Module(body=[node],type_ignores=[]),'<previous-platform-protocol>','exec'),globals())
rb=json.loads((b/'readbacks-final.json').read_text());groups=json.loads((b/'readback-source-groups.json').read_text());quote=(b/'mochizuki-quotation.md').read_text()
def prose(names):return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+n+'`\n\n'+rb[n][lang] for n in names) for lang,title in [('en','English'),('zh','简体中文'),('ja','日本語')])
common='Shinichi Mochizuki, Noncritical Belyi Maps (May 2004), proof of Theorem 2.5, printed p.6, https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . This passage supplies the geometric context of actual divisors, residue-field evaluation and simultaneous nonvanishing. The precise independent Lean constructions and proofs are adapted from Belyi 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8, pinned by refer/iut, with Apache 2.0 notices retained. The paper passage does not state all implementation details. No Belyi, Genl or Iut runtime import is used. '
sources={
 'FermatCurveFieldBasic':'Belyi/CurveField/Basic.lean:40–136; the exact one-field curve-function-field class is witnessed by the existing Model.u, transcendental_u and finite_u. No constant-field equality or finite-type-field premise is added.',
 'FermatCurveFieldChart':'Belyi/CurveField/Chart.lean:35–129; actual integral closure of Q[t] in K, Dedekind, finite and finite-type proofs.',
 'FermatCurveFieldPlace':'Belyi/CurveField/Place.lean; localization at actual nonzero prime ideals identifies every proper valuation ring; native places and residue fields retained.',
 'FermatCurveFieldResidue':'Belyi/CurveField/Residue.lean:76; actual residue is a surjective finite-type quotient, hence finite-dimensional over Q. Existing placesDiscrete and residuesFinite are consequences, not extra laws.',
 'FermatCurveFieldZerosPoles':'Belyi/CurveField/ZerosPoles.lean; actual zero/pole existence and finite support over all proper valuative places.',
 'FermatRiemannSpaces':'Belyi/CurveField/RiemannRochSpace.lean:49–82 and Divisor.lean; actual L(A), its finrank and actual finite divisor arithmetic. The separate zero branch preserves ord(0)=0.',
 'FermatRiemannComposition':'Belyi/CurveField/Riemann.lean:288–390; finite union of proper subspaces gives large effective polar realization; positive and negative parts produce an arbitrary polar presentation.',
 'FermatFunctionDivisors':'Belyi/CurveField/Divisor.lean:124–220 and Riemann.lean:163–166; actual principal/zero/pole divisors, actual basis and basis pole correction; principal degree zero is conditional on equal actual fiber degrees.',
 'FermatRiemannLocalDimension':'Belyi/CurveField/RiemannRochSpace.lean:89–337; actual scaled residue linear map, exact kernel, rank-nullity, finite divisor induction and multiplication equivalence. Principal-degree-zero remains an explicit conditional input.',
 'FermatRiemannDimensionComposition':'Belyi/CurveField/Riemann.lean:158–282; actual integer degree-minus-dimension defects are bounded from pole approximation and basis-power bounds, and the attained maximum yields eventual equality.'}
val=json.loads((b/'upload-validation.json').read_text());assert val['passed'] and val['elaborated_types_equal'] and val['existing_target_types_definitionally_equal']
for f,sha in val['definition_hashes'].items():assert hashlib.sha256((w/f).read_bytes()).hexdigest()==sha,f
for tag in ['closed-axioms-review','sketch-axioms-leaf']:
 x=json.loads((b/(tag+'-result.json')).read_text());assert x['status']=='succeeded'
 if tag=='closed-axioms-review':assert x['result']['review']['passed'] and 'sorryAx' not in x['result']['stdout']
for name in sources:
 f='Definitions/Def_'+name+'.lean';names=groups[Path(f).name]
 publish('def-'+name,'/submit-definition',{'definition_name':name,'definition_title':name+' — actual function-field geometry','definition':(w/f).read_text(),'natural_language_statement':quote+prose(names),'source':common+sources[name],'env':ENV,'private':True,'tags':['abc-conjecture','arithmetic-geometry']})
titles={'functionZeroPoleDegrees':'Actual zero and pole fiber degrees','riemannPolarApproximation':'Principal modification bounded by the actual coordinate pole divisor','riemannBasisPowerLowerBound':'Dimension lower bound from the actual function-field basis','riemannRochFiniteDimensional':'Finite dimensionality of every actual Riemann space','riemannRochDimensionUpperBound':'Degree upper bound for the actual Riemann dimension','riemannRochEventuallyLinear':'Eventual linearity of the actual Riemann dimension'}
items=json.loads((b/'upload-problem-items.json').read_text())
for item in items:
 n=item['theorem_name'].removeprefix(pre);group='FermatFunctionDivisors' if n=='functionZeroPoleDegrees' else 'FermatRiemannDimensionComposition' if n in ['riemannPolarApproximation','riemannBasisPowerLowerBound','riemannRochEventuallyLinear'] else 'FermatRiemannLocalDimension'
 item.update(theorem_title=titles[n],natural_language_statement=quote+prose([pre+n]),source=common+sources[group],tags=['abc-conjecture','arithmetic-geometry'])
results=publish('riemann-children','/submit-problem',{'problems':items,'env':ENV,'private':True});ids={x['theorem_name']:x['theorem_id'] for x in results};save('published-child-ids.json',ids)
old=json.loads((w/'.local/adaptation/fermat-proper-canonical-20261113/published-child-ids.json').read_text())
arguments={
 'placesDiscrete':('The model supplies a transcendental coordinate u and a finite extension over Q(u). Every proper valuation place contains a transcendental coordinate or its inverse. The integral closure of the corresponding polynomial chart is Dedekind. Its localization at the prime under the place is exactly the given valuation ring, hence is a discrete valuation ring.','模型提供超越坐标 u 和在有理函数域上的有限扩张。每个真赋值处包含某个超越坐标或其逆。对应多项式图册的整闭包为 Dedekind 整环，其在处下方素理想处的局部化等于给定赋值环，因而是离散赋值环。','模型の超越座標と有限拡大から Dedekind 整域である整閉包のチャートを取る。各付値環はその素イデアルでの局所化と一致するため、離散付値環となる。'),
 'residuesFinite':('Choose an integral-closure chart containing the place. Its residue map is surjective onto the actual residue field. The chart is a finite-type Q-algebra, so its field quotient is finite over Q by Zariski’s lemma.','选择被该处包含的整闭包图册。图册到实际剩余域的剩余映射满射；图册是有理数域上的有限生成代数，因此 Zariski 引理给出该剩余域在有理数域上有限。','整閉包のチャートから実際の剰余体への全射を取る。チャートは有理数体上有限生成なので、Zariski の補題により剰余体は有理数体上有限拡大となる。'),
 'riemannRochFiniteDimensional':('The zero and pole fiber degrees agree, so every principal divisor has degree zero. A nonzero function in L(A) makes A plus its principal divisor effective; thus L(A) vanishes at negative degree. Subtract enough copies of an actual place to reach negative degree, then add them back through the scaled residue map. Its kernel is the preceding Riemann space and its target is a finite residue field. This proves finite dimensionality by induction.','零点与极点纤维次数相等，推出每个主除子次数为零。L(A) 中的非零函数使 A 加上其主除子有效，所以负次数时空间为零。减去同一实际处的足够多个副本达到负次数，再用逐处的缩放剩余映射逐次加回；映射的核是前一个 Riemann 空间，目标是有限维剩余域，因而归纳得到有限维性。','零点と極の次数の一致から主因子の次数は零となる。負次数の Riemann 空間は零であり、一つの実際の素点を十分引いてこの場合に帰着する。縮小した空間を核とする剰余写像で素点を加え戻し、剰余体の有限次元性から帰納する。'),
 'riemannRochDimensionUpperBound':('If L(A) is zero the bound is immediate. Otherwise choose a nonzero z in L(A); then A+div(z) is effective. Multiplication by z identifies its Riemann space with L(A). Adding the effective divisor one place at a time gives the bound by its degree plus the actual dimension of L(0). Principal degree zero restores deg(A).','若 L(A) 为零则上界直接成立。否则选取其中非零函数 z，使 A+div(z) 有效。乘以 z 给出相应 Riemann 空间与 L(A) 的线性同构。逐处加上这个有效除子，维数增加量不超过其次数；再用主除子次数为零得到原上界，其中保留实际的 L(0) 维数。','空間が零の場合を除き、非零元 z により A+div(z) を有効にする。z の乗法による線形同型と一素点ごとの次元評価を用い、主因子の次数零により元の評価を得る。L(0) の実際の次元を保つ。'),
 'riemannRochEventuallyLinear':('The actual basis-power lower bound controls degree minus dimension along multiples of the pole divisor of u. Principal modification and the approximation child transfer this bound to every divisor. This integer-valued defect therefore has an attained maximum. Monotonicity after a suitable effective modification forces every sufficiently large-degree divisor to have that same defect, giving uniform eventual linearity.','实际基底幂的维数下界控制 u 的极点除子各倍数上的次数与维数之差。主除子修改与逼近子定理将此界传递给所有除子。整数值差因而有一个被实际除子取到的最大值；对足够大次数的除子作有效修改，单调性迫使其差等于这个最大值，从而得到统一的最终线性公式。','実際の基底の冪による下界が u の極因子の倍数上の次数と次元の差を抑える。主因子による変更と近似により全因子へ移し、整数値の差の最大値を取る因子を得る。有効な変更後の単調性から十分大きい次数で差が一定となる。'),
 'polarPresentationExists':('The three dimension children imply that, above one uniform degree threshold, L(A-P) is a proper subspace of L(A) for every place in the finite support of an effective A. A finite union of these proper subspaces cannot cover a rational vector space. A function outside the union has exactly the prescribed poles. Add the same sufficiently large effective divisor to the positive and negative parts of the requested divisor, realize both polar divisors, then subtract to cancel the auxiliary divisor.','三个维数子定理保证：有效除子的次数超过统一阈值后，对其有限支撑中的每个处 P，L(A−P) 都是 L(A) 的真子空间。有限个真子空间不能覆盖有理数向量空间，因此可选函数恰有指定极点除子。将同一个足够大的有效除子分别加到目标除子的正部与负部，实现两个极点除子，再相减消去辅助除子。','三つの次元命題から、十分大きい次数では各 L(A−P) が L(A) の真部分空間となる。有限個の真部分空間を避ける元を選び、指定された極因子を実現する。求める因子の正部分と負部分に共通の十分大きい有効因子を加えてそれぞれを実現し、差を取る。')}
for n in ['placesDiscrete','residuesFinite','riemannRochFiniteDimensional','riemannRochDimensionUpperBound','riemannRochEventuallyLinear','polarPresentationExists']:
 target=(old if n in ['placesDiscrete','residuesFinite','polarPresentationExists'] else ids)[pre+n]
 explanation=quote+prose([pre+n])+'\n\n'+'\n\n'.join('**'+label+'**\n\n'+body for label,body in zip(['Argument','论证','証明の構成'],arguments[n]))+'\n\n'+common+('The existing source proof closes this node directly.' if n in ['placesDiscrete','residuesFinite'] else 'This proof is a reduction. Its imported geometric children remain Open; the body itself contains no admission.')
 verify('reduce-'+n,target,'.local/adaptation/fermat-riemann-20261113/Solution_'+n+'.lean',explanation)
save('root-graph-after.json',api.request('/theorems/'+ROOT+'/graph?depth=10'))
for n in ['polarPresentationExists','riemannRochFiniteDimensional','riemannRochDimensionUpperBound','riemannRochEventuallyLinear']:
 target=(old if n=='polarPresentationExists' else ids)[pre+n];save('graph-'+n+'.json',api.request('/theorems/'+target+'/graph?depth=3'))
leaves=[];offset=0
while True:
 x=api.request('/theorems/'+ROOT+'/open-leaves?limit=50&offset='+str(offset));save('root-frontier-page-'+str(offset)+'.json',x);leaves.extend(x['open_leaves']);offset+=len(x['open_leaves'])
 if offset>=x['total']:break
 assert x['open_leaves']
assert len({x['theorem_id'] for x in leaves})==len(leaves)
save('root-frontier-after.json',{'root_id':ROOT,'open_leaves':leaves,'total':x['total'],'all_pages_fetched':True})
print('Riemann two-layer private reductions complete.',flush=True)
