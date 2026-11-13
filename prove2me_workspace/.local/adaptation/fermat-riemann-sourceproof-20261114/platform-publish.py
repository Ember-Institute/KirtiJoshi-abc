from pathlib import Path
import ast,json,hashlib,importlib.util,urllib.request,urllib.error,uuid,time
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/fermat-riemann-sourceproof-20261114';pre='AbcAdaptation.Tripod.Fermat.Proper.'
spec=importlib.util.spec_from_file_location('api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
ENV='0df444a360eaa60ab8c11dca51a86af692955474';ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5'
def save(n,x):(b/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
source=(w/'.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
for n in ast.parse(source).body:
 if isinstance(n,ast.FunctionDef) and n.name in ['publish','verify']:exec(compile(ast.Module(body=[n],type_ignores=[]),'<previous-platform-protocol>','exec'),globals())
v=json.loads((b/'sourceproof-validation.json').read_text());assert v['passed'] and v['exact_platform_types_equal']
# Bind delivery to the exact local files that passed scheduled validation.
for relative, expected in v['definition_hashes'].items():
 assert hashlib.sha256((w/relative).read_bytes()).hexdigest()==expected, relative
for name, expected in v['theorem_hashes'].items():
 relative='Theorems/Thm_'+name.replace('.','_')+'.lean'
 assert hashlib.sha256((w/relative).read_bytes()).hexdigest()==expected, relative
assert hashlib.sha256((b/'decl_graph.jsonl').read_bytes()).hexdigest()==v['declaration_graph_sha256']
assert json.loads((b/'platform-types-equal.json').read_text()) is True
for name in ['functionZeroPoleDegrees','riemannPolarApproximation','riemannBasisPowerLowerBound']:
 relative='.local/adaptation/fermat-riemann-sourceproof-20261114/Solution_'+name+'.lean'
 receipt=json.loads((b/('solution-'+name+'-leaf-result.json')).read_text())
 assert receipt['status']=='succeeded' and receipt['result']['exit_code']==0
 assert receipt['request']['parameters']['source']==relative
 assert receipt['request']['worktree_manifest']['source_sha256']==hashlib.sha256((w/relative).read_bytes()).hexdigest(), relative
exact=json.loads((b/'exact-platform-types-leaf-result.json').read_text())
assert exact['status']=='succeeded' and exact['result']['exit_code']==0
assert exact['request']['worktree_manifest']['source_sha256']==hashlib.sha256((b/'ValidatePlatformTypes.lean').read_bytes()).hexdigest()
# Refuse cached submissions if their original saved request differs.
original_publish=publish
original_verify=verify
def publish(tag, endpoint, payload):
 if (b/(tag+'-submit.json')).exists():
  assert json.loads((b/(tag+'-payload.json')).read_text())==payload, tag
 return original_publish(tag, endpoint, payload)
def verify(tag, target, file, explanation):
 if (b/(tag+'-verify-submit.json')).exists():
  previous=json.loads((b/(tag+'-verify-request.json')).read_text())
  assert previous['theorem_id']==target and previous['file']==file
  assert previous['source_sha256']==hashlib.sha256((w/file).read_bytes()).hexdigest(), tag
  assert previous['explanation']==explanation, tag
 return original_verify(tag, target, file, explanation)
for f,sha in v['definition_hashes'].items():assert hashlib.sha256((w/f).read_bytes()).hexdigest()==sha
for tag in ['sourceproof-closed-review','source-closure-review','all-new-definition-axioms-review','production-gates-review']:
 x=json.loads((b/(tag+'-result.json')).read_text());assert x['status']=='succeeded' and x['result']['review']['passed'];assert 'sorryAx' not in x['result']['stdout']
rb=json.loads((b/'readbacks-final.json').read_text());rows=rb['declarations'];quote=(b/'mochizuki-quotation.md').read_text()
def prose(items):return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+x['declaration']+'`\n\n'+x[key] for x in items) for key,title in [('en','English'),('zh_Hans','简体中文'),('ja','日本語')])
common='Shinichi Mochizuki, Noncritical Belyi Maps, proof of Theorem 2.5, printed p.6, https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . The cited passage provides geometric context for divisors and sections; the exact Lean proof is independently adapted from the Apache-2.0 Belyi project at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8, pinned by refer/iut. No Belyi/Iut/Genl runtime dependency is added. '
modules={'FermatCurveFieldDegree':'Belyi/CurveField/Degree.lean:47–327. Actual integral closure, ideal ramification/inertia sums, full residue fields, and inverse chart for poles. Explicit canonical local algebra instances replace expensive search paths; mathematical hypotheses are unchanged.','FermatFunctionFiberDegrees':'Belyi/CurveField/Divisor.lean:190–213. The genuine existing zero and pole divisors are expanded over all positive/negative-order places, with the actual residue-degree-weighted degree.','FermatRiemannPolarApproximation':'Belyi/CurveField/Riemann.lean:54–158. Actual residue minimal polynomials and finite divisor induction give one global nonzero function controlling all places simultaneously.','FermatRiemannBasisPowers':'Belyi/CurveField/Riemann.lean:164–213. Genuine powers times the actual rational-function-field basis are independent vectors in the actual Riemann space. The original finite-dimensionality premise and exact N count are retained.'}
for mod,ref in modules.items():
 f='Definitions/Def_'+mod+'.lean';items=[r for r in rows if Path(r['path']).name==Path(f).name];assert items,mod
 publish('def-'+mod,'/submit-definition',{'definition_name':mod,'definition_title':mod+' — source proofs on actual function fields','definition':(w/f).read_text(),'natural_language_statement':quote+prose(items),'source':common+ref,'env':ENV,'private':True,'tags':['abc-conjecture','arithmetic-geometry']})
ids=json.loads((w/'.local/adaptation/fermat-riemann-20261113/published-child-ids.json').read_text())
arguments={
 'functionZeroPoleDegrees':('The normalized order at a chart place is its ideal valuation. The quotient by its prime ideal is the full existing residue field. At the prime generated by the coordinate, the sum of ramification index times inertia degree equals the function-field extension degree. The chart-place bijection gives the complete zero divisor sum; apply it to the inverse coordinate to obtain the pole sum.','图册处的规范化阶数等于相应理想赋值，素理想商等于原有完整剩余域。在坐标生成的素理想上，分歧指数与惯性次数的乘积求和等于函数域扩张次数。图册与处的双射给出全部零点处的求和；再对倒数坐标应用同一公式，得到极点次数。','チャートの正規化位数をイデアル付値と同定し、素イデアルによる商を既存の剰余体と同定する。分岐指数と惰性次数の積の和の公式を全素点の零点和へ移し、逆元の座標に適用して極の和も得る。'),
 'riemannPolarApproximation':('At a pole of the fixed coordinate, adding one copy of the place is absorbed by its pole divisor. At a regular place, evaluate the minimal polynomial of the actual residue of the coordinate. The evaluation is nonzero by transcendence and has positive order at that place. Divide the current function by this evaluation; the global polynomial pole bound controls every other place. Finite-support induction yields one global witness for each divisor.','在固定坐标的极点处，极点除子吸收一个处的副本；在正则处，取坐标的实际剩余值的最小多项式并求值。超越性保证求值非零，剩余映射保证该处阶数为正。用此值除当前函数，再由全局多项式极点界控制其余所有处。对有限支撑归纳，便为每个除子取得同一个全局见证。','極では極因子に素点を一つ加えて処理する。正則な素点では座標の剰余の最小多項式を評価し、超越性から非零、剰余の消失から正の位数を得る。この評価で関数を割り、全素点での極の評価と有限台の帰納法を用いる。'),
 'riemannBasisPowerLowerBound':('For every basis vector b_i and 0≤k≤l, the function u^k b_i lies in L(l(u)_∞+C), where C is the actual sum of basis pole divisors. Transcendental polynomial evaluation makes the powers independent over Q; scalar-tower independence combines them with the actual Q(u)-basis. The finite-dimensionality premise bounds this independent family’s cardinality by the actual finrank, and the model degree identifies the basis size with N.','对每个实际基向量及不超过 l 的坐标幂，其乘积都属于同一个由实际极点修正控制的 Riemann 空间。超越多项式求值给出幂的有理线性无关性，再沿标量塔与实际有理函数域基组合。保留的有限维性前提使这一无关族的基数不超过实际有限秩；模型次数将基底大小识别为 N。','実際の基底の各元と座標の零から l までの冪との積が同じ Riemann 空間に入ることを示す。超越的な多項式評価とスカラー塔の独立性からこの族は有理数体上独立である。有限次元性から元の個数を有限階数で抑え、模型の次数により基底の大きさを N とする。')}
for n,arg in arguments.items():
 items=[r for r in rows if r['declaration']==pre+n];assert len(items)==1
 explanation=quote+prose(items)+'\n\n'+'\n\n'.join('**'+label+'**\n\n'+body for label,body in zip(['Argument','论证','証明の構成'],arg))+'\n\n'+common+'This submission reuses the complete pinned source proof and has no Open mathematical child.'
 x=verify('prove-'+n,ids[pre+n],'.local/adaptation/fermat-riemann-sourceproof-20261114/Solution_'+n+'.lean',explanation);assert x['status']=='ACCEPTED'
old=json.loads((w/'.local/adaptation/fermat-proper-canonical-20261113/published-child-ids.json').read_text())
for n in ['functionZeroPoleDegrees','riemannPolarApproximation','riemannBasisPowerLowerBound','riemannRochFiniteDimensional','riemannRochDimensionUpperBound','riemannRochEventuallyLinear','polarPresentationExists']:
 target=(old if n=='polarPresentationExists' else ids)[pre+n];x=api.request('/theorems/'+target);save('platform-after-'+n+'.json',x);print('node-status',n,x['status'],flush=True)
save('root-graph-after.json',api.request('/theorems/'+ROOT+'/graph?depth=10'))
leaves=[];offset=0
while True:
 x=api.request('/theorems/'+ROOT+'/open-leaves?limit=50&offset='+str(offset));save('root-frontier-page-'+str(offset)+'.json',x);leaves.extend(x['open_leaves']);offset+=len(x['open_leaves'])
 if offset>=x['total']:break
 assert x['open_leaves']
assert len({x['theorem_id'] for x in leaves})==len(leaves)
save('root-frontier-after.json',{'open_leaves':leaves,'total':x['total'],'all_pages_fetched':True})
print('Three direct source proofs synchronized.',flush=True)
