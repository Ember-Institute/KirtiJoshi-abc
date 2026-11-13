from pathlib import Path
import ast,json,hashlib,importlib.util,urllib.request,urllib.error,uuid,time
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
b=w/'.local/adaptation/canonical-high-height-20261113'
s=importlib.util.spec_from_file_location('p2m_api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(s);s.loader.exec_module(api)
ENV='0df444a360eaa60ab8c11dca51a86af692955474'
ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5'
PARENT='54209a9c-d508-41f4-b24c-f8a293eacdb9'
def save(name,data):(b/name).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
# Reuse the same private publication and verification protocol as the preceding unit.
prior=Path('/tmp/p2m-platform-tripod-20261113.py').read_text()
for node in ast.parse(prior).body:
 if isinstance(node,ast.FunctionDef) and node.name in ['publish','verify']:
  exec(compile(ast.Module(body=[node],type_ignores=[]),'<prior-platform-protocol>','exec'),globals())
readback_root=w/'.local/adaptation/readbacks/canonical-high-height-v1'
rb=json.loads((readback_root/'result.json').read_text())
def prose(names):
 return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+n+'`\n\n'+rb[n][lang] for n in names) for lang,title in [('en','English'),('zh','简体中文'),('ja','日本語')])
quote='> “But such an inequality follows immediately, in light of the [relevant] equality of BD-classes of Corollary 2.2, (i), from Corollary 2.2, (ii) [cf. condition (C2)], (iii) […]”\n\n— Shinichi Mochizuki, *Inter-universal Teichmüller Theory IV*, §2, proof of Corollary 2.3.\n\n'
source_common='Shinichi Mochizuki, Inter-universal Teichmüller Theory IV, §2, Corollary 2.2(i)–(iii) and proof of Corollary 2.3; https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf . Independently adapted under Apache 2.0; no Iut or Genl imports. '
sources={
 'inputs':source_common+'Exact Lean expressions: refer/iut/Iut/Tripod/Height.lean:58 (finHeight), :246 (legendreJ), :603 (h_eq_finHeight_div), :791 (legendreHeight); refer/iut/Iut/Implication/Corollary22.lean:107 (epsilonE), :111 (epsilonE_le), :273 (deltaBound), :386 (c2). The three predicates specify Open mathematical children, not supplied proof assumptions.',
 'compare':source_common+'Exact Lean source refer/iut/Iut/Tripod/Height.lean:603 h_eq_finHeight_div and :791 legendreHeight. The stated absolute-discrepancy consequence combines both directional bounds and retains the actual field Q(x), finite places, 256 coefficient and division by degree.',
 'c2':source_common+'Exact Lean source refer/iut/Iut/Implication/Corollary22.lean:338 excCore_finite, :378 threshold, :386 c2; refer/iut/Iut/Tripod/Height.lean:603. This is the full three-conclusion extracted consequence on the actual tripod, not the polymorphic c2 signature. The future source-construction decomposition must use one common Corollary22 input source, E=excCore intersect (K.set intersect ptLE d), H=I.threshold cheb and C=40*pnt.eta+I.B/3; these source identities remain Open work.',
 'epsilon':source_common+'Exact Lean source refer/iut/Iut/Implication/Corollary22.lean:107 epsilonE and :111 epsilonE_le. Both the explicit fourth-power threshold and the independent hypothesis 1 <= h are retained.',
 'composition':source_common+'Exact source composition refer/iut/Iut/Implication/Corollary23.lean:56–112. The three Open children imply HighHeightEstimate by absorbing the finite exceptional set below a height threshold, transferring between the two fixed heights and applying the explicit error bound. This conditional combination does not close any of its three children.'
}
# Require the complete local receipt sequence, and the independently audited exact input version.
expected=['inputs-leaf','inputs-artifact','composition-leaf','composition-artifact']
for n in ['canonicalLegendreHeightComparison','canonicalCorollary22HighHeightEstimate','epsilonELargeHeight']:
 expected.extend([n+'-leaf',n+'-artifact'])
expected.extend(['solution-leaf','solution-artifact','composition-review','reduction-axioms-leaf'])
for tag in expected:
 d=json.loads((b/(tag+'-result.json')).read_text())
 assert d['status']=='succeeded' and d['result']['exit_code']==0,tag
 assert d['request']['exclusive'] is True,tag
 assert d.get('workspace_mode')=='exclusive_worktree' or d.get('snapshot',{}).get('workspace_mode')=='exclusive_worktree' or d['request']['exclusive'],tag
 if tag=='composition-review':assert d['result']['review']['passed'],tag
for f,sha in json.loads((readback_root/'input-hashes.json').read_text()).items():
 assert hashlib.sha256((w/f).read_bytes()).hexdigest()==sha,f
predicates=['AbcAdaptation.Tripod.'+n for n in ['finHeight','legendreJ','auxiliaryHeight','deltaBound','epsilonE','CanonicalLegendreHeightComparison','CanonicalCorollary22HighHeightEstimate','EpsilonELargeHeight']]
for name,names,src in [('TripodCanonicalHighHeightInputs',predicates,'inputs'),('TripodCanonicalHighHeightComposition',['AbcAdaptation.Tripod.highHeightEstimate_of_canonical_children'],'composition')]:
 code=(w/('Definitions/Def_'+name+'.lean')).read_text();assert 'sorry' not in code
 payload={'definition_name':name,'definition_title':{'TripodCanonicalHighHeightInputs':'Canonical Legendre height and precise large-height inputs','TripodCanonicalHighHeightComposition':'Composition of the canonical large-height estimates'}[name],'definition':code,'natural_language_statement':quote+prose(names),'source':sources[src],'env':ENV,'private':True,'tags':['abc-conjecture','arithmetic-teichmuller-spaces','arithmetic-geometry']}
 publish('def-'+name,'/submit-definition',payload)
entries=[('canonicalLegendreHeightComparison','CanonicalLegendreHeightComparison','compare','Canonical Legendre height comparison on compactly bounded sets'),('canonicalCorollary22HighHeightEstimate','CanonicalCorollary22HighHeightEstimate','c2','Canonical Corollary 2.2 estimate with its finite exceptional set'),('epsilonELargeHeight','EpsilonELargeHeight','epsilon','Explicit fourth-power threshold for the Corollary 2.2 error')]
problems=[]
for n,p,src,title in entries:
 name='AbcAdaptation.Tripod.'+n
 problems.append({'theorem_name':name,'theorem_title':title,'preamble':'import Definitions.Def_TripodCanonicalHighHeightInputs\n\nset_option autoImplicit false','formal_statement':'theorem '+name+' : AbcAdaptation.Tripod.'+p+' := by sorry','natural_language_statement':quote+prose([name]),'source':sources[src],'tags':['abc-conjecture','arithmetic-teichmuller-spaces','arithmetic-geometry']})
results=publish('canonical-children','/submit-problem',{'problems':problems,'env':ENV,'private':True})
ids={x['theorem_name']:x['theorem_id'] for x in results};save('published-child-ids.json',ids)
en='The auxiliary height is fixed by the actual Legendre j-invariant over Q(x). The three children provide its comparison with the existing normalized height, the Corollary 2.2 inequality outside a finite exceptional set, and the explicit decay estimate for its error function. Bound the existing height on the exceptional set, raise the final threshold to cover this bound and both analytic thresholds, transfer the canonical estimate to the existing height, and enlarge the error coefficient using nonnegativity of the logarithmic different and conductor. This proves a reduction to the three Open children. The arithmetic source construction behind the Corollary 2.2 child remains to be decomposed.\n\n'+sources['composition']
zh='辅助高度固定为实际单生成数域上 Legendre 曲线不变量的有限处对数高度除以该点次数。三个子定理分别提供它与既有归一化高度的比较、有限例外集外的推论二点二不等式，以及误差函数的显式衰减估计。先给例外集上的既有高度取上界，再将最终阈值提高到同时覆盖该上界与两个解析阈值；利用高度比较转移不等式，并用对数不同理想项与导子项的非负性放大误差系数。三个子定理仍为开放节点，其中推论二点二所需的共同算术来源还要继续拆分。'
ja='補助的な高さは、実際の単純生成数体上の Legendre 曲線の不変量から得られる有限素点の対数的高さを、その点の次数で割ったものに固定する。三つの子定理は、既存の正規化された高さとの比較、有限例外集合の外での系2.2の不等式、および誤差関数の明示的な減衰評価を与える。例外集合上の高さに上界を取り、その上界と二つの解析的なしきい値を覆うように最終しきい値を上げる。高さの比較で不等式を移し、対数的な不同項と導手項の非負性により誤差係数を拡大する。三つの子定理は未証明であり、系2.2に必要な共通の算術的構成は引き続き分解する。'
verify('high-height-to-canonical',PARENT,'Solutions/Sol_TripodHighHeightEstimate.lean',quote+'**English**\n\n'+en+'\n\n**简体中文**\n\n'+zh+'\n\n**日本語**\n\n'+ja)
for tag,path in [('root-graph-after','/theorems/'+ROOT+'/graph'),('root-frontier-after','/theorems/'+ROOT+'/open-leaves')]:
 x=api.request(path);save(tag+'.json',x);print(tag,json.dumps(x,ensure_ascii=False)[:1200],flush=True)
print('Canonical large-height private platform unit completed.',flush=True)
