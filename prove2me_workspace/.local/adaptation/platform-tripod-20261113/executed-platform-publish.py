from pathlib import Path
import json,hashlib,importlib.util,urllib.request,urllib.error,uuid,time
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/platform-tripod-20261113';b.mkdir(exist_ok=True)
s=importlib.util.spec_from_file_location('p2m_api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(s);s.loader.exec_module(api)
ENV='0df444a360eaa60ab8c11dca51a86af692955474';ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5';RATIONAL='905ccf0a-2831-4751-852f-92b19b256a89'
current=json.loads((w/'.local/adaptation/readbacks/tripod-current-v1/result.json').read_text());rb={r['name']:r for r in current};rb.update({r['name']:r for r in json.loads((w/'.local/adaptation/readbacks/statement-ii-v1/result.json').read_text())})

def save(name,data):(b/name).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
def prose(names):return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+n+'`\n\n'+rb[n][lang] for n in names) for lang,title in [('en','English'),('zh','简体中文'),('ja','日本語')])
quote='> “Thus, it follows from the equivalence of [GenEll], Theorem 2.1, that, in order to complete the proof of Corollary 2.3, it suffices to verify that [GenEll], Theorem 2.1, (ii), holds.”\n\n— Shinichi Mochizuki, *Inter-universal Teichmüller Theory IV*, §2, proof of Corollary 2.3.'
sources={
 'tripod':'Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position, Theorem 2.1(i),(ii), printed pp.11–13, https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf ; Inter-universal Teichmüller Theory IV, §2, Corollary 2.3. Exact Lean source refer/iut/Iut/Tripod/Basic.lean:70–385; independently adapted without Iut or Genl imports.',
 'rational':'Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position, Theorem 2.1(i), rational-tripod specialization; Inter-universal Teichmüller Theory IV, §2, Corollary 2.3. Exact Lean source refer/iut/Iut/Tripod/ClassicalAbc.lean:73 (degree), :93 (different), :198 (height comparison), :144 (conductor), :227 (classical integer implication).',
 'finite':'Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position, Proposition 1.4(iv) and Theorem 2.1(ii); Inter-universal Teichmüller Theory IV, proof of Corollary 2.3. Exact Lean source refer/iut/Iut/Tripod/Northcott.lean:183 and refer/iut/Iut/Implication/Corollary23.lean:56–112. BoundedDegreeFiniteness uses the existing actual normalized height on all algebraic points of bounded degree. HighHeightEstimate is the precise extracted high-height consequence; its arithmetic and height-transfer requirements remain Open children.',
 'ii_i':'Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position, Theorem 2.1(ii) implies (i), printed pp.11–13; https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf . Exact Lean source refer/iut/Iut/Tripod/GeneralPosition.lean:269; its proof factors through the height theory of all curves, noncritical Belyi maps and ramified coverings.'
}
def publish(tag,endpoint,payload):
 save(tag+'-payload.json',payload);sub=b/(tag+'-submit.json')
 if sub.exists():r=json.loads(sub.read_text())
 else:r=api.request(endpoint,payload,'POST');save(sub.name,r)
 if r.get('errors'):raise RuntimeError(r['errors'])
 jobs=r.get('jobs') or [{'job_id':r['job_id'],'name':r.get('definition_name')}]
 results=[]
 for job in jobs:
  print('publish',tag,job['job_id'],flush=True)
  while True:
   x=api.request('/publish-jobs/'+job['job_id']);save(tag+'-'+job['job_id']+'-result.json',x)
   if x['status'] in ['PUBLISHED','FAILED','ERROR']:break
   time.sleep(5)
  print('result',x.get('theorem_name'),x['status'],x.get('error_message',''),flush=True)
  if x['status']!='PUBLISHED':raise RuntimeError(x.get('error_message') or x['status'])
  results.append(x)
 return results

def definition(name,names,source):
 code=(w/('Definitions/Def_'+name+'.lean')).read_text();assert 'sorry' not in code
 payload={'definition_name':name,'definition_title':name+' — concrete arithmetic interfaces','definition':code,'natural_language_statement':quote+'\n\n'+prose(names),'source':source,'env':ENV,'private':True,'tags':['abc-conjecture','arithmetic-teichmuller-spaces','arithmetic-geometry']}
 return publish('def-'+name,'/submit-definition',payload)[0]

def children():
 entries=[('degreeOneProjection','DegreeOneProjection','rational'),('logDifferentZeroProjection','LogDifferentZeroProjection','rational'),('heightComparisonProjection','HeightComparisonProjection','rational'),('radicalConductorProjection','RadicalConductorProjection','rational'),('statementII','StatementII','tripod'),('statementI_of_statementII','StatementI','ii_i'),('boundedDegreeFiniteness','BoundedDegreeFiniteness','finite'),('highHeightEstimate','HighHeightEstimate','finite')]
 problems=[]
 for n,p,src in entries:
  name='AbcAdaptation.Tripod.'+n
  imported='TripodStatementIIInputs' if src=='finite' else 'AbcTripod'
  pre='import Definitions.Def_'+imported+'\n\nset_option autoImplicit false'
  ty=('(hII : AbcAdaptation.Tripod.StatementII) : ' if n=='statementI_of_statementII' else ': ')+'AbcAdaptation.Tripod.'+p
  formal='theorem '+name+' '+ty+' := by sorry'
  problems.append({'theorem_name':name,'theorem_title':{'degreeOneProjection':'Degree one of rational tripod points','logDifferentZeroProjection':'Vanishing logarithmic different for rational tripod points','heightComparisonProjection':'Comparison with the actual rational logarithmic height','radicalConductorProjection':'Rational conductor bounded by the integer radical','statementII':'Uniform height inequality on compactly bounded tripod subsets','statementI_of_statementII':'General-position transfer from compactly bounded to bounded-degree points','boundedDegreeFiniteness':'Northcott finiteness for all bounded-degree tripod points','highHeightEstimate':'Asymptotic high-height estimate on compactly bounded tripod subsets'}[n],'preamble':pre,'formal_statement':formal,'natural_language_statement':quote+'\n\n'+prose([name]),'source':sources[src],'tags':['abc-conjecture','arithmetic-teichmuller-spaces','arithmetic-geometry']})
 results=publish('tripod-children','/submit-problem',{'problems':problems,'env':ENV,'private':True})
 return {x['theorem_name']:x['theorem_id'] for x in results}

def verify(tag,target,file,explanation):
 code=(w/file).read_bytes();assert b'sorry' not in code;own=api.request('/theorems/'+target);assert own['visibility']=='private' and own['mathlib_rev']==ENV
 assert ('import Theorems.Thm_'+own['theorem_name'].replace('.','_')).encode() not in code
 meta={'theorem_id':target,'proof_type':'prove','file':file,'source_sha256':hashlib.sha256(code).hexdigest(),'explanation':explanation};save(tag+'-verify-request.json',meta);(b/(tag+'-solution.lean')).write_bytes(code)
 p=b/(tag+'-verify-submit.json')
 if p.exists():result=json.loads(p.read_text())
 else:
  boundary='p2m-'+uuid.uuid4().hex;parts=[]
  for name,value in [('theorem_id',target),('proof_type','prove'),('explanation',explanation)]:parts.append(('--'+boundary+'\r\nContent-Disposition: form-data; name="'+name+'"\r\n\r\n'+value+'\r\n').encode())
  parts.extend([('--'+boundary+'\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode()+code+b'\r\n',('--'+boundary+'--\r\n').encode()]);cred=json.loads((w/'credentials.json').read_text());req=urllib.request.Request(api.base+'/verify',data=b''.join(parts),headers={'Authorization':'Bearer '+cred['access_token'],'Accept':'application/json','Content-Type':'multipart/form-data; boundary='+boundary},method='POST')
  try:
   with api.opener.open(req,timeout=45) as response:result=json.load(response)
  except urllib.error.HTTPError as e:raise RuntimeError('HTTP '+str(e.code)+': '+e.read().decode()[:2000]) from None
  save(p.name,result)
 sub=result['submission_id'];print('verify',tag,sub,flush=True)
 while True:
  x=api.request('/verify?submission_id='+sub);save(tag+'-verify-result.json',x)
  if x['status']!='PENDING':break
  time.sleep(5)
 print('verdict',tag,x['status'],x.get('error_message',''),flush=True)
 assert x['status'] in ['SKETCH_ACCEPTED','ACCEPTED'],x
 return x

# Existing main-agent exclusive CI receipts are the compile evidence for these unchanged sources.
for receipt in ['final-leaf-audit-20261113/tripod-rational-composition-review-result.json','tripod-unit-20261113/statement-ii-composition-review-result.json']:
 x=json.loads((w/'.local/adaptation'/receipt).read_text());assert x['status']=='succeeded' and x['result']['review']['passed']
all_tripod=[r['name'] for r in current if r['name'].startswith('AbcAdaptation.Tripod.') and r['name'] not in ['AbcAdaptation.Tripod.rationalABCHeight_of_statementI','AbcAdaptation.Tripod.degreeOneProjection','AbcAdaptation.Tripod.logDifferentZeroProjection','AbcAdaptation.Tripod.heightComparisonProjection','AbcAdaptation.Tripod.radicalConductorProjection','AbcAdaptation.Tripod.statementII','AbcAdaptation.Tripod.statementI_of_statementII']]
definition('AbcTripod',all_tripod,sources['tripod'])
definition('TripodRationalComposition',['AbcAdaptation.Tripod.rationalABCHeight_of_statementI'],sources['rational'])
definition('TripodStatementIIInputs',['AbcAdaptation.Tripod.BoundedDegreeFiniteness','AbcAdaptation.Tripod.HighHeightEstimate'],sources['finite'])
definition('TripodStatementIIComposition',['AbcAdaptation.Tripod.statementII_of_children'],sources['finite'])
ids=children();save('published-child-ids.json',ids)
en='The rational logarithmic-height inequality reduces to six precise children. The compactly bounded tripod estimate and the general-position implication yield Statement I for all bounded-degree algebraic points. For a rational point, the other four children identify degree one, logarithmic different zero, its actual rational height, and the conductor upper bound by the logarithm of the integer radical. Apply Statement I at degree one; substitute these four conclusions and use $1+\\varepsilon>0$ to obtain the rational inequality with the same additive constant. All six children remain Open. Source: Mochizuki, Arithmetic Elliptic Curves in General Position, Theorem 2.1, and IUT IV, §2, Corollary 2.3; reference arithmetic chain refer/iut/Iut/Tripod/ClassicalAbc.lean:227 and GeneralPosition.lean:269.'
zh='有理数对数高度界归约到六个精确子定理。紧有界三支点曲线估计与一般位置传递给出全部有界次数代数点上的命题一；其余四项分别给出有理点次数为一、对数不同理想项为零、实际有理数高度比较，以及导子不超过整数根基的对数。将命题一用于次数一，代入这四个结论，并使用 $1+\\varepsilon>0$，即以同一个加法常数得到有理数不等式。六个子定理均仍开放。'
ja='有理数の対数的高さの不等式を六つの明示的な子定理に帰着する。三点を除いた射影直線のコンパクト有界部分集合上の評価と一般位置への移行から、有界次数のすべての代数点に対する命題一を得る。残る四つは、有理点の次数が一であること、対数的な不同項の消失、実際の有理数の高さとの比較、および導手の整数根基による評価である。次数一に命題一を適用し、これらを代入して $1+\\varepsilon>0$ を用いると、同じ加法定数で有理数の不等式が得られる。六つの子定理は未証明のままである。'
verify('rational-to-tripod',RATIONAL,'Solutions/Sol_abc_rational_height.lean','**English**\n\n'+en+'\n\n**简体中文**\n\n'+zh+'\n\n**日本語**\n\n'+ja)
en='For a positive degree bound, the high-height child supplies a uniform threshold $H$ and constant $C$. The bounded-degree finiteness child makes the eligible points of height at most $H$ finite. Their discrepancy $h-(1+\\varepsilon)(D+R)$ therefore has a real upper bound $B$. The constant $\\max(C,B)$ covers both the low-height set and all points above $H$. Degree zero has no eligible points. This proves the reduction to exactly these two Open children, rather than proving either child. Source: Mochizuki, IUT IV, proof of Corollary 2.3; reference finite-exception composition refer/iut/Iut/Implication/Corollary23.lean:56–112.'
zh='对于正次数界，高点估计子定理提供统一阈值 $H$ 与常数 $C$。有界次数有限性子定理保证高度不超过 $H$ 的合格点构成有限集，其偏差 $h-(1+\\varepsilon)(D+R)$ 因而有实数上界 $B$。取常数 $\\max(C,B)$ 即同时覆盖低点集与阈值以上的点。次数零时没有合格点。这建立了到两个开放子定理的归约，未证明这两个子定理本身。'
ja='正の次数上限について、高さの大きい点の評価から一様なしきい値 $H$ と定数 $C$ を得る。有界次数の有限性により、高さが $H$ 以下の該当点は有限個なので、その差 $h-(1+\\varepsilon)(D+R)$ は実数の上界 $B$ を持つ。定数 $\\max(C,B)$ により低い高さの点としきい値を超える点を同時に扱える。次数零では該当点がない。これにより二つの未証明の子定理への帰着を得るのであり、子定理自体の証明ではない。'
verify('statement-ii-to-children',ids['AbcAdaptation.Tripod.statementII'],'Solutions/Sol_TripodStatementII.lean','**English**\n\n'+en+'\n\n**简体中文**\n\n'+zh+'\n\n**日本語**\n\n'+ja)
for tag,path in [('root-graph-after','/theorems/'+ROOT+'/graph'),('root-frontier-after','/theorems/'+ROOT+'/open-leaves')]:
 x=api.request(path);save(tag+'.json',x);print(tag,json.dumps(x,ensure_ascii=False)[:7000],flush=True)
