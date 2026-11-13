from pathlib import Path
import ast,json,hashlib,importlib.util,urllib.request,urllib.error,uuid,time
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/fermat-general-position-20261113'
s=importlib.util.spec_from_file_location('p2m_api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(s);s.loader.exec_module(api)
ENV='0df444a360eaa60ab8c11dca51a86af692955474';ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5';PARENT='29d69993-e4b0-483a-8557-835cf1953b08'
def save(name,data):(b/name).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
prior=(w/'.local/adaptation/canonical-high-height-20261113/platform-publish.py').read_text()
# publish and verify are the same stable API protocol as the preceding unit.
protocol=(Path('/tmp/p2m-platform-tripod-20261113.py')).read_text()
for node in ast.parse(protocol).body:
 if isinstance(node,ast.FunctionDef) and node.name in ['publish','verify']:
  exec(compile(ast.Module(body=[node],type_ignores=[]),'<private-platform-protocol>','exec'),globals())
readback_root=w/'.local/adaptation/readbacks/fermat-general-position-v1';rb=json.loads((readback_root/'result.json').read_text())
def prose(names):return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+n+'`\n\n'+rb[n][lang] for n in names) for lang,title in [('en','English'),('zh','简体中文'),('ja','日本語')])
quote='> “Since every point of '+r'$U_X(\overline{\mathbb Q})^{\le d}$ clearly lifts to a point of $U_Y(\overline{\mathbb Q})^{\le d^{\prime}}$'+', this completes the verification of the claim.”\n\n— Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position*, proof of Theorem 2.1, printed p.12.\n\n'
common='Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position, Theorem 2.1 (printed pp.11–13), Propositions 1.4, 1.6, 1.7; https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf . Reference parent refer/iut/Iut/Tripod/GeneralPosition.lean:269. Independent Fermat specialization of Genl pinned ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf; this is a new adapted statement, not a renamed source theorem, and imports neither Iut, Genl, Heights nor Belyi. '
sources={
 'inputs':common+'Source Genl/Curves/Covering.lean:97 (actual Kummer roots), :177 (Fermat covering), :425–448 (different), :460–473 (degree/lifts); Genl/Curves/BelyiDescent.lean:248–327; Genl/Curves/Theory.lean:60. The field is Q(u,v), the normalized projective height is that of [u:v:1], and the fixed canonical representative is (N-3) times that height. Its identification with an actual canonical-divisor height remains the explicit duty of the CanonicalEstimate child.',
 'norm':common+'Source Genl/Curves/Covering.lean:177 and Genl/Curves/Theory.lean:60. This exact normalized-projective-height consequence must prove the field-tower normalization Q(u^N) subset Q(u,v), the Nth-power height identity and uniform comparison of [u:v:1] to [u:1]. The actual field inclusion is already a proved structural lemma; the height identities remain Open.',
 'lift':common+'Source Genl/Curves/Covering.lean:97, :425–448 and :460–473. Lift to actual nonzero Fermat coordinates with full point degree <=N^2*deg(z), and normalized log discriminant <=logDiff(z)+logCond(z)+C_N uniformly in z. This child owns the precise Kummer local different and actual-conductor comparison; it is not an arbitrary covering certificate.',
 'canonical':common+'Source Genl/Curves/BelyiDescent.lean:248–327 and Genl/GeneralPosition/TheoremTwoOne.lean:59, :132. Owns remaining explicit sub-decomposition of smoothness/geometric connectedness, adjunction omega=O(N-3), comparison with this fixed canonical-height representative, local compactness, noncritical Belyi maps, compactly bounded image, point-field discriminant normalization, cusp conductor comparison, strict-q argument and degree induction. These are still Open work, not hidden structure assumptions.',
 'composition':common+'Source epsilon bookkeeping Genl/GeneralPosition/TheoremTwoOne.lean:146. Choose N>max(3,3(1+epsilon)/epsilon), a=(N-3)/N and delta=a(1+epsilon)-1>0. The three precise children yield the parent StatementI from StatementII with a uniform additive constant. This proves only their conditional combination.'
}
expected=['inputs-leaf','inputs-artifact','composition-leaf','composition-artifact']
for n in ['heightNormalization','liftDifferent','canonicalEstimate']:expected += [n+'-leaf',n+'-artifact']
expected += ['solution-leaf','solution-artifact','composition-review','reduction-axioms-leaf']
for tag in expected:
 d=json.loads((b/(tag+'-result.json')).read_text());assert d['status']=='succeeded' and d['result']['exit_code']==0,tag
 snap=d['result']['snapshot'];assert snap['workspace_mode']=='exclusive_worktree' and snap['snapshot_id'] is None,tag
 if tag=='composition-review':assert d['result']['review']['passed'],tag
for f,sha in json.loads((readback_root/'input-hashes.json').read_text()).items():assert hashlib.sha256((w/f).read_bytes()).hexdigest()==sha,f
shape=json.loads((b/'shape-audit.json').read_text());assert shape.get('integration_blocked') is not True
inputs=['AbcAdaptation.Tripod.Fermat.'+n for n in ['Pt','fieldOf','degree','u','v','toTripod','fieldOf_toTripod_le','logDiff','projectiveHeight','canonicalHeight','coefficient','HeightNormalization','LiftDifferent','CanonicalEstimate']]
for name,names,src in [('TripodFermatInputs',inputs,'inputs'),('TripodFermatComposition',['AbcAdaptation.Tripod.statementI_of_fermat_children'],'composition')]:
 code=(w/('Definitions/Def_'+name+'.lean')).read_text();assert '\n  sorry' not in code
 publish('def-'+name,'/submit-definition',{'definition_name':name,'definition_title':{'TripodFermatInputs':'Actual Fermat points, heights and precise arithmetic inputs','TripodFermatComposition':'General-position transfer through actual Fermat curves'}[name],'definition':code,'natural_language_statement':quote+prose(names),'source':sources[src],'env':ENV,'private':True,'tags':['abc-conjecture','arithmetic-geometry','arithmetic-teichmuller-spaces']})
problems=[]
for n,p,src,title in [('heightNormalization','HeightNormalization','norm','Normalized projective height along the Fermat map'),('liftDifferent','LiftDifferent','lift','Fermat lifting with degree and logarithmic discriminant bounds'),('canonicalEstimate','CanonicalEstimate','canonical','Canonical height estimate on Fermat curves from Statement II')]:
 name='AbcAdaptation.Tripod.Fermat.'+n
 problems.append({'theorem_name':name,'theorem_title':title,'preamble':'import Definitions.Def_TripodFermatInputs\n\nset_option autoImplicit false','formal_statement':'theorem '+name+' : AbcAdaptation.Tripod.Fermat.'+p+' := by sorry','natural_language_statement':quote+prose([name]),'source':sources[src],'tags':['abc-conjecture','arithmetic-geometry','arithmetic-teichmuller-spaces']})
res=publish('fermat-children','/submit-problem',{'problems':problems,'env':ENV,'private':True});ids={x['theorem_name']:x['theorem_id'] for x in res};save('published-child-ids.json',ids)
en='Choose an integer N>max(3,3(1+epsilon)/epsilon). Then a=(N-3)/N>0 and delta=a(1+epsilon)-1>0. Lift each tripod point to the actual Fermat curve by the degree/discriminant child; apply the canonical estimate at degree N^2*d and error delta; use the fixed projective-height normalization child. Dividing the resulting inequality by a yields Statement I with constant ((1+delta)*C_D+C_F+C_N)/a, chosen before the point. This reduction retains the three Open mathematical children, including the still-to-be-decomposed Belyi, compactness and adjunction chain.\n\n'+sources['composition']
zh='先选自然数 N 大于 3 与 3(1+epsilon)/epsilon 的最大值，使 a=(N-3)/N 为正、delta=a(1+epsilon)-1 为正。利用提升与不同理想估计子定理把每个三支点曲线上的点提升到实际 Fermat 曲线，将规范高度估计用于次数界 N²d 和误差 delta，再用固定射影高度的归一化子定理。所得不等式除以正数 a，即得到命题一，且加法常数在选点之前确定。三个子定理仍开放，其中 Belyi 映射、局部紧性与伴随公式还需继续展开。'
ja='自然数 N を 3 と 3(1+epsilon)/epsilon の最大値より大きく選ぶと、a=(N-3)/N と delta=a(1+epsilon)-1 は正となる。持ち上げと不同の評価により三点を除いた射影直線の各点を実際の Fermat 曲線へ持ち上げ、次数上限 N²d と誤差 delta で標準的高さの評価を適用し、固定した射影的高さの正規化を用いる。得られた不等式を正数 a で割ると命題一となり、加法定数は点に先立って選ばれる。三つの子定理は未証明であり、Belyi 写像、局所コンパクト性、随伴公式に関する連鎖はさらに分解する。'
verify('general-position-to-fermat',PARENT,'Solutions/Sol_TripodStatementI.lean',quote+'**English**\n\n'+en+'\n\n**简体中文**\n\n'+zh+'\n\n**日本語**\n\n'+ja)
for tag,path in [('root-graph-after','/theorems/'+ROOT+'/graph'),('root-frontier-after','/theorems/'+ROOT+'/open-leaves')]:save(tag+'.json',api.request(path))
print('Fermat general-position private platform unit completed.',flush=True)
