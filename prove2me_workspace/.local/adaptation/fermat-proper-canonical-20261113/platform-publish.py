from pathlib import Path
import ast,json,hashlib,importlib.util,urllib.request,urllib.error,uuid,time
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/fermat-proper-canonical-20261113'
s=importlib.util.spec_from_file_location('p2m_api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(s);s.loader.exec_module(api)
ENV='0df444a360eaa60ab8c11dca51a86af692955474';ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5'
PARENT=json.loads((w/'.local/adaptation/fermat-general-position-20261113/published-child-ids.json').read_text())['AbcAdaptation.Tripod.Fermat.canonicalEstimate']
def save(name,data):(b/name).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
protocol=(w/'.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
for node in ast.parse(protocol).body:
 if isinstance(node,ast.FunctionDef) and node.name in ['publish','verify']:exec(compile(ast.Module(body=[node],type_ignores=[]),'<verified-platform-protocol>','exec'),globals())
rb={}
for folder in ['fermat-proper-carrier-v1','fermat-proper-canonical-v1']:
 d=w/'.local/adaptation/readbacks'/folder;rb.update(json.loads((d/'result.json').read_text()))
 for f,sha in json.loads((d/'input-hashes.json').read_text()).items():assert hashlib.sha256((w/f).read_bytes()).hexdigest()==sha,f
pre='AbcAdaptation.Tripod.Fermat.Proper.'
def prose(names):return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+n+'`\n\n'+rb[n][lang] for n in names) for lang,title in [('en','English'),('zh','简体中文'),('ja','日本語')])
quote='> “Moreover, if '+r'$X$, $S$, and $T$ are defined over a number field $F$, then $\phi$'+' may be taken to be defined over '+r'$F$'+'.”\n\n— Shinichi Mochizuki, *Noncritical Belyi Maps*, Theorem 2.5, printed pp.5–6.\n\n'
common='Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position, Propositions 1.4, 1.6, 1.7 and Theorem 2.1, printed pp.11–13; https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf . Shinichi Mochizuki, Noncritical Belyi Maps, Theorem 2.5 and Corollary 3.2, pp.5–8; https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . Independent concrete Fermat adaptation of Belyi 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8, Heights 721496ca4c158e511d25d8ccf6bfe8503eda73c1, and Genl ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf. No Iut/Genl/Heights/Belyi runtime import is used. '
sources={
 'proper':common+'Actual source carriers: Belyi/CurveField/Basic.lean:36,67; Place.lean:184,283,289; Residue.lean:37,76; Point.lean:38; NoncriticalBasic.lean:88–97; NoncriticalBridge.lean:47–54. The full Fermat presentation and its exact N degree over Q(u) are a new explicit specialization; irreducibility and existence remain Open.',
 'divisor':common+'Actual source definitions: Belyi/CurveField/Divisor.lean:44; Riemann.lean:372; Canonical.lean:42–83; CoordRing.lean:28,126; Heights/Curve/DivisorHeight.lean:107–125, TupleHeight.lean and Conductor.lean:104–119. Function heights are computed in Q(f(x)) with explicit degree normalization; divisors have actual valuation coefficients and the conductor uses the full point field. Fermat plane adjunction is an explicit new specialization, not a claim of a verbatim upstream theorem.',
 'local':common+'Source Heights/Curve/Compactness.lean exists_subseq_bounded; Genl/Curves/BelyiDescent.lean:264–282,356–374; refer/iut/Iut/Tripod/GeneralPosition.lean:177–220. The actual local field PadicAlgCl 2 and its spectral norm are supplied by the pinned Mathlib.NumberTheory.Padics.Complex, lines54,67,130. All conjugate embeddings are quantified; one common compact set uses the degree-scaled bound (d+1)*max(c,0).',
 'comparisons':common+'Source Genl/Curves/BelyiDescent.lean:215–237,313–327,395–445; Heights.Curve.divHeight_le_mul, Heights.Different.logDisc_add_cond_le and Heights.Curve.logCondOf_le_divHeight. The canonical divisor is div(du), its true degree N(N-3) remains an explicit child, and its actual polar-presentation height is compared to the fixed projective Fermat height. The strict divisor-degree inequality is preserved.',
 'composition':common+'Source numerical contradiction Genl/GeneralPosition/TheoremTwoOne.lean:59–126. Apply local compactness to the entire bounded-degree failure sequence, choose a genuine noncritical Belyi map and actual divisor/coordinate-ring data, and use delta=epsilon/(1+q*(1+epsilon)) for a strict q above the actual cusp/canonical degree ratio. Strictly increasing subsequence indices preserve unbounded failure. This is a conditional combination of exactly twenty Open children.'
}
# The exact upload text has separately passed scheduled validation and elaborated-type comparison.
validation=json.loads((b/'upload-validation.json').read_text());assert validation['passed'] and validation['elaborated_types_equal']
for receipt in ['closed-compositions-review-result.json','canonical-solution-leaf-result.json','canonical-solution-artifact-result.json','canonical-reduction-axioms-result.json']:
 d=json.loads((b/receipt).read_text());assert d['status']=='succeeded' and d['result']['exit_code']==0,receipt
 if 'review' in receipt:assert d['result']['review']['passed']
defs=[
 ('FermatProperCarrier',[pre+n for n in ['Ω','Model','Model.trdeg_eq_one','Place','Place.ResidueField','Place.residue','Place.ratHom','Place.degree','QbarPoint','QbarPoint.eval','QbarPoint.fieldOf','QbarPoint.degree','QbarPoint.eval_mem_fieldOf','PlacesDiscrete','ResiduesFinite','ord','cusps','ramIdx','IsBelyi','Divisor','divisorDegree','cuspDivisor','planeCanonicalDegree','StrictQ','AffinePoint','AffineIdentification','NoncriticalSelection','NoncriticalInput']],'proper'),
 ('FermatProperComposition',[pre+'noncriticalInput_of_children'],'proper'),
 ('FermatProperDivisorHeight',[pre+n for n in ['poleMultiplicity','PolarPresentation','functionHeight','functionHeight_of_regular','functionHeight_of_pole','functionHeight_of_eval_zero','divHeight','cuspHeight','CanonicalDivisorData','InfinityDivisorData','PlaneAdjunctionData','coordRing','CuspGenerators','pointField_finiteDimensional','evalInPointField','logCondOf','pointLogDiff','ArithmeticDivisorChoices']],'divisor'),
 ('FermatProperDivisorComposition',[pre+'arithmeticDivisorChoices_of_children'],'divisor'),
 ('FermatLocalBelyi',[pre+n for n in ['affineLift','affineLift_field_eq','affineLift_degree_eq','evalInField','GoodValue','belyiImage','belyiImage_eq','belyiImage_field_le','belyiImage_degree_le','LocalBounds','LocalCompactness','AvoidanceRegularity','localCompactSet','EmbeddingBoundsToSet','BoundedBelyiImages']],'local'),
 ('FermatLocalBelyiComposition',[pre+'boundedBelyiImages_of_children'],'local'),
 ('FermatBelyiComparisons',[pre+n for n in ['CanonicalDegreeIdentity','CanonicalHeightIdentification','BelyiHeightRelation','DivisorDegreeHeightComparison','BelyiDifferentConductorComparison','CuspConductorHeightComparison']],'comparisons'),
 ('FermatCanonicalBelyiComposition',[pre+'canonicalEstimate_of_belyi_children'],'composition')]
for name,names,src in defs:
 f='Definitions/Def_'+name+'.lean';code=(w/f).read_text();assert hashlib.sha256(code.encode()).hexdigest()==validation['definition_hashes'][f]
 publish('def-'+name,'/submit-definition',{'definition_name':name,'definition_title':name+' — concrete Fermat arithmetic data','definition':code,'natural_language_statement':quote+prose(names),'source':sources[src],'env':ENV,'private':True,'tags':['abc-conjecture','arithmetic-geometry','arithmetic-teichmuller-spaces']})
titles={
 'modelExists':'Existence of the full Fermat function-field presentation','placesDiscrete':'Discreteness of every proper Fermat place','residuesFinite':'Finite residue fields at all proper Fermat places','affineIdentification':'Actual affine Fermat points and their residue fields','noncriticalSelection':'Noncritical Belyi maps avoiding finitely many places','cuspsFinite':'Finite cusp support of a genuine Belyi function','polarPresentationExists':'Polar presentations of actual Fermat divisors','canonicalDivisorExists':'The actual canonical divisor of du','infinityDivisorExists':'The hyperplane divisor of the projective Fermat model','planeAdjunctionExists':'Adjunction for the full Fermat plane curve','cuspGeneratorsExists':'Actual affine generators for the Belyi cusp complement','canonicalDivisorDegree':'Canonical degree N(N−3) of the Fermat curve','localCompactness':'One subsequence controlling every local conjugate','avoidanceRegularity':'Regularity of the tripod functions away from Belyi cusps','embeddingBoundsToSet':'Conjugate norm bounds give a common compactly bounded set','canonicalHeightIdentification':'Actual canonical divisor height versus the fixed Fermat height','belyiHeightRelation':'Canonical plus cusp height along an actual Belyi map','divisorDegreeHeightComparison':'Height comparison at a strict divisor-degree ratio','belyiDifferentConductorComparison':'Discriminant and conductor along actual point-field towers','cuspConductorHeightComparison':'Actual cusp conductor bounded by its divisor height'}
items=json.loads((b/'upload-problem-items.json').read_text());assert len(items)==20
for item in items:
 n=item['theorem_name'].removeprefix(pre);assert n in titles
 group='proper' if n in ['modelExists','placesDiscrete','residuesFinite','affineIdentification','noncriticalSelection','cuspsFinite'] else 'divisor' if n in ['polarPresentationExists','canonicalDivisorExists','infinityDivisorExists','planeAdjunctionExists','cuspGeneratorsExists','canonicalDivisorDegree'] else 'local' if n in ['localCompactness','avoidanceRegularity','embeddingBoundsToSet'] else 'comparisons'
 item.update(theorem_title=titles[n],natural_language_statement=quote+prose([pre+n]),source=sources[group],tags=['abc-conjecture','arithmetic-geometry','arithmetic-teichmuller-spaces'])
results=publish('proper-canonical-children','/submit-problem',{'problems':items,'env':ENV,'private':True});ids={x['theorem_name']:x['theorem_id'] for x in results};save('published-child-ids.json',ids)
explanation=quote+'**English**\n\n'+rb['solution']['en']+'\n\n'+sources['composition']+'\n\n**简体中文**\n\n'+rb['solution']['zh']+'\n\n这些子定理仍为开放节点；本次提交建立精确归约。\n\n**日本語**\n\n'+rb['solution']['ja']+'\n\n子定理は未証明であり、本提出は明示的な帰着を構成する。'
verify('canonical-estimate-to-actual-belyi',PARENT,'Solutions/Sol_FermatCanonicalEstimate.lean',explanation)
save('root-graph-after.json',api.request('/theorems/'+ROOT+'/graph?depth=10'))
save('canonical-parent-graph-after.json',api.request('/theorems/'+PARENT+'/graph?depth=3'))
leaves=[];offset=0
while True:
 page=api.request('/theorems/'+ROOT+'/open-leaves?limit=50&offset='+str(offset));save('root-frontier-page-'+str(offset)+'.json',page)
 leaves.extend(page['open_leaves']);offset+=len(page['open_leaves'])
 if offset>=page['total']:break
 assert page['open_leaves'],'Unexpected empty frontier page before total'
assert len({x['theorem_id'] for x in leaves})==len(leaves)
save('root-frontier-after.json',{'root_id':ROOT,'open_leaves':leaves,'total':page['total'],'all_pages_fetched':True})
print('Proper Fermat canonical estimate private reduction completed.',flush=True)
