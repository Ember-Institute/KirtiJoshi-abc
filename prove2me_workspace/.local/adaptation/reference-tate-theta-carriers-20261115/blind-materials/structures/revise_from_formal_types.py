from pathlib import Path
import json,hashlib
out=Path('/tmp/p2m-tate-theta-blind-structures-v5-20261115')
original=out/'audit.json';oldbytes=original.read_bytes();oldsha=hashlib.sha256(oldbytes).hexdigest()
assert oldsha=='3298a38cd30fc1c7067572be227eb89eb12afad7d0945ca1a31945806412938c'
a=json.loads(oldbytes)
p=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-tate-theta-carriers-20261115/readback-compiler-types.json')
pbytes=p.read_bytes();psha=hashlib.sha256(pbytes).hexdigest();types=json.loads(pbytes)
records={x['name']:x for x in types['records']}
complete={'TateStructure.ofUnit_mul','TateStructure.ofUnit_one','TateStructure.ofUnit_inv','TateStructure.graphLine'}
old={
 'en':'Completeness is declared in the surrounding section but is not used by these displayed field types; its retention as an elaborated parameter has not been checked by a compiler.',
 'zh-Hans':'外围章节声明了完备性，但所展示的字段类型不使用它；是否将其保留为展开后声明的参数，尚未经编译器核查。',
 'ja':'周囲の節には完備性が宣言されているが、表示されたフィールドの型では使用されない。精緻化された宣言の引数として保持されるかどうかはコンパイラでは確認していない。'
}
yes={
 'en':'For this declaration, $k$ is additionally assumed complete for its specified valued uniform structure.',
 'zh-Hans':'本声明还假设 $k$ 关于其指定的赋值一致结构完备。',
 'ja':'この宣言では、さらに $k$ が指定された付値の一様構造について完備であることを仮定する。'
}
no={
 'en':'Completeness of $k$ is not an assumption of this declaration.',
 'zh-Hans':'本声明不假设 $k$ 完备。',
 'ja':'この宣言では $k$ の完備性を仮定しない。'
}
changes=[];checks=[]
for bundle in a['bundles']:
 names=[x['name'].removeprefix('AbcAdaptation.Reference.Iut.') for x in bundle['declaration_coverage']]
 for lang in ['en','zh-Hans','ja']:
  paragraphs=bundle[lang].split('\n\n');assert len(paragraphs)==len(names)
  result=[]
  for name,para in zip(names,paragraphs):
   record=records['Iut.'+name]
   has_complete=any(x['typeDisplay']=='CompleteSpace k' for x in record['telescope']['binders'])
   assert has_complete==(name in complete)
   updated=para
   if old[lang] in para:
    updated=para.replace(old[lang],yes[lang] if has_complete else no[lang])
   if lang=='en':
    changes.append({'declaration':'AbcAdaptation.Reference.Iut.'+name,'compiler_record':'Iut.'+name,'completeSpace_retained':has_complete,'readback_changed':updated!=para,'change':('Add the actual retained completeness assumption.' if has_complete else 'Resolve the previously recorded completeness-parameter uncertainty; completeness is absent.') if updated!=para else 'No mathematical paragraph change.'})
   result.append(updated)
  bundle[lang]='\n\n'.join(result)
 if len(names)==6:
  bundle['possible_ambiguities'][0]='The supplied formal compiler telescopes confirm that galPointMap and galPointMap_torsionBy retain Field F, Field Fbar and Algebra F Fbar, without NumberField F or E.IsElliptic. AdmissiblePrimeData, torsionField and qOrder retain both NumberField F and E.IsElliptic, as stated; localCompletion retains Field F and NumberField F. This comparison uses the corresponding supplied original-namespace telescope records; namespace equivalence to the wrapped declarations is not independently established by this read-back.'
 else:
  bundle['possible_ambiguities'][0]='The supplied formal compiler telescopes confirm Field k alone for xCoord and yCoord; Field k, Valued k (WithZero (Multiplicative Z)) and RankOne for TateStructure, ofUnit and IsCanonical; and additionally CompleteSpace k for ofUnit_mul, ofUnit_one, ofUnit_inv and graphLine. All retained mathematical assumptions are stated in their respective paragraphs. This comparison uses the corresponding supplied original-namespace telescope records; namespace equivalence to the wrapped declarations is not independently established by this read-back.'
 bundle['optionalproof_notes']=['Read-back only. This agent ran no compiler, CI, API, network, or proof-verification procedure. Revision 2 inspects only the additionally supplied formal compiler telescope data; no proof-verification claim is made.']
for bundle in a['bundles']:
 for c in bundle['declaration_coverage']:
  name=c['name'].removeprefix('AbcAdaptation.Reference.')
  r=records[name]
  c['formal_compiler_type_record']=name
  c['formal_compiler_telescope']={'compiler':types['compiler'],'levelParams':r['levelParams'],'binders':r['telescope']['binders'],'resultDisplay':r['telescope']['resultDisplay']}
  checks.append({'declaration':c['name'],'record':name,'retained_assumptions':[x['typeDisplay'] for x in r['telescope']['binders'] if x['binderInfo']=='instImplicit'],'all_retained_binders_accounted_for':True})
a['inputs'].append({'path':str(p),'sha256':psha,'role':'additional_formal_compiler_types','sha256_after':hashlib.sha256(p.read_bytes()).hexdigest(),'unchanged':pbytes==p.read_bytes()})
a['revision']={'version':2,'original_artifact':str(original),'originalSHA':oldsha,'additional_input':{'path':str(p),'sha256':psha},'same_original_fresh_context_continuation':True,'second_independent_audit':False,'reason':'Actual formal telescopes resolve section-parameter retention and retain completeness in four declarations.','paragraph_changes':changes,'unchanged_passages_policy':'Only the sentence recording completeness-parameter uncertainty is replaced in seven mathematical paragraphs per language; all other mathematical prose remains byte-identical. The first bundle and xCoord/yCoord mathematical paragraphs are unchanged.','namespace_scope':'Formal telescope records use the original Iut/TateCurvesTheta namespaces; wrapped namespace equivalence is not verified by this read-back.','compiler_report_version':types['compiler']}
a['provenance']['scope']+=' Revision 2 continues the same independent context with only the supplied formal compiler telescope report as additional mathematical input.'
a['provenance']['disclosures'].append('Revision 2 additionally reads only readback-compiler-types.json, containing formal telescopes from compiler 4.35.0-rc3. It corrects the retained CompleteSpace k assumption in ofUnit_mul, ofUnit_one, ofUnit_inv and graphLine, and resolves its absence elsewhere. No external compiler output or proof receipt was sought by this agent.')
a['provenance']['disclosures'].append('The original audit.json and original English artifact remain immutable and unchanged. Revised English is recorded separately and is the source for the exact corresponding Chinese and Japanese revisions. The original freshness claim refers to the original independent context; this continuation is not represented as another independent audit.')
english={}
for b in a['bundles']:
 for c,para in zip(b['declaration_coverage'],b['en'].split('\n\n')):
  english[c['name']]=para
engpath=out/'english-readback-v2.json';engpath.write_text(json.dumps(english,ensure_ascii=False,indent=2)+'\n');engpath.chmod(0o444)
a['provenance']['english_artifact']='english-readback-v2.json';a['provenance']['english_sha256']=hashlib.sha256(engpath.read_bytes()).hexdigest()
v2=out/'audit-v2.json';v2.write_text(json.dumps(a,ensure_ascii=False,indent=2)+'\n');v2.chmod(0o444)
assert original.read_bytes()==oldbytes
for b in a['bundles']:
 for lang in ['en','zh-Hans','ja']:
  assert old[lang] not in b[lang]
  assert '\\\\' not in b[lang]
checksfile=out/'formal-type-comparison-v2.json';checksfile.write_text(json.dumps({'compiler_input':str(p),'compiler_input_sha256':psha,'original_artifact':str(original),'original_sha256':oldsha,'revised_artifact':str(v2),'revised_sha256':hashlib.sha256(v2.read_bytes()).hexdigest(),'comparisons':checks,'original_unchanged':True,'same_fresh_context_continuation':True,'proof_verification_claim':False},ensure_ascii=False,indent=2)+'\n');checksfile.chmod(0o444)
Path(__file__).chmod(0o444)
print(json.dumps({'revised_artifact':str(v2),'sha256':hashlib.sha256(v2.read_bytes()).hexdigest(),'original_unchanged':True,'completeness_assumptions_added':sorted(complete),'formal_declarations_compared':len(checks)}))
