#!/usr/bin/env python3
"""Bind the narrow audit-only helper resolution. Writes only this draft directory."""
from pathlib import Path
import argparse,copy,hashlib,json
HERE=Path(__file__).resolve().parent
DEFAULT=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-packet-field-carriers-20261115')
ELIDED=['Iut.solvableClosure._proof_2','Iut.solvableClosure._proof_4']
RENAMED='Iut.solvableClosure._proof_3'
TARGET='AbcAdaptation.Reference.Iut.solvableClosure._proof_2'
def load(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def name(n):
 out=[]
 for part in n.split('.'):out=[out,'str',part]
 return out
def dump(p,j):Path(p).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--unit',type=Path,default=DEFAULT);ap.add_argument('--output',type=Path,default=HERE/'audit-config.json');a=ap.parse_args();unit=a.unit.resolve();out=a.output.resolve();assert out.parent==HERE,'Output must stay in the unique draft directory'
 basepath=unit/'audit-config.json';base=load(basepath);sourcepath=Path(base['originalExprFile']);source=load(sourcepath);records={r['name']:r for r in source['records']};assert len(records)==196 and source['recordCount']==196 and source['selectedCount']==sum(r['selected'] for r in records.values())==133
 acceptpath=unit/'original-exprs-acceptance.json';accept=load(acceptpath);assert accept['status']=='accepted' and accept['job_id']=='ci-013498-336a3a9a' and sha(sourcepath)==accept['originalExprsSha256'];assert source['inventorySha256']==base['inventorySha256']==accept['inventorySha256'] and source['graphSha256']==base['graphSha256']
 factpath=unit/'platform-globalfield-facts.json';facts=load(factpath);receiptpath=unit/'platform-globalfield-query-result.json';receipt=load(receiptpath);assert receipt['job_id']=='ci-013599-61a18ec4' and receipt['status']=='succeeded' and receipt['result']['exit_code']==0;assert facts['recordCount']==len(facts['records'])==29 and facts['compilerVersion']=='4.33.1';actual={r['name']:r for r in facts['records']};assert actual[TARGET]['constantKind']=='theorem' and actual[TARGET]['isProposition'] and not actual[TARGET]['isInstance']
 parserpath=unit/'parser-output/Iut-Cor312-ThetaData-GlobalField.jsonl';parser=[json.loads(l) for l in parserpath.read_text().splitlines()];parserdecl={f['name']:f for f in parser if f.get('kind')=='compilerDecl'}
 reportpath=unit/'generated/foundation-small-source-report.json';report=load(reportpath);m=next(m for m in report['modules'] if m['module']=='Iut.Cor312.ThetaData.GlobalField');cmd=next(c for c in m['retainedCommands'] if c['commandIndex']==18);original=Path(m['originalCoordinateSource']);retained=Path(m['source']);r=cmd['originalRange'];q=cmd['outputRange'];ob=original.read_bytes()[r['start']['offset']:r['end']['offset']];rb=retained.read_bytes()[q['start']['offset']:q['end']['offset']];assert ob==rb and hashlib.sha256(ob).hexdigest()==cmd['sha256'];assert parserdecl['Iut.solvableClosure']['compilerRange']==r
 oldmaps={r['original']:r for r in base['projectMap']};assert len(oldmaps)==347
 for n in ELIDED+[RENAMED]:
  d=records[n];p=parserdecl[n];assert d['constantKind']=='theorem' and d['isProposition'] and not d['isInstance'] and d['selected'] and d['valueExpr'] is not None;assert p['compilerRange'] is None and not p['containingCommandIndices'] and not p['sourceRootCandidate'] and p['selected'];assert set(d['axioms'])<= {'propext','Classical.choice','Quot.sound'}
 config=copy.deepcopy(base);config['projectMap']=[row for row in config['projectMap'] if row['original'] not in ELIDED]
 for row in config['projectMap']:
  if row['original']==RENAMED:row['target']=TARGET;row['targetName']=name(TARGET);row['resolutionRole']='approved-internal-proof-rename';row['resolutionEvidenceJob']='ci-013599-61a18ec4'
 assert len(config['projectMap'])==len({r['original'] for r in config['projectMap']})==len({r['target'] for r in config['projectMap']})==345
 proofrows=[]
 for n in ELIDED:
  proofrows.append({'original':n,'originalName':name(n),'standaloneTargetIdentity':None,'expectedOriginalRecord':records[n],'expectedIsInstance':oldmaps[n]['expectedIsInstance'],'expectedSourceAxioms':oldmaps[n]['expectedSourceAxioms'],'parserFact':parserdecl[n],'parentOriginalName':name('Iut.solvableClosure'),'parentCommandIndex':18,'parentCommandSha256':cmd['sha256'],'recordValueAuthority':'accepted original compiler Expr; no handwritten auxiliary'})
 config['internalProofElisions']=proofrows
 config['internalProofRenames']=[{'originalName':name(RENAMED),'targetName':name(TARGET),'expectedOriginalRecord':records[RENAMED],'expectedIsInstance':oldmaps[RENAMED]['expectedIsInstance'],'expectedSourceAxioms':oldmaps[RENAMED]['expectedSourceAxioms'],'parserFact':parserdecl[RENAMED]}]
 config['expectedNamedSelectedCount']=131;config['expectedElidedProofCount']=2;config['expectedNamedMappingCount']=345;config['originalCandidateCountIncludingElisions']=347
 evidencepaths=[basepath,sourcepath,acceptpath,factpath,receiptpath,parserpath,reportpath,original,retained]
 definition=unit.parent.parent.parent/'Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField.lean'
 # The actual artifact source lives at the project root's Definitions directory.
 definition=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField.lean');evidencepaths.append(definition)
 config['internalProofEvidence']={'originalAcceptanceFile':str(acceptpath),'originalExprsSha256':sha(sourcepath),'platformQueryReceipt':str(receiptpath),'platformFactsFile':str(factpath),'parserFactsFile':str(parserpath),'originalCoordinateSource':str(original),'retainedSmallSource':str(retained),'originalCommandStart':r['start']['offset'],'originalCommandEnd':r['end']['offset'],'retainedCommandStart':q['start']['offset'],'retainedCommandEnd':q['end']['offset'],'parentCommandSha256':cmd['sha256'],'files':[{'path':str(p),'sha256':sha(p)} for p in evidencepaths]}
 config['internalProofAccountingPolicy']='133 selected original obligations =131 mandatory named comparisons +2 mandatory genuine-original-proof resolutions, each covered by full solvableClosure owner value equivalence'
 dump(out,config)
 dump(HERE/'config-preparation.json',{'schema':'next-carrier-helper-config-preparation-v1','status':'prepared-not-compiled','baseConfig':str(basepath),'baseConfigSha256':sha(basepath),'output':str(out),'outputSha256':sha(out),'sourceSelected':133,'namedRequired':131,'elidedProofRequired':2,'namedRelocations':345,'originalCandidatesIncludingElisions':347,'evidence':config['internalProofEvidence']})
 print(json.dumps({'config':str(out),'sha256':sha(out),'namedRelocations':345,'namedRequired':131,'proofResolutions':2},indent=2))
if __name__=='__main__':main()
