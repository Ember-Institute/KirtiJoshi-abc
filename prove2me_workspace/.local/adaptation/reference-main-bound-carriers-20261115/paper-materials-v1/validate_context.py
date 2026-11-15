#!/usr/bin/env python3
"""Offline byte/coverage validation. It does not certify mathematical fidelity."""
from pathlib import Path
import json, hashlib, re
OUT=Path(__file__).resolve().parent
P=OUT/'paper-context.json'
d=json.loads(P.read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(cond,message):
 if not cond:raise AssertionError(message)
checks=[]
def record(name,fun):fun();checks.append(dict(check=name,passed=True))
S=Path(d['parser_selection_evidence']['path'])
sel=json.loads(S.read_text())
commands={c['rootOriginalName']:c for c in sel['commands']}
expected_counts=[5,3,2,13,4]
expected_fields={
 'Iut.QPilotData':['badFinset','badFinset_spec','weight','weight_pos'],
 'Iut.RHSData':['container','proc_standard','toRational_finite','toRational_infinite','vol','hull','thetaPilot','thetaPilot_hullAdmissible','thetaPilot_le_shell'],
 'Iut.Corollary312VariantData':['data','qPilot','rhsData'],
 'Iut.PrimeCountingBound':['η','one_lt_η','bound'],
 'Iut.Theorem110Invariants':['emod','one_le_emod','emod_le_dmod','logDtpd','logDtpd_nonneg','logFtpd','logFtpd_nonneg','dst','dst_prime','logDK','logDK_nonneg','logDK_eq_zero'],
 'Iut.Theorem110Certificate':['seven_le','bad_mem_dst','step_ii','step_iii'],
 'Iut.Theorem110Invariants.LocalEstimate':['cont','cont_mem_hullRegions','thetaPilot_subset','cont_eq_integral','vol_finite','vol_infinite','packetVol_mono']}
quotes={q['id']:q for q in d['quotations']}
check(len(quotes)==18,'18 distinct quotations')
check(len(d['bundles'])==5,'5 bundles')
check([len(b['selected_source_commands']) for b in d['bundles']]==expected_counts,'5/3/2/13/4 commands')
seen=[];fields={}
for b in d['bundles']:
 check(sha(b['source_path'])==b['source_sha256'],'frozen source hash')
 raw=Path(b['source_path']).read_bytes()
 check(b['source_sha256']==b['source_provenance']['effectiveSourceSha256'],'actual effective source')
 for key in ['upstreamSource','effectiveSource']:
  check(sha(b['source_provenance'][key])==b['source_provenance'][key+'Sha256'],'source provenance hash')
 delta=b['source_provenance']['exactSourceDelta'];check(sha(delta['path'])==delta['sha256'],'exact override delta')
 check(b['selected_source_commands']==[c['name'] for c in b['selected_command_bindings']],'bundle command ordering')
 for c in b['selected_command_bindings']:
  name=c['name'];seen.append(name);original=commands[name];r=c['actual_parser_range']
  check(r==original['actualParserRange'],'parser range unchanged')
  sl=raw[r['start']['offset']:r['end']['offset']]
  check(sl.decode()==c['source_text'],'whole source command copied')
  check(len(sl)==c['source_byte_length']==original['wholeCommandByteLength'],'byte length')
  check(hashlib.sha256(sl).hexdigest()==c['source_text_sha256']==original['wholeCommandSha256'],'command hash')
  check(c['actual_consumers']==original['actualConsumers'],'actual consumers copied')
  check(c['source_name_expr']==original['rootActualSourceNameExpr'],'actual source Name preserved')
  check(c['selected_compiler_declarations']==original['selectedRangedDeclarations'],'selected ranged declarations copied')
  check(set(c['quotation_ids'])<=quotes.keys(),'command citation exists')
  if 'complete_structure_fields' in c:fields[name]=c['complete_structure_fields']
 check(set(b['quotation_ids'])<=quotes.keys(),'bundle citation exists')
check(len(seen)==27 and len(set(seen))==27 and set(seen)==set(commands),'exact 27 commands')
check(fields==expected_fields,'all fields of 7 complete structure commands retained')
checks.append(dict(check='five_bundles_27_complete_commands_ranges_hashes_all_structure_fields_and_consumers',passed=True))
for e in d['input_evidence']:check(sha(e['path'])==e['sha256'],'frozen metadata input hash '+e['path'])
checks.append(dict(check='all_input_metadata_hashes_current',passed=True))
visual=set(d['evidence_policy']['new_original_pages_visually_checked'])
for ident,p in d['paper_sources'].items():
 check(p['author']=='Shinichi Mochizuki','only original Mochizuki sources')
 check(sha(p['local_pdf'])==p['sha256'],'paper PDF bytes')
 for key in ['page_image','raw_text']:
  e=p['version_evidence'];check(sha(e[key+'_path'])==e[key+'_sha256'],'version evidence')
for q in d['quotations']:
 check(q['paper_id'] in d['paper_sources'],'paper reference')
 check(q['printed_pages']==q['file_pages'],'observed printed/file page alignment')
 check(bool(q['quote_markdown'].strip()) and bool(q['locator']),'nonempty quote and locator')
 for e in q['evidence']:
  check(f"{e['paper_id']}-{e['file_page']:03}" in visual,'visually checked evidence page')
  for key in ['page_image','raw_text']:check(sha(e[key+'_path'])==e[key+'_sha256'],'quote evidence bytes')
checks.append(dict(check='18_original_quotations_page_render_raw_extract_and_PDF_hashes',passed=True))
check(len(d['normalization_distinctions'])==9,'nine separate normalization distinctions')
check('3/2' in d['bundles'][3]['implementation_scope_en'] and '4/3' in d['bundles'][3]['implementation_scope_en'],'prime factor difference retained')
check('No selected theorem identifies' in next(c for b in d['bundles'] for c in b['selected_command_bindings'] if c['name']=='Iut.Corollary312VariantData.logQAt')['paper_relation_en'],'fiber bridge not claimed')
checks.append(dict(check='normalization_and_open_bridge_scope_preserved',passed=True))
result=dict(status='passed',checks=checks,bundle_count=5,source_command_count=27,quotation_count=18,structure_count=7,verification_scope='Offline byte, coverage, provenance, and evidence-link checks only. The writer manually checked quotations against PDF renders. This script is not independent readback, compilation, a mathematical proof, or a new acceptance receipt.')
d['validation']=result
P.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
(OUT/'paper-context-validation.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result,ensure_ascii=False,indent=2))
