"""Offline preparation shim for six numeric candidates. No API on import/prepare.

Network, request journal, idempotency, private mission checks, GET readbacks,
proof ACCEPTED polling, and exact root graph preservation are the old delivery.
The main agent must provide explicit ready evidence before invoking deliver().
"""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
import importlib.util
import copy
import json

WORKSPACE = Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
UNIT = WORKSPACE/'.local/adaptation/main-c22-numeric-helpers-20261115'
OLD = WORKSPACE/'.local/adaptation/main-c22-numeric-reference-split-20261115/delivery.py'
PAPER = WORKSPACE/'.local/adaptation/reference-main-bound-carriers-20261115/paper-materials-v1'
spec = importlib.util.spec_from_file_location('numeric_delivery_previous', OLD)
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, sha, save = old.read, old.sha, old.save
ALL_SHORTS = ['log_bound_ell','log_le_four_mul_sqrt_sqrt','log_le_half_of_pos',
              'log_le_self_of_pos','log_pi_le_two','log_pi_nonneg','sum_affine_quadratic']
ALL_NAMES = ['AbcAdaptation.Reference.Iut.'+n for n in ALL_SHORTS]
INLINE = 'AbcAdaptation.Reference.Iut.log_pi_nonneg'
NAMES = [n for n in ALL_NAMES if n != INLINE]
old.UNIT, old.NAMES = UNIT, NAMES
old.ORIGINALS = [n.removeprefix('AbcAdaptation.Reference.') for n in NAMES]
old.GATES |= {'all_seven_kernel_audits','all_fourteen_leaf_and_artifact_pairs',
              'production_gates_reused_unchanged','original_proof_identity',
              'original_readback_metadata_bound'}
BASE_PREFLIGHT = old.preflight

def bind(files, path):
    path = Path(path)
    files[str(path)] = sha(path)
    return read(path)

def readbacks_bound(metadata):
    summary = bind(metadata, UNIT/'blind-readbacks.json')
    assert sha(UNIT/'blind-readbacks.json') == '8c19db0d1f03364b345b6825587635bc7ea9523c9f6a8a42412994cb7104f094'
    assert summary['status'] == 'all-seven-code-only-readbacks-bound'
    rows = {r['declaration']:r for r in summary['nodes']}
    assert set(rows) == set(ALL_NAMES)
    for review in summary['independent_reviews']:
        for entry in [review['metadata'], *review['unmodified_originals']]:
            assert sha(entry['path']) == entry['sha256']
            bind(metadata, entry['path']) if Path(entry['path']).suffix == '.json' else metadata.update({entry['path']:entry['sha256']})
    for name,row in rows.items():
        provenance=row['provenance']
        assert provenance['actual_backend'] is None
        assert provenance['fresh_context'] and provenance['input_only_formal_code']
        for key in ['original_readbacks','metadata']:
            entry=provenance[key]
            assert sha(entry['path']) == entry['sha256']
            metadata[entry['path']]=entry['sha256']
        blind=UNIT/'blind-formal-code'/row['file']
        assert row['source_sha256'] == sha(blind)
        metadata[str(blind)]=sha(blind)
        full=(WORKSPACE/old.relative_source('Theorems',name)).read_bytes()
        formal=blind.read_bytes()
        # The original blind input omits only these two recorded leading comments.
        notice=(b'/-\nCopyright (c) 2026 The iut contributors. All rights reserved.\n'
                b'Released under Apache 2.0 license as described in the file LICENSE.\n'
                b'Authors: The iut contributors\n-/\n'
                b'/- Adaptation draft: exact original declaration retained; imports and surrounding\n'
                b'context reduced to numerical inputs. Compiler semantic identity is pending. -/\n')
        assert full==notice+formal,('Blind formal input differs beyond leading notices',name)
    return rows

def target_evidence(metadata):
    acceptance=bind(metadata, UNIT/'target-acceptance.json')
    assert acceptance['status']=='all-seven-exact-source-target-solution-kernel-and-standard-axioms-passed'
    assert set(acceptance['names']) == {'Iut.'+n for n in ALL_SHORTS}
    receipts=acceptance['receipts']
    assert len(receipts)==35
    for name in acceptance['names']:
        assert {r['kind']for r in receipts if r['name']==name} == {
            'theorem-leaf','theorem-artifact','solution-leaf','solution-artifact','audit'}
    for entry in receipts:
        assert sha(entry['path']) == entry['sha256']
        receipt=bind(metadata,entry['path'])
        assert receipt['job_id']==entry['job_id'] and receipt['status']=='succeeded'
        assert receipt['result']['exit_code']==0
        rss=receipt['resources']['peak_rss_bytes']
        assert rss is not None and rss<=16*1024**3
    for short in ALL_SHORTS:
        audit=bind(metadata,UNIT/'type-audits'/('Iut-'+short+'.json'))
        for flag in ['signatureBinderInfoPreserved','allExpressionBinderInfoEqual',
                     'kernelTargetSolutionTypeEqual','kernelOriginalTargetTypeEqual',
                     'kernelOriginalSolutionTypeEqual','solutionClosureStandardAxiomsOnly']:
            assert audit[flag] is True
        assert not audit['solutionHasTransitiveSorryAx'] and not audit['solutionBodyDirectSorryAx']
        assert set(audit['solutionAxioms']) <= {'propext','Classical.choice','Quot.sound'}
        assert audit['standardConstantRelocations']==audit['projectConstantRelocations']==[]
    return acceptance

def prepare(output, names=None):
    """Offline packet and ready=false template. names may select a subset of six."""
    names=list(NAMES if names is None else names)
    assert names and len(set(names))==len(names) and set(names)<=set(NAMES)
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    metadata={str(OLD):sha(OLD),str(Path(__file__).resolve()):sha(__file__)}
    generation=bind(metadata,UNIT/'generated-target/generation-manifest.json')
    ledger=bind(metadata,UNIT/'generated-target/SOURCE_LEDGER.json')
    original=bind(metadata,UNIT/'source-facts/original-exprs.json')
    original_acceptance=bind(metadata,UNIT/'source-facts-acceptance.json')
    original_ci=bind(metadata,UNIT/'original-seven-facts-result.json')
    assert original_acceptance['sourceExprSha256']==sha(UNIT/'source-facts/original-exprs.json')
    assert original_acceptance['originalJob']==original_ci['job_id']=='ci-015163-070e492c'
    assert original_ci['status']=='succeeded' and original_ci['result']['exit_code']==0
    manifest=bind(metadata,UNIT/'manifest.json')
    records={r['name']:r for r in original['records']}
    assert set(records)=={'Iut.'+s for s in ALL_SHORTS}
    for node in generation['nodes']:
        source_entry,=[r for r in manifest['entries'] if r['wrappedName']==node['theoremName']]
        assert node['actualSourceRecord']==records[node['originalName']]
        for item in [source_entry['effectiveSource']['coordinateSource'],source_entry['effectiveSource']['path'],source_entry['originalSource']['path']]:
            metadata[item]=sha(item)
        data=Path(source_entry['effectiveSource']['coordinateSource']).read_bytes()
        assert __import__('hashlib').sha256(data).hexdigest()==records[node['originalName']]['sourceSha256']
        pr=source_entry['effectiveSource']['proofRange'];a,b=pr['start']['offset'],pr['end']['offset']
        assert __import__('hashlib').sha256(data[a:b]).hexdigest()==node['originalProofSha256']
        sa,sb=node['generatedSolutionProofByteOffsets']
        solution=WORKSPACE/old.relative_source('Solutions',node['theoremName'])
        assert solution.read_bytes()[sa:sb]==data[a:b]
    acceptance=target_evidence(metadata)
    rb=readbacks_bound(metadata)
    paper=bind(metadata,PAPER/'quotations-and-evidence.json')
    bind(metadata,PAPER/'paper-context.json')
    bind(metadata,PAPER/'paper-context-validation.json')
    assert len(paper['quotations'])==18
    quotes={q['id']:q for q in paper['quotations']}
    publications=[];verification=[];sources={};explanations={}
    for name in names:
        original_name=name.removeprefix('AbcAdaptation.Reference.')
        node,=[r for r in generation['nodes'] if r['theoremName']==name]
        source_entry,=[r for r in manifest['entries'] if r['wrappedName']==name]
        ledger_entry,=[r for r in ledger['entries'] if r['producer']==name]
        assert ledger_entry['actualOriginalConsumers'] and ledger_entry['canonicalConsumerConnected'] is False
        raw=bind(metadata,UNIT/'generated-target/payloads'/(name.replace('.','_')+'.json'))
        assert raw['theorem_name']==name
        theorem,solution=[old.relative_source(k,name)for k in ['Theorems','Solutions']]
        assert (WORKSPACE/theorem).read_bytes()==(raw['preamble']+raw['formal_statement']+'\n').encode()
        assert (WORKSPACE/solution).read_bytes()==raw['solution'].encode()
        assert node['actualSourceRecord']==records[original_name]
        source_data=Path(source_entry['effectiveSource']['coordinateSource']).read_bytes()
        assert __import__('hashlib').sha256(source_data).hexdigest()==records[original_name]['sourceSha256']
        pr=source_entry['effectiveSource']['proofRange'];a,b=pr['start']['offset'],pr['end']['offset']
        proof=source_data[a:b]
        assert __import__('hashlib').sha256(proof).hexdigest()==node['originalProofSha256']
        sa,sb=node['generatedSolutionProofByteOffsets']
        assert (WORKSPACE/solution).read_bytes()[sa:sb]==proof
        for item in [source_entry['effectiveSource']['coordinateSource'],source_entry['effectiveSource']['path'],source_entry['originalSource']['path']]:
            metadata[item]=sha(item)
        for item in [UNIT/'OriginalCommands'/(original_name.replace('.','_')+'.json'),UNIT/'OriginalCommands'/(original_name.replace('.','_')+'.command.lean')]:
            metadata[str(item)]=sha(item)
        # Paper context is explicitly separate from the unchanged formal blind text.
        quote_ids=['IV-capsule-bound','IV-infinite-bound'] if original_name.endswith('sum_affine_quadratic') else ['IV-infinite-bound']
        selected_quotes=[quotes[q] for q in quote_ids]
        for q in selected_quotes:
            assert q['paper_id']=='IV'
            for evidence in q['evidence']:
                for key in ['page_image','raw_text']:
                    assert sha(evidence[key+'_path'])==evidence[key+'_sha256']
                    metadata[evidence[key+'_path']]=evidence[key+'_sha256']
        quote_text='\n\n'.join('> '+q['quote_markdown']+'\n\n— Shinichi Mochizuki, IUT IV, '+q['locator']+', printed p. '+', '.join(map(str,q['printed_pages'])) for q in selected_quotes)
        note=('This is a proved numerical auxiliary lemma in the reference Lean implementation. '
              'It supports the named source-code consumers recorded in the source ledger. '
              'The paper quotations below give background for the numerical estimates and their consumers; '
              'they do not state this auxiliary lemma verbatim. The lemma constructs no initial theta data. '
              'Its private platform proof remains detached from the canonical Corollary 2.2 root.')
        description=('**Independent formal-code readback**\n\n'+old.trilingual(rb[name])+
                     '\n\n**Paper source context (English; separate from the formal blind readback)**\n\n'+note+
                     '\n\n**Original paper quotations**\n\n'+quote_text+
                     '\n\nSource paper: '+paper['paper_sources']['IV']['official_url'])
        payload={k:raw[k]for k in ['theorem_name','preamble','formal_statement']}
        payload.update(theorem_title=original_name.split('.')[-1].replace('_',' '),natural_language_statement=description,
                       source=source_entry['originalSource']['url'],env=old.ENV,private=True)
        tag=name.replace('.','_')
        publications.append({'tag':tag,'endpoint':'/submit-problem','payload':payload})
        verification.append({'tag':tag,'theorem_name':name,'source':solution})
        explanations[name]=old.trilingual(rb[name])
        sources.update({p:sha(WORKSPACE/p)for p in [theorem,solution]})
    # Keep all seven validated helper sources bound, even if fewer are published.
    for name in ALL_NAMES:
        for kind in ['Theorems','Solutions']:
            path=old.relative_source(kind,name);sources[path]=sha(WORKSPACE/path)
    metadata[str(UNIT/'LICENSE')]=sha(UNIT/'LICENSE')
    packet={'schema':'numeric-helpers-private-delivery-candidates-v1','workspace':str(WORKSPACE),
            'mission_id':old.MISSION,'root_id':old.ROOT,'environment':old.ENV,'scope':old.SCOPE,
            'root_graph_membership':False,'canonicalC22Connected':False,
            'root_graph_counts_expected':[36,83,101,16,42],
            'mathematical_scope':'Pure numerical auxiliary lemmas; detached source preparation.',
            'source_sha256':sources,'metadata_sha256':metadata,'publications':publications,'verification':verification,
            'selection':names,'remaining_source_helpers':[n for n in ALL_NAMES if n not in names],
            'inline_helper':{'name':INLINE,'published':False,'consumer':'Iut.Theorem110Invariants.theorem110'},
            'required_ci_receipts':[r['path']for r in acceptance['receipts']]}
    save(output/'packet.json',packet)
    ready={'passed':False,'packet_sha256':sha(output/'packet.json'),'source_sha256':sources,
           'gates':{g:False for g in sorted(old.GATES)},'evidence_sha256':metadata.copy(),
           'ci_receipts':packet['required_ci_receipts'],'explanations':explanations,'scope':old.SCOPE,
           'required_inputs':{'production_reuse':None,'git_diff_check':None,'existing_mission_scope':None},
           'note':'Main agent must fill actual required evidence and explicitly set gates/passed; prepare never sets ready true.'}
    save(output/'ready.template.json',ready)
    save(output/'required-evidence.template.json',{
        'production_reuse':{'path':None,'required_fields':['receipt','input_hashes','configuration_hashes','source_sha256','passed'],
                            'allowed_job_ids':['ci-013203-76bab44a','ci-014934'],
                            'rule':'Bind actual successful ProductionGates receipt and rehash every recorded production input/configuration; unchanged hashes required.'},
        'git_diff_check':{'path':None,'required_fields':['command','exit_code','source_sha256'],
                          'rule':'Fresh root-produced git diff --check receipt; sources match packet.'},
        'existing_mission_scope':{'path':None,'rule':'Bind existing readonly platform preflight; same private mission/root/env; no root graph mutation.'},
        'all_seven_kernel_and_28_compile_receipts':packet['required_ci_receipts'],
        'publish_candidates':names,'inline_helper':packet['inline_helper'],
        'ready_passed':False})
    return packet

def preflight(packet_path, ready_path):
    packet,ready=read(packet_path),read(ready_path)
    selected=packet['selection']
    assert selected and set(selected)<=set(NAMES) and INLINE not in selected
    assert {r['payload']['theorem_name']for r in packet['publications']}==set(selected)
    assert set(packet['required_ci_receipts'])<=set(ready['ci_receipts'])
    assert all(path in ready['evidence_sha256']for path in packet['required_ci_receipts'])
    evidence=ready['required_inputs']
    for key in ['production_reuse','git_diff_check','existing_mission_scope']:
        assert evidence[key] and evidence[key] in ready['evidence_sha256']
    production=read(evidence['production_reuse'])
    assert production['passed'] is True
    receipt=read(production['receipt'])
    assert receipt['job_id']=='ci-013203-76bab44a' or receipt['job_id'].startswith('ci-014934-')
    assert production['receipt'] in ready['evidence_sha256']
    assert receipt['status']=='succeeded' and receipt['result']['review']['passed'] is True
    recorded=receipt['request']['worktree_manifest']['input_hashes']
    assert production['input_hashes']==recorded and recorded
    configurations=receipt['request']['worktree_manifest']['configuration_hashes']
    assert production['configuration_hashes']==configurations
    for path,digest in (recorded|configurations).items():
        p=Path(path) if Path(path).is_absolute() else WORKSPACE/path
        assert sha(p)==digest,('Changed production gate input',path)
    assert production['source_sha256']==packet['source_sha256']
    diff=read(evidence['git_diff_check'])
    assert diff['command']=='git diff --check' and diff['exit_code']==0
    assert diff['source_sha256']==packet['source_sha256']
    prior=old.NAMES
    try:
        old.NAMES=selected
        return BASE_PREFLIGHT(packet_path,ready_path)
    finally:
        old.NAMES=prior

old.prepare,old.preflight=prepare,preflight
deliver=old.deliver

def registry_candidate(registry_path, delivery_directory, output):
    """Write an offline candidate only after the existing six-proof delivery succeeds."""
    delivery_directory=Path(delivery_directory)
    summary=read(delivery_directory/'delivery-summary.json')
    assert summary['root_graph_unchanged'] and summary['canonicalC22Connected'] is False
    ids=summary['published_ids']; assert ids and set(ids)<=set(NAMES) and INLINE not in ids
    registry=read(registry_path);candidate=copy.deepcopy(registry)
    ref=candidate['reference_source_preparation']
    existing={r['name']for r in ref['proved_nodes']}
    added=[]
    for name,target in ids.items():
        assert name not in existing
        tag=name.replace('.','_');proof=read(delivery_directory/('verify-'+tag+'-result.json'))
        assert proof['status']=='ACCEPTED' and proof['theorem_id']==target
        item=read(delivery_directory/(tag+'-published-item.json'))
        assert item['theorem_name']==name and item['visibility']=='private'
        row={'name':name,'theorem_id':target,'status':'Proved','submission_id':proof['id'],
             'verification_status':'ACCEPTED','source_commit':'07cb1da58f6d428a670dbb5dd6093d428bcbcdd8',
             'root_graph_membership':False}
        ref['proved_nodes'].append(row);added.append(row)
    assert 'numeric_helpers_unit' not in ref
    ref['numeric_helpers_unit']={'scope':old.SCOPE,'canonicalC22Connected':False,'proved_nodes':added,
        'inline_helpers':[{'name':INLINE,'consumer':'Iut.Theorem110Invariants.theorem110','platformPublished':False}],
        'root_graph_counts_unchanged':True,'delivery_summary':str(delivery_directory/'delivery-summary.json')}
    before=copy.deepcopy(registry);after=copy.deepcopy(candidate)
    for value in [before,after]:
        value['reference_source_preparation'].pop('proved_nodes')
        value['reference_source_preparation'].pop('numeric_helpers_unit',None)
    assert before==after
    save(output,candidate)
    return candidate

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',required=True)
    ap.add_argument('--names',nargs='*',help='Optional subset of the six full theorem names')
    args=ap.parse_args()
    packet=prepare(args.out,args.names)
    print(json.dumps({'prepared':len(packet['publications']),'ready':False,'api_calls':0,'output':args.out}))
