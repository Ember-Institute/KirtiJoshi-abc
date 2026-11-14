#!/usr/bin/env python3
"""Read accepted compiler graph; write only this task's inventory and parser config.

No Lean execution, source slicing, regular expressions, API, or Git operations.
"""
import hashlib
import json
from collections import Counter, deque
from pathlib import Path

TASK = Path('/tmp/p2m-reference-foundation-parser-20261115')
BASE = Path('/home/admin-wsl/Coq/abc')
GRAPH = BASE / 'prove2me_workspace/.local/adaptation/reference-extraction-20261115/c22-decl-graph.jsonl'
CLOSURE = Path('/tmp/p2m-reference-carrier-closure-next-20261115')
ORDER = ['Iut.Cor312.ThetaData.Places', 'Iut.Cor312.ThetaData.PointMap',
         'Iut.Cor312.RationalPlace', 'Iut.Cor312.Procession', 'Iut.Cor312.PacketPresentation']
SOURCE_ROOTS = {
 ORDER[0]: ['Iut.Place', 'Iut.Place.finite', 'Iut.Place.infinite', 'Iut.FinitePlace.LiesOver', 'Iut.residueChar'],
 ORDER[1]: ['Iut.Anabelian.pointMap'],
 ORDER[2]: ['Iut.RationalPlace', 'Iut.RationalPlace.IsFinite', 'Iut.RationalPlace.residueChar'],
 ORDER[3]: ['Iut.procLabels', 'Iut.procLabels_mono', 'Iut.Capsule', 'Iut.Capsule.card',
            'Iut.Capsule.LabelType', 'Iut.Capsule.instDecidableEqLabelType',
            'Iut.Capsule.instFintypeLabelType', 'Iut.Procession', 'Iut.Procession.standard'],
 ORDER[4]: ['Iut.DirectSumPresentation', 'Iut.DirectSumPresentation.Total',
            'Iut.DirectSumPresentation.instTopologicalSpaceTotal', 'Iut.DirectSumPresentation.integralRegion',
            'Iut.DirectSumPresentation.IsProductRegion', 'Iut.DirectSumPresentation.productRegion',
            'Iut.DirectSumPresentation.scaledIntegral', 'Iut.DirectSumPresentation.IsHullRegion']}
HELPERS = {
 'Iut.RationalPlace.IsFinite': {
  'policy': 'retain original source command before residueChar; no separate platform node',
  'reason': 'The accepted residueChar value uses the matcher also used by earlier IsFinite; preserving the earlier equations command retains its compiler-generated identity.',
  'sharedCompilerConstant': 'Iut.RationalPlace.IsFinite.match_1',
  'actualConsumer': 'Iut.RationalPlace.residueChar',
  'ownershipStatus': 'source-command owner must be confirmed by the small-source compiler oracle; do not infer ownership solely from the matcher name'},
 'Iut.procLabels_mono': {
  'policy': 'retain exact source proof inline in Procession Def bundle; no separate platform node',
  'actualConsumerChain': ['Iut.Procession.standard', 'Iut.Procession.standard._proof_1', 'Iut.procLabels_mono']}}

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(name, data):
    (TASK/name).write_text(json.dumps(data, ensure_ascii=False, indent=2)+'\n')
def point_offset(raw, p):
    lines=raw.decode().splitlines(keepends=True)
    return len((''.join(lines[:p['line']-1])+lines[p['line']-1][:p['col']]).encode())

def main():
    TASK.mkdir(exist_ok=True)
    rows=[json.loads(l) for l in GRAPH.read_text().splitlines()]
    rows=[r for r in rows if r.get('record')=='decl']
    by={r['name']:r for r in rows}
    modules={m['module']:m for m in json.loads((CLOSURE/'modules.json').read_text())}
    reverse={n:[] for n in by}
    for r in rows:
        for edge in ['typeDeps','valueDeps','constructors']:
            for n in r[edge]: reverse[n].append({'consumer':r['name'],'edge':edge})
    root='Iut.Theorem110Invariants.theorem110'
    def path_to_root(name):
        queue=deque([[name]]);seen={name}
        while queue:
            path=queue.popleft()
            if path[-1]==root:return path
            for e in reverse[path[-1]]:
                if e['consumer'] not in seen:
                    seen.add(e['consumer']);queue.append(path+[e['consumer']])
        return None
    config={'schema':'reference-foundation-parser-config-v1',
      'outputDir':str(TASK/'parser-output'), 'acceptedGraphSha256':sha(GRAPH), 'sources':[]}
    inventory=[];imports=[]
    oldroot=Path('/home/admin-wsl/Coq/mathlib4');newroot=Path('/home/admin-wsl/Coq/mathlib4-0df444a')
    mappings={'Mathlib.Basic.SetLike.Basic':'Mathlib.Data.SetLike.Basic',
              'Mathlib.Algebra.Group.Monoid':'Mathlib.Algebra.Group.Defs'}
    for module in ORDER:
        m=modules[module];source=Path(m['source']);raw=source.read_bytes();normalized=raw.replace(b'\r\n',b'\n')
        assert sha(source)==m['sourceSha256']
        assert hashlib.sha256(normalized).hexdigest()==m['normalizedSha256']
        for name in SOURCE_ROOTS[module]:
            if name in HELPERS:
                rng=by[name]['range']
                a=point_offset(normalized,rng['start']);b=point_offset(normalized,rng['end'])
                HELPERS[name].update(acceptedCompilerSource=str(source),
                  acceptedCompilerDeclarationRange=rng,normalizedByteStart=a,normalizedByteEnd=b,
                  compilerRangeBytesSha256=hashlib.sha256(normalized[a:b]).hexdigest(),
                  exactParserCommandSpan='pending main MCP-CI parser acceptance; no regex',
                  proofSubspan='pending AST, not claimed known')
        selected={d['name'] for d in m['actualRequiredDeclarations'] if d['inFullStructureEmission']}
        selected.update(SOURCE_ROOTS[module])
        module_rows=[r for r in rows if r['module']==module]
        facts=[];cfg=[]
        for r in module_rows:
            d=dict(r);d['selectedForBundle']=r['name'] in selected
            d['actualConsumers']=reverse[r['name']]
            d['consumerPathToMainTheorem']=path_to_root(r['name'])
            d['sourceCommandRootCandidate']=r['name'] in SOURCE_ROOTS[module]
            d['sourceHelper']=HELPERS.get(r['name'])
            facts.append(d)
            rng=r['range']
            cfg.append({'name':r['name'],'kind':r['kind'],'selected':r['name'] in selected,
              'sourceRootCandidate':r['name'] in SOURCE_ROOTS[module],
              'sourceHelper':r['name'] in HELPERS,
              'hasCompilerRange':rng is not None,
              'expectedStartOffset':point_offset(normalized,rng['start']) if rng else None,
              'expectedEndOffset':point_offset(normalized,rng['end']) if rng else None})
        config['sources'].append({'module':module,'source':str(source),
          'sourceSha256':m['sourceSha256'],'normalizedSha256':m['normalizedSha256'],
          'compilerDeclarations':cfg})
        inventory.append({'module':module,'source':str(source), 'sourceSha256':m['sourceSha256'],
          'normalizedSha256':m['normalizedSha256'], 'noProjectDependencies':not m['actualRequiredParticipatingModuleDependencies'],
          'parsedSourceImports':m['parsedSourceImports'], 'selectedSourceCommandCandidates':SOURCE_ROOTS[module],
          'sourceCommandSelectionStatus':'candidate list; final groups require compiler-range containment in parser command AST',
          'graphCounts':dict(Counter(r['kind'] for r in module_rows)), 'declarations':facts})
        import_facts=[]
        external=set(m['actualRequiredExternalTermModules'])
        # Include terms used by the retained matcher-generating source helper.
        for n in SOURCE_ROOTS[module]:external.update(d['module'] for d in by[n]['externalDependencies'])
        for name in sorted(x for x in external if x.startswith('Mathlib.')):
            mapped=mappings.get(name,name)
            import_facts.append({'sourceCompilerTermModule':name,
              'source435PathExists':oldroot.joinpath(*name.split('.')).with_suffix('.lean').is_file(),
              'platform433SamePathExists':newroot.joinpath(*name.split('.')).with_suffix('.lean').is_file(),
              'platform433Candidate':mapped,
              'platform433CandidatePathExists':newroot.joinpath(*mapped.split('.')).with_suffix('.lean').is_file(),
              'status':'static source existence only; macro/notation context and compiler compatibility need CI'})
        imports.append({'module':module,'candidates':import_facts,'monolithicMathlibImportAllowed':False})
    write('parser-config.json',config)
    write('inventory.json',{'schema':'reference-foundation-inventory-v1','graph':str(GRAPH),
      'graphSha256':sha(GRAPH),'acceptedGraphJob':'ci-012771-ee109b3e','modules':inventory})
    write('imports.json',imports)
    write('machine-plan.json',{
      'status':'draft-only-no-CI-no-source-generation-no-API-no-Git', 'modules':ORDER,
      'sourceCommandCandidates':sum(len(v) for v in SOURCE_ROOTS.values()),
      'sourceHelpers':HELPERS, 'maximumSourceHelpers':10,
      'parserOnly':{'query':'QueryFoundationParserRanges.lean','config':'parser-config.json',
        'environmentVariable':'FOUNDATION_PARSER_CONFIG','compiler':'4.35.0-rc3',
        'mode':'single cached C22 import; testParseModule only; no processHeader or processCommands',
        'firstLeafEstimate':{'expected_duration':'60s','expected_memory':'16GiB'}},
      'gatesBeforeSourceGeneration':[
        'Main agent accepts exclusive MCP-CI parser receipt, actual arguments, no diagnostics, and process-tree peak RSS <= 16GiB.',
        'Verify graph/config/query/fact hashes, raw SHA256, normalized LF SHA256, and all compiler range offsets.',
        'Join selected ranged graph declarations to exactly one complete parser command by compiler-range containment; reject unsupported atomic groups.',
        'Retain every original context command and the original command order; include RationalPlace.IsFinite helper before residueChar.',
        'Review no-range compiler auxiliaries as small-source reconstruction obligations, never handwritten declarations.'],
      'smallSourceFollowup':[
        'Only after parser acceptance: slice complete selected declaration commands by AST byte ranges. Keep all source context commands and license/module documentation.',
        'Replace only the import header with reviewed exact Mathlib candidates; no import Mathlib. Five small source files remain separate.',
        'Run the existing small-source InfoTree oracle through MCP-CI on these selected source commands, not the full original modules.',
        'Check generated declarations, constructor/projection completeness, every selected definition body and auxiliary dependency; audit sorryAx and allowed axioms.',
        'Use accepted small-source refs to wrap in namespace AbcAdaptation.Reference. Reuse the existing PrimeSelection namespace and Def bundle without redefining its carriers.',
        'Kernel-compare original/wrapped Exprs with a complete original-to-wrapped constant-name map; require precise consumers before platform node publication.'],
      'platformBundlePolicy':'At most five carrier Def bundles; source helper lemmas stay inline. No independent orphan theorem or auto-generated projection nodes.',
      'preservedInstances':['RationalPlace deriving DecidableEq','Capsule LabelType DecidableEq/Fintype',
        'DirectSumPresentation ring_summand/topology_summand instance attributes','DirectSumPresentation Total topology'],
      'scope':'Real source carriers for Theorem110 signature; no Act2, no new Fermat slots, no mathematical parent-obligation completion claim'})
    print(json.dumps({'modules':len(inventory),'sourceCommandCandidates':sum(len(v) for v in SOURCE_ROOTS.values()),
      'helpers':len(HELPERS),'declarations':sum(len(m['declarations']) for m in inventory)},ensure_ascii=False))

if __name__=='__main__':main()
