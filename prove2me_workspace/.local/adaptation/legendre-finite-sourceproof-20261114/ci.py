from pathlib import Path
import importlib.util, json, sys

b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/legendre-finite-sourceproof-20261114')
spec=importlib.util.spec_from_file_location('oldci',b/'scheduler_common.py')
ci=importlib.util.module_from_spec(spec);spec.loader.exec_module(ci)
ci.b=b;ci.base['session_id']='p2m-legendre-finite-sourceproof-20261114'
def manifest(source):
    state=json.loads((b/'git-input-state.json').read_text())
    cfg=['lean-toolchain','lakefile.lean','lake-manifest.json']
    files=[p for folder in ['Definitions','Theorems','Solutions'] for p in (ci.w/folder).glob('*.lean')]
    return dict(worktree_id=str(ci.r),**state,toolchain=(ci.w/'lean-toolchain').read_text().strip(),dependency_lock='lake-manifest.json',dependency_lock_sha256=ci.sha(ci.w/'lake-manifest.json'),configuration_hashes={f:ci.sha(ci.w/f) for f in cfg},input_hashes={str(p.relative_to(ci.w)):ci.sha(p) for p in files},source_sha256=ci.sha(ci.w/source),external_dependencies=ci.base['worktree_manifest']['external_dependencies'],required_artifacts=ci.base['environment']['LEAN_PATH'].split(':'),excluded_credentials='Ignored credentials; direct exclusive workspace, no snapshot')
ci.manifest=manifest
run=ci.run
u='.local/adaptation/legendre-finite-sourceproof-20261114/'
mods=['TripodLegendreValuationBounds','TripodFinitePlaceArithmetic','TripodFiniteHeightSupport','TripodLegendreFinitePlaceBounds','TripodFinitePrimeCounting']
if __name__=='__main__':
    for n in mods:
        f='Solutions/Source_'+n+'.lean';run(n+'-leaf',f);run(n+'-artifact',f,artifact=True)
    for n in ['legendreFiniteUpperBound','legendreFiniteLowerBound']:
        f='Theorems/Thm_AbcAdaptation_Tripod_'+n+'.lean'
        run(n+'-leaf',f,duration='45s',memory='6GiB');run(n+'-artifact',f,artifact=True)
    f='Solutions/Sol_LegendreFiniteSourceClosure.lean';run('parent-solution-leaf',f);run('parent-solution-artifact',f,artifact=True)
    run('closed-axioms-review','Solutions/Checks_LegendreFiniteSourceClosure.lean','review')
    run('source-graph-leaf',u+'ExtractFiniteGraph.lean')
    run('all-constants-review',u+'AuditAllConstants.lean','review')
    run('production-gates-review',u+'ProductionGates.lean','review',duration='100s',memory='10GiB')
