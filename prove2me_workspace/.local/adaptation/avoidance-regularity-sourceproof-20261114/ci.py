from pathlib import Path
import importlib.util, json, sys

b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/avoidance-regularity-sourceproof-20261114')
spec=importlib.util.spec_from_file_location('oldci',b/'scheduler_common.py')
ci=importlib.util.module_from_spec(spec);spec.loader.exec_module(ci)
ci.b=b;ci.base['session_id']='p2m-avoidance-regularity-sourceproof-20261114'
def manifest(source):
    state=json.loads((b/'git-input-state.json').read_text())
    cfg=['lean-toolchain','lakefile.lean','lake-manifest.json']
    files=[p for folder in ['Definitions','Theorems','Solutions'] for p in (ci.w/folder).glob('*.lean')]
    return dict(worktree_id=str(ci.r),**state,toolchain=(ci.w/'lean-toolchain').read_text().strip(),dependency_lock='lake-manifest.json',dependency_lock_sha256=ci.sha(ci.w/'lake-manifest.json'),configuration_hashes={f:ci.sha(ci.w/f) for f in cfg},input_hashes={str(p.relative_to(ci.w)):ci.sha(p) for p in files},source_sha256=ci.sha(ci.w/source),external_dependencies=ci.base['worktree_manifest']['external_dependencies'],required_artifacts=ci.base['environment']['LEAN_PATH'].split(':'),excluded_credentials='Ignored credentials; direct exclusive workspace, no snapshot')
ci.manifest=manifest
run=ci.run
u='.local/adaptation/avoidance-regularity-sourceproof-20261114/'
if __name__=='__main__':
    f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_avoidanceRegularity.lean'
    run('avoidanceRegularity-leaf',f,duration='60s',memory='7GiB');run('avoidanceRegularity-artifact',f,artifact=True)
    run('closed-axioms-review','Solutions/Checks_FermatAvoidanceRegularity.lean','review')
    run('compiler-facts-leaf',u+'ExtractAvoidanceFacts.lean')
