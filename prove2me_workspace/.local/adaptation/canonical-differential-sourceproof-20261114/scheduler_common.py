from pathlib import Path
import copy, hashlib, json, math, socket, subprocess, sys

r = Path('/home/admin-wsl/Coq/abc')
w = r / 'prove2me_workspace'
b = w / '.local/adaptation/canonical-differential-sourceproof-20261114'
base = json.loads((w / '.local/adaptation/epsilon-large-height-sourceproof-20261114/solution-types-leaf-request.json').read_text())
base.update(session_id='p2m-canonical-differential-sourceproof-20261114', agent_id='/root', exclusive=True)
base.pop('working_directory', None)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n, x): (b / n).write_text(json.dumps(x, ensure_ascii=False, indent=2) + '\n')
def rpc(name, args):
    for attempt in range(3):
        s = socket.socket(socket.AF_UNIX); s.settimeout(40)
        try:
            s.connect('/home/admin-wsl/codex-miniCI/data/mcp-ci.sock')
            s.sendall((json.dumps({'jsonrpc':'2.0','id':'legendre-root','method':'tools/call','params':{'name':name,'arguments':args}})+'\n').encode())
            raw = json.loads(s.makefile('r').readline())
            if 'error' in raw: raise RuntimeError(raw['error'])
            z=raw['result']; return z.get('structuredContent') or json.loads(next(c['text'] for c in z['content'] if c['type']=='text'))
        except (TimeoutError, ConnectionError, OSError):
            if attempt == 2: raise
            print('Reconnect to the same scheduler; preserve job and idempotency key.', flush=True)
        finally: s.close()
def manifest(source):
    files=[p for folder in ['Definitions','Theorems','Solutions'] for p in (w/folder).glob('*.lean')]
    cfg=['lean-toolchain','lakefile.lean','lake-manifest.json']
    return dict(worktree_id=str(r), head=subprocess.check_output(['git','-C',str(r),'rev-parse','HEAD'],text=True).strip(), modified_files=subprocess.check_output(['git','-c','core.quotePath=false','-C',str(r),'diff','HEAD','--name-only'],text=True).splitlines(), untracked_files=subprocess.check_output(['git','-c','core.quotePath=false','-C',str(r),'ls-files','--others','--exclude-standard'],text=True).splitlines(), toolchain=(w/'lean-toolchain').read_text().strip(), dependency_lock='lake-manifest.json', dependency_lock_sha256=sha(w/'lake-manifest.json'), local_configuration=cfg, configuration_hashes={s:sha(w/s) for s in cfg}, input_hashes={str(p.relative_to(w)):sha(p) for p in files}, source_sha256=sha(w/source), external_dependencies=base['worktree_manifest']['external_dependencies'], required_artifacts=base['environment']['LEAN_PATH'].split(':'), excluded_credentials='credentials.json ignored; exclusive mode copies nothing')
def run(tag, source, kind='leaf', artifact=False, version='v1', duration='60s', memory='16GiB'):
    path=b/(tag+'-result.json')
    if path.exists():
        old=json.loads(path.read_text())
        if old['status']=='succeeded':
            assert old['request']['worktree_manifest']['source_sha256']==sha(w/source), tag
            print(tag, 'already succeeded', flush=True); return old
        raise RuntimeError('Archive failed attempt before retry: '+tag)
    q=copy.deepcopy(base); params={'args':[source,'-o','.lake/build/lib/lean/'+source[:-5]+'.olean']} if artifact else {'source':source}
    if artifact:
        (w/'.lake/build/lib/lean'/source).parent.mkdir(parents=True,exist_ok=True)
        prior=json.loads((b/(tag.removesuffix('-artifact')+'-leaf-result.json')).read_text())['resources']
        duration=str(max(60,math.ceil(prior['wall_time_seconds']*1.3)))+'s'
        memory=str(min(16,max(1,math.ceil(prior['peak_rss_bytes']/1024**3*1.3))))+'GiB'
    q.update(task_type='full' if artifact else kind,target='module' if artifact else 'file',parameters=params,expected_duration=duration,expected_memory=memory,worktree_manifest=manifest(source))
    q['idempotency_key']='p2m-canonical-differential-sourceproof-'+tag+'-'+version+'-'+sha(w/source)[:16]
    sp=b/(tag+'-submit.json')
    if sp.exists():
        assert json.loads((b/(tag+'-request.json')).read_text())==q
        submitted=json.loads(sp.read_text())
    else:
        save(tag+'-request.json',q); submitted=rpc('ci_submit',q); save(sp.name,submitted)
    job=submitted['job_id'];print(json.dumps({'tag':tag,'job_id':job,'status':'submitted'}),flush=True)
    while True:
        z=rpc('ci_wait',{'job_id':job,'timeout_seconds':20})
        if z['status'] not in ['queued','running','preparing_snapshot']: break
    z=rpc('ci_result',{'job_id':job});save(path.name,z);result=z['result'];res=z.get('resources',{})
    print(json.dumps({'tag':tag,'job_id':job,'status':z['status'],'wall':res.get('wall_time_seconds'),'cpu':res.get('cpu_time_seconds'),'rss':res.get('peak_rss_bytes'),'stdout':result.get('stdout','')[-5500:],'stderr':result.get('stderr','')[-1600:]},ensure_ascii=False),flush=True)
    if z['status']!='succeeded': sys.exit(1)
    assert result['exit_code']==0 and result['snapshot']['workspace_mode']=='exclusive_worktree' and result['snapshot']['snapshot_id'] is None
    assert result['actual_arguments']==(['lean']+params['args'] if artifact else ['lean',source])
    assert res.get('peak_rss_bytes') is None or res['peak_rss_bytes']<=16*1024**3
    if kind=='review': assert result['review']['passed']
    return z
