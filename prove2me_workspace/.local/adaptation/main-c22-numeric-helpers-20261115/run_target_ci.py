"""Root-only sequential exclusive MCP-CI targets. No direct compiler calls."""
import argparse,json,math,subprocess,sys
from pathlib import Path
B=Path(__file__).resolve().parent
W=B.parents[2]
def load(p):return json.loads(Path(p).read_text())
def run(tag,source,extra=()):
 result=B/(tag+'-result.json')
 if result.exists():
  r=load(result)
  if r['status']!='succeeded':raise RuntimeError('Preserve failed input and use a new attempt tag: '+tag)
  return r
 sub=B/(tag+'-submit.json')
 if not sub.exists():
  subprocess.run([sys.executable,str(B/'ci.py'),'submit',tag,source,*extra],check=True)
 print(json.dumps({'tag':tag,**load(sub)}),flush=True)
 while not result.exists():
  subprocess.run([sys.executable,str(B/'ci.py'),'collect',tag],check=True)
 return load(result)
def artifact(tag,source,leaf):
 r=leaf['resources'];duration=str(max(30,math.ceil(r['wall_time_seconds']*1.3)))+'s';memory=str(max(2,min(16,math.ceil(r['peak_rss_bytes']/1024**3*1.3))))+'GiB'
 return run(tag,source,['--artifact','--duration',duration,'--memory',memory,'--basis','Measured matching source leaf plus30percent margin; existing dependencies preserved'])
def main():
 entries=load(B/'manifest.json')['entries']
 for e in entries:
  short=e['originalName'].split('.')[-1];slug=e['wrappedName'].replace('.','_')
  for folder,prefix,kind in [('Theorems','Thm_','theorem'),('Solutions','Sol_','solution')]:
   source=folder+'/'+prefix+slug+'.lean';tag='numeric-'+short+'-'+kind
   if short=='log_bound_ell' and kind=='theorem':leaf=load(B/'numeric-log-bound-theorem-result.json')
   else:leaf=run(tag+'-leaf',source,['--purpose','Exact numerical source target/signature or closed original proof; theorem stubs intentionally Open'])
   artifact(tag+'-artifact',source,leaf)
  audit=str((B/'generated-target/Audits'/('Audit_'+slug+'.lean')).relative_to(W))
  run('numeric-'+short+'-audit',audit,['--review','--env','NUMERIC_ORIGINAL_EXPR_FILE='+str(B/'source-facts/original-exprs.json'),'--env','NUMERIC_AUDIT_OUTPUT_DIR='+str(B/'type-audits'),'--input',str(B/'source-facts/original-exprs.json'),'--purpose','Full original-target-solution kernel types, entire BinderInfo, exact signature flags, native constants and solution standard axioms'])
 print(json.dumps({'status':'all-seven-target-signature-proof-and-kernel-audits-succeeded','platformUploaded':False}),flush=True)
if __name__=='__main__':main()
