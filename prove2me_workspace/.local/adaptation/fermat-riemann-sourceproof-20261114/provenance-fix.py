from pathlib import Path
import json,hashlib,importlib.util
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/fermat-riemann-sourceproof-20261114'
s=importlib.util.spec_from_file_location('ci','/tmp/p2m-riemann-sourceproof-ci-20261114.py');ci=importlib.util.module_from_spec(s);s.loader.exec_module(ci)
v=json.loads((b/'sourceproof-validation.json').read_text());assert v['passed']
f='Definitions/Def_FermatCurveFieldDegree.lean';p=w/f;before=p.read_bytes();old=b'Only the namespace, local imports, and Place.degree name are changed.';new=b'Scalar instances and proof elaboration are adapted; mathematical statements are preserved.'
assert before.count(old)==1
assert hashlib.sha256(before).hexdigest()==v['definition_hashes'][f]
after=before.replace(old,new);assert after.count(b'\n')==before.count(b'\n');p.write_bytes(after)
ci.run('degree-provenance-leaf',f,duration='70s',memory='6GiB')
v['definition_hashes'][f]=hashlib.sha256(after).hexdigest()
v['comment_only_provenance_correction']={'file':f,'previous_sha256':hashlib.sha256(before).hexdigest(),'current_sha256':hashlib.sha256(after).hexdigest(),'old_header_line':old.decode(),'new_header_line':new.decode(),'proof_and_declaration_bytes_unchanged':True,'source_line_numbers_unchanged':True,'recheck_receipt':'degree-provenance-leaf-result.json','note':'A single line inside the existing leading block comment was corrected. Compiled declarations and their graph spans are unchanged; the exact corrected source passed a scheduled leaf check.'}
ci.save('sourceproof-validation.json',v)
print('Source attribution corrected and exact source rechecked.',flush=True)
