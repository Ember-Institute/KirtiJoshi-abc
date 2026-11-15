from pathlib import Path
import hashlib
import json

out = Path('/tmp/p2m-numeric-log-blind-v6-20261115')
source_dir = Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-c22-numeric-helpers-20261115/blind-formal-code')
mission = Path('/home/admin-wsl/Coq/abc/prove2me_workspace/references/mission_auditor.md')
records = [
    {
        'name': 'log_bound_ell',
        'en': r'For every pair of real numbers $\delta$ and $h$, both implicit parameters, given the explicit hypotheses $h_\delta:1\leq\delta$ and $h_h:1\leq h$, the natural logarithm satisfies $\log(20\delta^2h^2)\leq6\log(2\delta h)$. Both inequalities in the hypotheses are non-strict, so $\delta=1$, $h=1$, and their simultaneous occurrence are included; zero and negative values of either parameter are excluded. Under these hypotheses both logarithm arguments are positive. There are no additional parameters or typeclass assumptions. The supplied proof is the placeholder `by sorry`.',
        'zh-Hans': r'对于任意实数 $\delta$ 和 $h$（二者均为隐式参数），给定显式前提 $h_\delta:1\leq\delta$ 和 $h_h:1\leq h$，自然对数满足 $\log(20\delta^2h^2)\leq6\log(2\delta h)$。两个前提中的不等式均为非严格不等式，因此包括 $\delta=1$、$h=1$ 以及二者同时成立的情形；任一参数为零或负数的情形均被排除。在这些前提下，两个对数的真数均为正数。没有其他参数或类型类假设。所提供的证明为占位代码 `by sorry`。',
        'ja': r'任意の実数 $\delta$ と $h$（いずれも暗黙のパラメータ）について、明示的な仮定 $h_\delta:1\leq\delta$ および $h_h:1\leq h$ のもとで、自然対数は $\log(20\delta^2h^2)\leq6\log(2\delta h)$ を満たす。仮定の二つの不等式はいずれも等号を許すため、$\delta=1$、$h=1$、および両者が同時に成り立つ場合も含まれる。いずれかのパラメータが零または負となる場合は除外される。これらの仮定のもとでは、二つの対数の真数はいずれも正である。ほかのパラメータや型クラスの仮定はない。提示された証明はプレースホルダー `by sorry` である。',
        'assumptions': {
            'implicit_parameters': [{'name': 'δ', 'type': 'real number'}, {'name': 'h', 'type': 'real number'}],
            'explicit_hypotheses': [{'name': 'hδ', 'proposition': r'$1\leq\delta$'}, {'name': 'hh', 'proposition': r'$1\leq h$'}],
            'typeclass_assumptions': []
        },
        'conclusion': r'$\log(20\delta^2h^2)\leq6\log(2\delta h)$, where $\log$ denotes the natural logarithm.'
    },
    {
        'name': 'log_le_four_mul_sqrt_sqrt',
        'en': r'For every real number $h$, an implicit parameter, given the explicit hypothesis $h_h:1\leq h$, the natural logarithm and the nonnegative real square root satisfy $\log h\leq4\sqrt{\sqrt h}$. The boundary value $h=1$ is included; zero and negative values are excluded. Under the hypothesis, the logarithm argument and both radicands are positive, and both square roots are the nonnegative real square roots. There are no additional parameters or typeclass assumptions. The supplied proof is the placeholder `by sorry`.',
        'zh-Hans': r'对于任意实数 $h$（隐式参数），给定显式前提 $h_h:1\leq h$，自然对数与非负实平方根满足 $\log h\leq4\sqrt{\sqrt h}$。包括边界值 $h=1$；零和负数均被排除。在该前提下，对数的真数和两个被开方数均为正数，两个平方根均指非负实平方根。没有其他参数或类型类假设。所提供的证明为占位代码 `by sorry`。',
        'ja': r'任意の実数 $h$（暗黙のパラメータ）について、明示的な仮定 $h_h:1\leq h$ のもとで、自然対数と非負の実平方根は $\log h\leq4\sqrt{\sqrt h}$ を満たす。境界値 $h=1$ は含まれ、零および負の値は除外される。この仮定のもとでは、対数の真数と二つの被開平数はいずれも正であり、二つの平方根はいずれも非負の実平方根を表す。ほかのパラメータや型クラスの仮定はない。提示された証明はプレースホルダー `by sorry` である。',
        'assumptions': {
            'implicit_parameters': [{'name': 'h', 'type': 'real number'}],
            'explicit_hypotheses': [{'name': 'hh', 'proposition': r'$1\leq h$'}],
            'typeclass_assumptions': []
        },
        'conclusion': r'$\log h\leq4\sqrt{\sqrt h}$, where $\log$ is the natural logarithm and each square root is the nonnegative real square root.'
    },
    {
        'name': 'log_le_half_of_pos',
        'en': r'For every real number $y$, an implicit parameter, given the explicit hypothesis $h_y:0<y$, the natural logarithm satisfies $\log y\leq y/2$, where division is in the real numbers. All positive real values are included, in particular $0<y<1$ and $y=1$; $y=0$ and negative values are excluded. The denominator is the nonzero real number $2$, so no division-by-zero case occurs. There are no additional parameters or typeclass assumptions. The supplied proof is the placeholder `by sorry`.',
        'zh-Hans': r'对于任意实数 $y$（隐式参数），给定显式前提 $h_y:0<y$，自然对数满足 $\log y\leq y/2$，其中除法为实数除法。包括所有正实数值，特别包括 $0<y<1$ 和 $y=1$；$y=0$ 和负数均被排除。分母为非零实数 $2$，因此不存在除以零的情形。没有其他参数或类型类假设。所提供的证明为占位代码 `by sorry`。',
        'ja': r'任意の実数 $y$（暗黙のパラメータ）について、明示的な仮定 $h_y:0<y$ のもとで、自然対数は $\log y\leq y/2$ を満たす。ここで除算は実数の除算である。すべての正の実数値が含まれ、とくに $0<y<1$ および $y=1$ も含まれる。$y=0$ および負の値は除外される。分母は零でない実数 $2$ であるため、零による除算は生じない。ほかのパラメータや型クラスの仮定はない。提示された証明はプレースホルダー `by sorry` である。',
        'assumptions': {
            'implicit_parameters': [{'name': 'y', 'type': 'real number'}],
            'explicit_hypotheses': [{'name': 'hy', 'proposition': '$0<y$'}],
            'typeclass_assumptions': []
        },
        'conclusion': r'$\log y\leq y/2$, where $\log$ is the natural logarithm and division is real division.'
    },
    {
        'name': 'log_le_self_of_pos',
        'en': r'For every real number $y$, an implicit parameter, given the explicit hypothesis $h_y:0<y$, the natural logarithm satisfies $\log y\leq y$. All positive real values are included, in particular $0<y<1$ and $y=1$; $y=0$ and negative values are excluded. There are no additional parameters or typeclass assumptions. The supplied proof is the placeholder `by sorry`.',
        'zh-Hans': r'对于任意实数 $y$（隐式参数），给定显式前提 $h_y:0<y$，自然对数满足 $\log y\leq y$。包括所有正实数值，特别包括 $0<y<1$ 和 $y=1$；$y=0$ 和负数均被排除。没有其他参数或类型类假设。所提供的证明为占位代码 `by sorry`。',
        'ja': r'任意の実数 $y$（暗黙のパラメータ）について、明示的な仮定 $h_y:0<y$ のもとで、自然対数は $\log y\leq y$ を満たす。すべての正の実数値が含まれ、とくに $0<y<1$ および $y=1$ も含まれる。$y=0$ および負の値は除外される。ほかのパラメータや型クラスの仮定はない。提示された証明はプレースホルダー `by sorry` である。',
        'assumptions': {
            'implicit_parameters': [{'name': 'y', 'type': 'real number'}],
            'explicit_hypotheses': [{'name': 'hy', 'proposition': '$0<y$'}],
            'typeclass_assumptions': []
        },
        'conclusion': r'$\log y\leq y$, where $\log$ denotes the natural logarithm.'
    }
]

metadata = {
    'fresh_context': True,
    'input_only_formal_code': True,
    'input_only_formal_code_scope': 'The mathematical readbacks use only the four complete Lean files. The mission_auditor.md file supplies the auditing instructions.',
    'configured_model': 'gpt-6.1-sol',
    'actual_backend_model': None,
    'actual_backend_model_note': 'The actual backend model is not independently reported in this context.',
    'author_rewriting_applied': False,
    'compilation_performed': False,
    'mathematical_proof_verified': False,
    'platform_acceptance_checked': False,
    'instruction_input': {'file': str(mission), 'sha256': hashlib.sha256(mission.read_bytes()).hexdigest()},
    'formal_inputs': []
}

for r in records:
    name = r.pop('name')
    f = source_dir / ('Thm_AbcAdaptation_Reference_Iut_' + name + '.lean')
    digest = hashlib.sha256(f.read_bytes()).hexdigest()
    r['file'] = f.name
    r['source_sha256'] = digest
    r['proof_status'] = {'status': 'placeholder_by_sorry', 'literal_proof': 'by\n  sorry', 'proof_verification_performed': False}
    metadata['formal_inputs'].append({'file': str(f), 'source_sha256': digest})
    (out / (name + '.json')).write_text(json.dumps(r, ensure_ascii=False, indent=2) + '\n')

(out / 'readbacks.json').write_text(json.dumps({'metadata': metadata, 'declarations': records}, ensure_ascii=False, indent=2) + '\n')
(out / 'metadata.json').write_text(json.dumps(metadata, ensure_ascii=False, indent=2) + '\n')
(out / 'original_english_readbacks.md').write_text('\n\n'.join('## ' + r['file'] + '\n\n' + r['en'] for r in records) + '\n')
for language, filename in [('zh-Hans', 'readbacks.zh-Hans.md'), ('ja', 'readbacks.ja.md')]:
    (out / filename).write_text('\n\n'.join('## ' + r['file'] + '\n\n' + r[language] for r in records) + '\n')

# Check serialization and preservation of the original English paragraphs without compiling Lean.
loaded = json.loads((out / 'readbacks.json').read_text())
assert len(loaded['declarations']) == 4
for r in loaded['declarations']:
    assert r['en'] in (out / 'original_english_readbacks.md').read_text()
    assert set(['file', 'source_sha256', 'en', 'zh-Hans', 'ja', 'assumptions', 'conclusion', 'proof_status']) <= set(r)
    assert hashlib.sha256((source_dir / r['file']).read_bytes()).hexdigest() == r['source_sha256']
print(json.dumps({'output_dir': str(out), 'declaration_count': 4, 'json_roundtrip': 'passed', 'english_preservation': 'passed', 'input_hashes_rechecked': 'passed', 'compilation_performed': False}, ensure_ascii=False))
