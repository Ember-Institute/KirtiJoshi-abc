"""Northcott delivery runner draft. Import and default execution perform no API action.

The main agent must align the final validation schema and supply an API adapter.
Adapter methods:
  request(endpoint, payload=None, method='GET') -> JSON object
  verify_file(theorem_id, proof_type, absolute_path, explanation) -> submit receipt
"""
from pathlib import Path
import hashlib
import json
import time

from graph_completion import fetch_complete_math_graph


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class Delivery:
    def __init__(self, api, evidence, workspace):
        self.api = api
        self.evidence = Path(evidence)
        self.workspace = Path(workspace)
        self.plan = self.read('delivery-plan.json')

    def read(self, name):
        return json.loads((self.evidence / name).read_text())

    def save(self, name, value):
        path = self.evidence / name
        temporary = path.with_name(path.name + '.tmp')
        temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
        temporary.replace(path)

    def bind(self, name, value):
        if (self.evidence / name).exists():
            assert self.read(name) == value, ('Bound request changed', name)
        else:
            self.save(name, value)

    def preflight(self):
        # The main agent supplies this file after actual integration and MCP-CI.
        assert all(item.get('source_sha256') for item in self.plan['solutions']), (
            'Root must generate six ASCII solution files and bind their actual hashes before delivery.')
        validation = self.read('delivery-validation.json')
        assert validation['passed'] is True
        assert validation['exact_existing_target_type_equal'] is True
        assert validation['readbacks_compiler_bound'] is True
        assert validation['new_open_mathematical_obligations'] == 0
        expected_sources = {item['source'] for item in self.plan['definitions']}
        expected_sources |= {'Theorems/Thm_' + name.replace('.', '_') + '.lean'
                             for name in self.plan['new_mathematical_nodes'] + [self.plan['parent_name']]}
        assert set(validation['source_hashes']) == expected_sources
        expected_solutions = {row['source'] for row in self.plan['solutions']}
        assert set(validation['solution_hashes']) == expected_solutions
        for relative, expected in validation['source_hashes'].items() | validation['solution_hashes'].items():
            assert sha(self.workspace / relative) == expected, relative
        assert validation['compiler_checks']
        for check in validation['compiler_checks']:
            receipt = self.read(check['tag'] + '-result.json')
            assert receipt['status'] == 'succeeded' and receipt['result']['exit_code'] == 0
            req, result = receipt['request'], receipt['result']
            assert req['workspace'] == str(self.workspace) and req['exclusive'] is True
            assert req['worktree_manifest']['source_sha256'] == sha(self.workspace / check['source'])
            assert result['snapshot']['workspace_mode'] == 'exclusive_worktree'
            assert result['snapshot']['snapshot_id'] is None
            assert 'sorryAx' not in result.get('stdout', '') + result.get('stderr', '')
        assert self.read('source-pin-draft.json')['sha256'] == sha(self.read('source-pin-draft.json')['exact_archive_path'])
        for mod in self.plan['definitions']:
            payload = self.read(mod['payload'])
            assert payload['definition'] == (self.workspace / mod['source']).read_text()
            assert not any(line.startswith('import Theorems.') for line in payload['definition'].splitlines())
        for item in self.plan['solutions']:
            assert sha(self.workspace / item['source']) == item['source_sha256']
        return validation

    def observe(self, ident, name):
        value = self.api.request('/theorems/' + ident)
        assert value['theorem_id'] == ident and value['theorem_name'] == name
        assert value['visibility'] == 'private' and value['mathlib_rev'] == self.plan['mathlib_rev']
        return value

    def publication(self, tag, endpoint, payload):
        intent = {'endpoint': endpoint, 'payload': payload}
        submitted_path = self.evidence / (tag + '-submit.json')
        if submitted_path.exists():
            assert self.read(tag + '-publication-requested.json') == intent
            submitted = self.read(submitted_path.name)
        else:
            assert not (self.evidence / (tag + '-publication-requested.json')).exists(), (
                'Prior POST has intent without receipt. Reconcile acceptance before retry.', tag)
            self.save(tag + '-payload.json', payload)
            self.save(tag + '-publication-requested.json', intent)
            submitted = self.api.request(endpoint, payload, 'POST')
            self.save(submitted_path.name, submitted)
        assert not submitted.get('errors'), submitted
        jobs = submitted.get('jobs') or [{'job_id': submitted['job_id']}]
        results = []
        for job in jobs:
            result = None
            for attempt in range(121):
                result = self.api.request('/publish-jobs/' + job['job_id'])
                self.save(tag + '-' + job['job_id'] + '-result.json', result)
                if result['status'] in ['PUBLISHED', 'FAILED', 'ERROR']:
                    break
                if attempt < 120:
                    time.sleep(5)
            assert result['status'] == 'PUBLISHED' and result['visibility'] == 'private', result
            results.append(result)
        return results

    def verify(self, name, ident, expected):
        short = name.removeprefix('AbcAdaptation.Tripod.').replace('.', '_')
        tag = 'verify-' + short
        request = self.read(tag + '-request-draft.json')
        request['theorem_id'] = ident
        request.pop('theorem_name', None)
        path = self.workspace / request['file']
        assert sha(path) == request['source_sha256']
        submit_path = self.evidence / (tag + '-submit.json')
        if submit_path.exists():
            assert self.read(tag + '-verification-requested.json') == request
            submitted = self.read(submit_path.name)
        else:
            assert not (self.evidence / (tag + '-verification-requested.json')).exists(), (
                'Prior verification has intent without receipt. Reconcile before retry.', tag)
            self.save(tag + '-verification-requested.json', request)
            submitted = self.api.verify_file(ident, 'prove', path, request['explanation'])
            self.save(submit_path.name, submitted)
        result = None
        for attempt in range(121):
            result = self.api.request('/verify?submission_id=' + submitted['submission_id'])
            self.save(tag + '-result.json', result)
            if result['status'] != 'PENDING':
                break
            if attempt < 120:
                time.sleep(5)
        assert result['id'] == submitted['submission_id'] and result['theorem_id'] == ident
        assert result['status'] in expected, result
        return result

    def frontier(self, stage):
        all_rows, offset, total = [], 0, None
        while True:
            page = self.api.request('/theorems/' + self.plan['root_id'] + '/open-leaves?limit=50&offset=' + str(offset))
            self.save('root-frontier-' + stage + '-page-' + str(offset) + '.json', page)
            total = page['total'] if total is None else total
            assert total == page['total']
            all_rows.extend(page['open_leaves'])
            offset += len(page['open_leaves'])
            if offset >= total:
                break
            assert page['open_leaves']
        assert len(all_rows) == total == len({row['theorem_id'] for row in all_rows})
        self.save('root-frontier-' + stage + '.json', {'open_leaves': all_rows, 'total': total, 'all_pages_fetched': True})

    def run(self):
        self.preflight()
        for suffix in ['before']:
            if not (self.evidence / ('root-graph-' + suffix + '.json')).exists():
                self.save('root-graph-' + suffix + '.json', fetch_complete_math_graph(
                    self.api, self.plan['root_id'], self.save, 'root-graph-' + suffix))
            if not (self.evidence / ('root-frontier-' + suffix + '.json')).exists():
                self.frontier(suffix)
        parent_id, parent = self.plan['parent_id'], self.plan['parent_name']
        current = self.observe(parent_id, parent)
        if not (self.evidence / 'platform-before-parent.json').exists():
            self.save('platform-before-parent.json', current)
        original_type = self.read('platform-before-parent.json')['formal_statement']
        assert current['formal_statement'] == original_type
        ids = dict(self.plan['existing_child_matches'])
        for module in self.plan['definitions']:
            self.publication('def-' + module['name'], '/submit-definition', self.read(module['payload']))
        batch = self.read('northcott-children-payload.json')
        if batch['problems']:
            results = self.publication('northcott-children', '/submit-problem', batch)
            for item in results:
                assert item['theorem_name'] not in ids
                ids[item['theorem_name']] = item['theorem_id']
        assert set(ids) == set(self.plan['new_mathematical_nodes'])
        self.save('published-child-ids.json', ids)
        # Parent reduction remains a separate accepted-sketch receipt.
        self.verify(parent, parent_id, {'SKETCH_ACCEPTED', 'ACCEPTED'})
        for name in self.plan['new_mathematical_nodes']:
            value = self.observe(ids[name], name)
            if value['status'] != 'Proved':
                self.verify(name, ids[name], {'ACCEPTED'})
            self.save('platform-after-' + name.removeprefix('AbcAdaptation.Tripod.').replace('.', '_') + '.json',
                      self.observe(ids[name], name))
        for attempt in range(13):
            current = self.observe(parent_id, parent)
            if current['status'] == 'Proved':
                break
            if attempt < 12:
                time.sleep(5)
        assert current['status'] == 'Proved', 'Keep original parent submission; propagation is pending.'
        assert current['formal_statement'] == original_type
        patch = self.read('parent-metadata-patch-draft.json')
        assert set(patch) == {'natural_language_statement', 'source'}
        self.bind('parent-metadata-patch-request.json', patch)
        if not all(current.get(k) == v for k, v in patch.items()):
            response = self.api.request('/theorems/' + parent_id, patch, 'PATCH')
            self.save('parent-metadata-patch-response.json', response)
        after = self.observe(parent_id, parent)
        assert after['formal_statement'] == original_type and after['status'] == 'Proved'
        assert all(after.get(k) == v for k, v in patch.items())
        self.save('platform-after-parent.json', after)
        graph = fetch_complete_math_graph(self.api, self.plan['root_id'], self.save, 'root-graph-after')
        self.save('root-graph-after.json', graph)
        self.frontier('after')
        root = self.observe(self.plan['root_id'], 'abc.goal.lt_constant_mul_fix')
        assert root['status'] != 'Proved'
        # Record actual shared helper dependencies. Do not impose the old unchanged-graph assertion.
        self.save('actual-delivery-states.json', {'parent': after,
                  'new_nodes': [self.observe(ids[n], n) for n in self.plan['new_mathematical_nodes']],
                  'root': root, 'expected_named_dependency_pairs': self.plan['true_dependencies'],
                  'graph_edges': graph['edges']})


if __name__ == '__main__':
    print('Draft only. Import Delivery and supply the main-agent accepted validation plus API adapter.')
    print('No API call or workspace mutation occurs from this default command.')
