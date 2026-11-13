from copy import deepcopy


def fetch_complete_math_graph(api, root_id, save, tag):
    overview = api.request('/theorems/' + root_id + '/graph?depth=8')
    save(tag + '-overview.json', overview)
    nodes, edges, missing, complete, drilled = {}, {}, {}, set(), []
    hidden_deprecated = False
    hidden_sketches = False

    def merge(graph):
        nonlocal hidden_deprecated, hidden_sketches
        hidden_deprecated |= bool(graph.get('has_hidden_deprecated'))
        hidden_sketches |= bool(graph.get('has_hidden_deprecated_sketches'))
        for node in graph['nodes']:
            ident = node['node_id'] if node['node_type'] == 'sketch' else node['theorem_id']
            nodes[ident] = deepcopy(node)
            if not node.get('has_more_children'):
                complete.add(ident)
            for edge in node.get('missing_children', []):
                key = (edge['source'], edge['target'])
                missing.setdefault(ident, {})[key] = edge
        for edge in graph['edges']:
            edges[(edge['kind'], edge['source'], edge['target'])] = deepcopy(edge)

    merge(overview)
    while True:
        pairs = {(edge['source'], edge['target']) for edge in edges.values()}
        pending = []
        for ident, node in nodes.items():
            if node['node_type'] != 'theorem' or node['status'] == 'Definition':
                continue
            unresolved = [edge for key, edge in missing.get(ident, {}).items() if key not in pairs]
            unknown = node.get('has_more_children') and not missing.get(ident) and ident not in complete
            if unknown or any(edge.get('hidden_by_definitions') is not True for edge in unresolved):
                pending.append(ident)
        if not pending:
            break
        for ident in pending:
            assert ident not in drilled, ('Mathematical graph still truncated after a direct drill', ident)
            graph = api.request('/theorems/' + ident + '/graph?depth=2')
            save(tag + '-drill-' + ident + '.json', graph)
            merge(graph)
            drilled.append(ident)
    pairs = {(edge['source'], edge['target']) for edge in edges.values()}
    for ident, node in nodes.items():
        unresolved = [edge for key, edge in missing.get(ident, {}).items() if key not in pairs]
        if node['node_type'] == 'theorem' and node['status'] != 'Definition':
            assert all(edge.get('hidden_by_definitions') is True for edge in unresolved)
        node['missing_children'] = unresolved
        node['has_more_children'] = bool(unresolved)
    out = deepcopy(overview)
    out.update(nodes=list(nodes.values()), edges=list(edges.values()),
               has_hidden_deprecated=hidden_deprecated,
               has_hidden_deprecated_sketches=hidden_sketches,
               mathematical_closure_complete=True, mathematical_drills=drilled,
               overview_receipt=tag + '-overview.json')
    return out
