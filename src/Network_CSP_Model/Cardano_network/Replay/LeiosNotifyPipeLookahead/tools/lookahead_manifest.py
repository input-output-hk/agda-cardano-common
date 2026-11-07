#!/usr/bin/env python3
"""Validate explicit lookahead replay profiles and capture declarations, never protocol traces.

Only load_manifest reads a file (the JSON manifest). Validation resolves capture
paths but does not open them, verify their hashes or establish the declarations.
Unknown deployed provenance stays unknown, separately from the model source pin.
"""
import argparse
import copy
import json
from pathlib import Path
import re
import tempfile

SCHEMA = 'leiosnotify-lookahead-manifest-v1'
MODEL_CONSENSUS_PIN = '2416493bfdbe93b761b3a4bb1ccf2b4a913e5e4b'
MODES = {'localclient': {'client'}, 'localserver': {'server'}, 'paired': {'client', 'server'}}
FIXED_PROFILE = {'observation': 'driver-log', 'clientCallbacks': 'generic-successful',
                 'return': 'unit', 'eof': 'prefix'}
CONTRACTS = {'generic-next', 'node-next'}
# Logger-silenced observation: RequestNext/Votes rows are absent; generic-successful client only.
SILENCED_OBSERVATION = 'driver-log-no-request-votes'
NODE_CLIENT_POLICY = 'node-client-control'
FULL_NODE_POLICY = 'full-node'
SHA256 = re.compile(r'[0-9a-fA-F]{64}\Z')
REVISION = re.compile(r'[0-9a-fA-F]{40}\Z')


def unique_keys(pairs):
    """Reject duplicate keys at every JSON object level instead of retaining the last value."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate manifest key: ' + key)
        result[key] = value
    return result


def reject_constant(value):
    """Python's permissive NaN/Infinity extension is outside the manifest's JSON schema."""
    raise ValueError('non-JSON number: ' + value)


def validate_manifest(data, base_dir):
    """Return ready/invalid-input/missing-capture-evidence and separate declared metadata.

    ready means that a supported profile and complete operator declarations are
    structurally present. It is not a proof of lossless capture or protocol acceptance.
    """
    errors, missing = [], []
    base = Path(base_dir).resolve()

    def issue(items, path, code, message):
        items.append({'path': path, 'code': code, 'message': message})

    def fields(value, required, optional, path):
        if not isinstance(value, dict):
            issue(errors, path, 'object-required', 'must be an object')
            return False
        for key in sorted(required - value.keys()):
            issue(errors, path + '.' + key, 'missing-field', 'required profile/input field is absent')
        for key in sorted(value.keys() - required - optional):
            issue(errors, path + '.' + key, 'unknown-field', 'unsupported field; no extra policy is inferred')
        return True

    def text(value, path):
        if not isinstance(value, str) or not value.strip() or value != value.strip() or any(ord(c) < 32 for c in value):
            issue(errors, path, 'text-required', 'must be nonempty trimmed text without control characters')
            return None
        return value

    def digest(value, path):
        if value is not None and (not isinstance(value, str) or not SHA256.fullmatch(value)):
            issue(errors, path, 'sha256-required', 'must be a 64-digit hexadecimal SHA-256 or null')
        return value.lower() if isinstance(value, str) and SHA256.fullmatch(value) else None

    def resolve(value, path):
        value = text(value, path)
        return str((base / value).resolve()) if value else None

    report = {'schema': SCHEMA, 'status': 'invalid-input', 'errors': errors, 'missingEvidence': missing,
              'protocolVerdict': None, 'validation': 'schema and declared capture evidence only',
              'profile': None, 'endpoints': {},
              'model': {'consensusRevision': MODEL_CONSENSUS_PIN, 'repositoryRevision': None},
              'limitations': ['Capture paths are resolved but capture files and checksums are not read or verified.',
                  'Fresh/ordered/lossless statements and endpoint pairing are declarations, not established facts.',
                  'No protocol decision, deployed conformance, deployment revision or successful completion is inferred.']}
    required = {'schema', 'protocol', 'mode', 'observation', 'clientCallbacks', 'return',
                'serverContract', 'eof', 'connection', 'session', 'endpoints', 'checkerInput'}
    if not fields(data, required, {'model', 'note', 'nodePolicy'}, '$'):
        return report
    if data.get('schema') != SCHEMA:
        issue(errors, '$.schema', 'unsupported-schema', 'expected ' + SCHEMA)
    if data.get('protocol') != 'LeiosNotifyP':
        issue(errors, '$.protocol', 'unsupported-protocol', 'only LeiosNotifyP is supported')
    mode = data.get('mode')
    if not isinstance(mode, str) or mode not in MODES:
        issue(errors, '$.mode', 'unsupported-mode', 'expected localclient, localserver or paired')
    node_client_policy = data.get('clientCallbacks') == NODE_CLIENT_POLICY
    full_node_policy = data.get('nodePolicy') == FULL_NODE_POLICY
    if 'nodePolicy' in data and not full_node_policy:
        issue(errors, '$.nodePolicy', 'unsupported-profile', 'supported explicit nodePolicy is full-node')
    if full_node_policy and (mode != 'paired' or not node_client_policy or data.get('serverContract') != 'node-next'):
        issue(errors, '$.nodePolicy', 'unsupported-profile',
              'full-node requires mode paired, clientCallbacks node-client-control and serverContract node-next')
    silenced = data.get('observation') == SILENCED_OBSERVATION
    if silenced and (node_client_policy or 'nodePolicy' in data):
        issue(errors, '$.observation', 'unsupported-profile',
              SILENCED_OBSERVATION + ' requires clientCallbacks generic-successful and no nodePolicy')
    for key, supported in FIXED_PROFILE.items():
        if key == 'observation' and silenced:
            continue
        if key == 'clientCallbacks' and node_client_policy:
            if mode != 'localclient' and not full_node_policy:
                issue(errors, '$.clientCallbacks', 'unsupported-profile',
                      'node-client-control requires localclient or an explicit paired full-node profile')
        elif data.get(key) != supported:
            issue(errors, '$.' + key, 'unsupported-profile', 'supported value is ' + supported)
    contract = data.get('serverContract')
    if not isinstance(contract, str) or contract not in CONTRACTS:
        issue(errors, '$.serverContract', 'unsupported-contract', 'explicit generic-next or node-next is required')
    report['profile'] = {key: data.get(key) for key in ['protocol', 'mode', *FIXED_PROFILE, 'serverContract']}
    if full_node_policy:
        report['profile']['nodePolicy'] = FULL_NODE_POLICY
        report['profile']['serverContractUsed'] = True
        report['profile']['clientPolicyScope'] = 'full NodeDriverModel; fixed depth1000; credit FIFO; existential policy inputs'
        report['limitations'].append('Full-node acceptance establishes an existential original node-policy wire run; actual forecast/governor/eligibility/handler truth remains external.')
    elif node_client_policy:
        report['profile']['serverContractUsed'] = False
        report['profile']['clientPolicyScope'] = 'local NodeClientModel; fixed depth1000; existential policy inputs'
        report['limitations'].append('This local client policy does not check NodeDriver forecast/governor inputs, server credit/FIFO policy or actual exception outcomes.')
    if silenced:
        report['limitations'].append('Silenced acceptance concerns the RequestNext/Votes-erased observation, not full-observation '
                                     'acceptance; undetermined is a failed canonical reconstruction, never a rejection.')
    checker_input = data.get('checkerInput')
    report['checkerInput'] = None
    report['checkerArguments'] = None
    if fields(checker_input, {'format', 'file'}, {'sha256'}, '$.checkerInput'):
        expected_format = 'paired-v1' if mode == 'paired' else 'local-v1'
        if checker_input.get('format') != expected_format:
            issue(errors, '$.checkerInput.format', 'unsupported-input-format', 'mode requires ' + expected_format)
        report['checkerInput'] = {'format': checker_input.get('format'),
            'file': resolve(checker_input.get('file'), '$.checkerInput.file'),
            'declaredSha256': digest(checker_input.get('sha256'), '$.checkerInput.sha256')}
    for key in ['connection', 'session']:
        report[key] = text(data.get(key), '$.' + key)
    if 'note' in data:
        text(data['note'], '$.note')
    if 'model' in data and fields(data['model'], {'consensusRevision'}, {'repositoryRevision'}, '$.model'):
        model = data['model']
        if model.get('consensusRevision') != MODEL_CONSENSUS_PIN:
            issue(errors, '$.model.consensusRevision', 'unsupported-model', 'this profile uses the pinned consensus model revision')
        revision = model.get('repositoryRevision')
        if revision is not None and (not isinstance(revision, str) or not REVISION.fullmatch(revision)):
            issue(errors, '$.model.repositoryRevision', 'revision-required', 'must be a full 40-digit git revision or null')
        report['model']['repositoryRevision'] = revision
    endpoints = data.get('endpoints')
    roles = MODES.get(mode, set()) if isinstance(mode, str) else set()
    if fields(endpoints, roles, set(), '$.endpoints'):
        for role in sorted(roles & endpoints.keys()):
            endpoint = endpoints[role]
            path = '$.endpoints.' + role
            if not fields(endpoint, {'node', 'connection', 'generation', 'file'},
                          {'capture', 'captureEvidence', 'source', 'sourceMap', 'sha256',
                           'sourceSha256', 'sourceMapSha256', 'provenance'}, path):
                continue
            out = {'role': role}
            report['endpoints'][role] = out
            for key in ['node', 'connection', 'generation']:
                out[key] = text(endpoint.get(key), path + '.' + key)
            out['file'] = resolve(endpoint.get('file'), path + '.file')
            out['declaredSha256'] = digest(endpoint.get('sha256'), path + '.sha256')
            capture = endpoint.get('capture')
            if capture is not None and capture not in ('fresh', 'unknown', 'partial'):
                issue(errors, path + '.capture', 'unsupported-capture', 'expected fresh, unknown or partial')
            if capture != 'fresh':
                issue(missing, path + '.capture', 'fresh-assertion-required', 'fresh initial-state assertion is required; suffix initialization is unsupported')
            out['initialStateAssertion'] = capture
            evidence = endpoint.get('captureEvidence')
            if evidence is None:
                issue(missing, path + '.captureEvidence', 'capture-evidence-required', 'declare ordered/lossless capture and the basis for that declaration')
            elif fields(evidence, set(), {'ordered', 'lossless', 'basis'}, path + '.captureEvidence'):
                for key in ['ordered', 'lossless']:
                    value = evidence.get(key)
                    if value is not None and type(value) is not bool:
                        issue(errors, path + '.captureEvidence.' + key, 'boolean-required', 'must be true, false or null')
                    if value is not True:
                        issue(missing, path + '.captureEvidence.' + key, 'capture-assertion-required', 'an explicit true declaration is required')
                if evidence.get('basis') is None:
                    issue(missing, path + '.captureEvidence.basis', 'evidence-basis-required', 'state the basis for the capture declarations')
                else:
                    text(evidence['basis'], path + '.captureEvidence.basis')
            out['captureEvidence'] = copy.deepcopy(evidence)
            if ('source' in endpoint) != ('sourceMap' in endpoint):
                issue(errors, path, 'source-map-pair-required', 'source and sourceMap must be supplied together')
            for key in ['source', 'sourceMap']:
                out[key] = resolve(endpoint[key], path + '.' + key) if key in endpoint else None
            for key in ['source', 'sourceMap']:
                if key + 'Sha256' in endpoint and key not in endpoint:
                    issue(errors, path + '.' + key + 'Sha256', 'orphan-checksum', 'checksum requires the corresponding path')
                out['declared' + key[0].upper() + key[1:] + 'Sha256'] = digest(endpoint.get(key + 'Sha256'), path + '.' + key + 'Sha256')
            provenance = endpoint.get('provenance', {})
            out['provenance'] = {'sourceRevision': None, 'binarySha256': None, 'buildId': None}
            if fields(provenance, set(), {'sourceRevision', 'binarySha256', 'buildId', 'note'}, path + '.provenance'):
                revision = provenance.get('sourceRevision')
                if revision is not None and (not isinstance(revision, str) or not REVISION.fullmatch(revision)):
                    issue(errors, path + '.provenance.sourceRevision', 'revision-required', 'must be a full deployed source revision or null')
                out['provenance']['sourceRevision'] = revision
                out['provenance']['binarySha256'] = digest(provenance.get('binarySha256'), path + '.provenance.binarySha256')
                for key in ['buildId', 'note']:
                    if provenance.get(key) is not None:
                        out['provenance'][key] = text(provenance[key], path + '.provenance.' + key)
    if mode == 'paired' and set(report['endpoints']) == {'client', 'server'}:
        if report['endpoints']['client'].get('node') == report['endpoints']['server'].get('node'):
            issue(errors, '$.endpoints', 'distinct-node-identities-required', 'declare distinct client and server node identities')
    report['status'] = 'invalid-input' if errors else 'missing-capture-evidence' if missing else 'ready'
    if report['status'] == 'ready':
        argv = (['--paired-notify-lookahead', report['checkerInput']['file']] if mode == 'paired' else
                ['--notify-lookahead', report['checkerInput']['file'], '--role', next(iter(roles))])
        if full_node_policy:
            report['checkerArguments'] = argv + ['--node-policy', FULL_NODE_POLICY,
                                                  '--observation', 'driver-log', '--assume-fresh']
        elif node_client_policy:
            report['checkerArguments'] = argv + ['--client-policy', NODE_CLIENT_POLICY,
                                                  '--observation', 'driver-log', '--assume-fresh']
        else:
            report['checkerArguments'] = argv + ['--next-contract', contract, '--observation', data['observation'], '--assume-fresh']
    return report


def load_manifest(path):
    """Read one manifest with strict JSON duplicate-key checking; never open declared input paths."""
    path = Path(path).resolve()
    try:
        data = json.loads(path.read_text(), object_pairs_hook=unique_keys, parse_constant=reject_constant)
    except (OSError, ValueError, UnicodeError) as exc:
        report = validate_manifest(None, path.parent)
        report['errors'] = [{'path': '$', 'code': 'manifest-read-failed', 'message': str(exc)}]
    else:
        report = validate_manifest(data, path.parent)
    report['manifest'] = str(path)
    return report


def example_manifest(mode='paired'):
    """Create a schema example with honest unknown deployment provenance, without touching captures."""
    result = {'schema': SCHEMA, 'protocol': 'LeiosNotifyP', 'mode': mode,
              **FIXED_PROFILE, 'serverContract': 'node-next', 'connection': 'example-AB', 'session': 'example-0',
              'model': {'consensusRevision': MODEL_CONSENSUS_PIN, 'repositoryRevision': None}, 'endpoints': {}}
    result['checkerInput'] = {'format': 'paired-v1' if mode == 'paired' else 'local-v1',
                              'file': 'pair.txt' if mode == 'paired' else next(iter(MODES[mode])) + '.txt'}
    for role in sorted(MODES[mode]):
        result['endpoints'][role] = {'node': 'example-' + role, 'connection': role + '-connection',
            'generation': '0', 'file': role + '.txt', 'capture': 'fresh',
            'captureEvidence': {'ordered': True, 'lossless': True,
                'basis': 'EXAMPLE ONLY: replace with your actual capture declaration and evidence'},
            'provenance': {'sourceRevision': None, 'binarySha256': None, 'buildId': None}}
    return result


def example_full_node_manifest():
    """Select the full policy explicitly while retaining honest unknown deployed provenance."""
    result = example_manifest('paired')
    result.update(nodePolicy=FULL_NODE_POLICY, clientCallbacks=NODE_CLIENT_POLICY)
    return result


def selftest():
    """Exercise supported profiles, explicit evidence failures and provenance separation without a node."""
    cases = 0
    with tempfile.TemporaryDirectory(prefix='lookahead-manifest-') as directory:
        base = Path(directory)
        for mode in MODES:
            for contract in CONTRACTS:
                data = example_manifest(mode)
                data['serverContract'] = contract
                report = validate_manifest(data, base)
                assert report['status'] == 'ready', report
                assert report['protocolVerdict'] is None
                assert report['checkerArguments'][-1] == '--assume-fresh'
                assert all(ep['provenance']['sourceRevision'] is None for ep in report['endpoints'].values())
                assert not any(Path(ep['file']).exists() for ep in report['endpoints'].values())
                cases += 1
        # The new policy is an explicit local-client branch; old examples stay generic.
        for contract in CONTRACTS:
            data = example_manifest('localclient')
            data.update(clientCallbacks=NODE_CLIENT_POLICY, serverContract=contract)
            report = validate_manifest(data, base)
            assert report['status'] == 'ready' and report['profile']['serverContractUsed'] is False
            assert report['checkerArguments'] == ['--notify-lookahead', str(base/'client.txt'),
                '--role', 'client', '--client-policy', NODE_CLIENT_POLICY,
                '--observation', 'driver-log', '--assume-fresh']
            assert report['protocolVerdict'] is None
            cases += 1
        for mode in ('localserver', 'paired'):
            data = example_manifest(mode)
            data['clientCallbacks'] = NODE_CLIENT_POLICY
            report = validate_manifest(data, base)
            assert report['status'] == 'invalid-input' and report['checkerArguments'] is None
            cases += 1
        data = example_full_node_manifest()
        report = validate_manifest(data, base)
        assert report['status'] == 'ready' and report['profile']['serverContractUsed'] is True
        assert report['checkerArguments'] == ['--paired-notify-lookahead', str(base/'pair.txt'),
            '--node-policy', FULL_NODE_POLICY, '--observation', 'driver-log', '--assume-fresh']
        assert report['protocolVerdict'] is None
        cases += 1
        def check_full(change, status):
            nonlocal cases
            data = example_full_node_manifest()
            change(data)
            report = validate_manifest(data, base)
            assert report['status'] == status and report['protocolVerdict'] is None, report
            if status != 'ready':
                assert report['checkerArguments'] is None
            cases += 1
        check_full(lambda d: d.pop('nodePolicy'), 'invalid-input')
        check_full(lambda d: d.update(nodePolicy='node-next'), 'invalid-input')
        check_full(lambda d: d.update(nodePolicy=None), 'invalid-input')
        check_full(lambda d: d.update(clientCallbacks='generic-successful'), 'invalid-input')
        check_full(lambda d: d.update(serverContract='generic-next'), 'invalid-input')
        check_full(lambda d: d.update(mode='localclient'), 'invalid-input')
        check_full(lambda d: d.update(mode='localserver'), 'invalid-input')
        check_full(lambda d: d['checkerInput'].update(format='local-v1'), 'invalid-input')
        check_full(lambda d: d['endpoints']['server'].update(capture='partial'), 'missing-capture-evidence')
        check_full(lambda d: d['endpoints']['client']['captureEvidence'].update(lossless=False), 'missing-capture-evidence')
        check_full(lambda d: d['endpoints']['server']['provenance'].update(sourceRevision=None), 'ready')
        def check_node(change, status):
            nonlocal cases
            data = example_manifest('localclient')
            data['clientCallbacks'] = NODE_CLIENT_POLICY
            change(data)
            report = validate_manifest(data, base)
            assert report['status'] == status and report['protocolVerdict'] is None, report
            if status != 'ready':
                assert report['checkerArguments'] is None
            cases += 1
        check_node(lambda d: d.update(clientCallbacks='fixed-depth-1000'), 'invalid-input')
        check_node(lambda d: d.pop('clientCallbacks'), 'invalid-input')
        check_node(lambda d: d.update(returnValue='unit'), 'invalid-input')
        check_node(lambda d: d.update({'return': 'arbitrary'}), 'invalid-input')
        check_node(lambda d: d.update(eof='success'), 'invalid-input')
        check_node(lambda d: d.update(observation='source-operations'), 'invalid-input')
        check_node(lambda d: d.update(serverContract='unused'), 'invalid-input')
        check_node(lambda d: d['checkerInput'].update(format='paired-v1'), 'invalid-input')
        check_node(lambda d: d['endpoints']['client'].update(capture='unknown'), 'missing-capture-evidence')
        check_node(lambda d: d['endpoints']['client']['captureEvidence'].update(lossless=False), 'missing-capture-evidence')
        check_node(lambda d: d['endpoints']['client']['captureEvidence'].pop('basis'), 'missing-capture-evidence')
        def check(change, status):
            nonlocal cases
            data = example_manifest()
            change(data)
            report = validate_manifest(data, base)
            assert report['status'] == status, report
            assert report['protocolVerdict'] is None
            cases += 1
        # The silenced observation is an explicit generic-successful profile in every mode.
        for mode in MODES:
            data = example_manifest(mode)
            data['observation'] = SILENCED_OBSERVATION
            report = validate_manifest(data, base)
            assert report['status'] == 'ready' and report['profile']['observation'] == SILENCED_OBSERVATION, report
            assert report['checkerArguments'][-3:] == ['--observation', SILENCED_OBSERVATION, '--assume-fresh']
            assert report['protocolVerdict'] is None
            cases += 1
        check(lambda d: d.update(observation=SILENCED_OBSERVATION, nodePolicy=FULL_NODE_POLICY,
                                 clientCallbacks=NODE_CLIENT_POLICY), 'invalid-input')
        check_node(lambda d: d.update(observation=SILENCED_OBSERVATION), 'invalid-input')
        check(lambda d: d.update(observation=SILENCED_OBSERVATION, eof='success'), 'invalid-input')
        check(lambda d: d.update(observation=SILENCED_OBSERVATION) or d['endpoints']['client'].pop('capture'),
              'missing-capture-evidence')
        check(lambda d: d.update(mode='fixed-node'), 'invalid-input')
        check(lambda d: d.update(clientCallbacks='fixed-depth-1000'), 'invalid-input')
        check(lambda d: d.update(depth=1000), 'invalid-input')
        check(lambda d: d.update(serverContract='inferred'), 'invalid-input')
        check(lambda d: d.update(observation='source-operations'), 'invalid-input')
        check(lambda d: d.update(eof='success'), 'invalid-input')
        check(lambda d: d['checkerInput'].update(format='local-v1'), 'invalid-input')
        check(lambda d: d['checkerInput'].update(sha256=False), 'invalid-input')
        check(lambda d: d['endpoints']['client'].update(capture='unknown'), 'missing-capture-evidence')
        check(lambda d: d['endpoints']['client'].pop('capture'), 'missing-capture-evidence')
        check(lambda d: d['endpoints']['server'].pop('captureEvidence'), 'missing-capture-evidence')
        check(lambda d: d['endpoints']['server'].update(capture='partial'), 'missing-capture-evidence')
        check(lambda d: d['endpoints']['server']['captureEvidence'].pop('basis'), 'missing-capture-evidence')
        check(lambda d: d['endpoints']['server']['captureEvidence'].update(lossless=False), 'missing-capture-evidence')
        check(lambda d: d['endpoints']['server']['captureEvidence'].update(ordered=1), 'invalid-input')
        check(lambda d: d['endpoints']['client'].update(source='capture with spaces.log'), 'invalid-input')
        check(lambda d: d['endpoints']['client'].update(source='capture with spaces.log', sourceMap='map.txt'), 'ready')
        check(lambda d: d['endpoints']['client'].update(sha256='broken'), 'invalid-input')
        check(lambda d: d['endpoints']['client'].update(sourceMapSha256='0'*64), 'invalid-input')
        check(lambda d: d['endpoints']['server']['provenance'].update(sourceRevision=MODEL_CONSENSUS_PIN), 'ready')
        check(lambda d: d['endpoints']['server'].update(node='example-client'), 'invalid-input')
        check(lambda d: d['model'].update(consensusRevision='0'*40), 'invalid-input')
        for key in ['schema', 'protocol', 'mode', 'observation', 'clientCallbacks', 'return',
                    'serverContract', 'eof', 'connection', 'session', 'endpoints', 'checkerInput']:
            for value in [None, False, 0, [], {}]:
                data = example_manifest()
                data[key] = value
                assert validate_manifest(data, base)['status'] == 'invalid-input', (key, value)
                cases += 1
        for raw in ['{"schema":"a","schema":"b"}', '{"endpoints":{"client":{"file":"a","file":"b"}}}', '{', '{"x":NaN}']:
            path = base/'manifest.json'
            path.write_text(raw)
            assert load_manifest(path)['status'] == 'invalid-input'
            cases += 1
        path.write_text(json.dumps(example_manifest('localserver')))
        assert load_manifest(path)['status'] == 'ready'
        cases += 1
    return {'selftest': 'passed', 'cases': cases, 'scope': 'Python schema/declaration checks, not formal proof or protocol replay'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', nargs='?', type=Path)
    parser.add_argument('--selftest', action='store_true')
    parser.add_argument('--example', choices=[*sorted(MODES), FULL_NODE_POLICY])
    args = parser.parse_args()
    if sum([bool(args.manifest), args.selftest, bool(args.example)]) != 1:
        parser.error('choose one manifest, --selftest or --example MODE')
    if args.selftest:
        print(json.dumps(selftest(), indent=2))
        return
    if args.example:
        print(json.dumps(example_full_node_manifest() if args.example == FULL_NODE_POLICY else example_manifest(args.example), indent=2))
        return
    report = load_manifest(args.manifest)
    print(json.dumps(report, indent=2))
    raise SystemExit({'ready': 0, 'invalid-input': 2, 'missing-capture-evidence': 3}[report['status']])


if __name__ == '__main__':
    main()
