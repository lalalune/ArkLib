#!/usr/bin/env python3
"""Check archived execution receipts and exact field certificates, not a scan replay."""

import argparse
import hashlib
import json
from math import isqrt, prod
from pathlib import Path
import subprocess

HEAD = '5ec32fa23607ec7a205dc3a17cd0f8cd1c71a402'
SOURCE_SHA = '6b2069e47e698fa96100881eb81175e6acdd8d60d5e0b24a19682817ffa117a5'
P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
N = 2**30
ROOT = Path(__file__).resolve().parents[2]
DEFAULT = Path(__file__).resolve().parent / 'receipts/astra_hosted_33941607360'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(directory):
    manifest = json.loads((directory / 'manifest.json').read_text())
    names = {'acceptance.jsonl', 'metadata.json', 'stdout.jsonl', 'stderr.txt',
             'result.json', 'field_certificate.json'}
    require(set(manifest['files']) == names, 'Wrong archive file inventory')
    require(manifest['head'] == HEAD and manifest['run_id'] == 33941607360,
            'Wrong hosted revision or run')
    for name, expected in manifest['files'].items():
        require(digest((directory / name).read_bytes()) == expected,
                f'Archive digest mismatch: {name}')
    for key, path in [('native_source', 'scripts/probes/astra_mca_native_eval.cpp'),
                      ('acceptance_driver', 'scripts/probes/astra_mca_native_eval_check.py')]:
        require(manifest[key] == path, f'Unexpected pinned path: {key}')
        data = subprocess.check_output(['git', 'show', f'{HEAD}:{path}'], cwd=ROOT)
        require(digest(data) == manifest[key + '_sha256'], f'Pinned source mismatch: {key}')
    require(manifest['native_source_sha256'] == SOURCE_SHA, 'Wrong native revision')

    def rows(name):
        return [json.loads(line) for line in (directory / name).read_text().splitlines()
                if line.strip()]

    acceptance_rows, output_rows = rows('acceptance.jsonl'), rows('stdout.jsonl')
    require(len(acceptance_rows) == len(output_rows) == 1, 'Unexpected receipt count')
    acceptance, count = acceptance_rows[0], output_rows[0]
    metadata = json.loads((directory / 'metadata.json').read_text())
    result = json.loads((directory / 'result.json').read_text())
    require(all(result.get(key) == value for key, value in metadata.items()),
            'Execution metadata changed between start and completion')
    require(result['head'] == HEAD and result['source_sha256'] == SOURCE_SHA,
            'Execution source mismatch')
    require(result['exit_code'] == 0 and result['timed_out'] is False,
            'Incomplete execution')
    require(result['status'] == 'COMPLETE_NATIVE_COUNT_NOT_PRIZE_CLOSURE',
            'No completed native count')
    require(result['count_receipt'] == count, 'Raw output differs from result')
    for name in ('stdout', 'stderr'):
        suffix = '.jsonl' if name == 'stdout' else '.txt'
        require(result[name + '_sha256'] == digest((directory / (name + suffix)).read_bytes()),
                f'Execution digest mismatch: {name}')
    require(not (directory / 'stderr.txt').read_bytes(), 'Unexpected execution diagnostic')
    require(acceptance['status'] == 'PASS_BOUNDED_NATIVE_ACCEPTANCE_NOT_PRODUCTION_SCAN'
            and acceptance['compiled_from_current_source_by_this_run'] is True,
            'Missing compiling acceptance')
    require(acceptance['source_sha256'] == SOURCE_SHA and
            acceptance['binary_sha256'] == result['binary_sha256'],
            'Acceptance and execution disagree')
    require(result['command'] == [acceptance['binary'], '--scan', str(N), '4', '8193'],
            'Unexpected scan command')
    expected = dict(mode='exact_fingerprint_scan', n=N, slots=N+2,
                    array_bytes=8*(N+2), chart_pole_slots=0, distinct_keys=N+1,
                    finite_event_count_lower_bound=N+1, exact_resolution_used=False,
                    length_plus_one_met=True, production_budget_exceeded=True,
                    scope='native_finite_computation_not_Lean_proof')
    require(all(count.get(key) == value for key, value in expected.items()),
            'Unexpected production count or scope')
    require(count['available_bytes_before'] >= count['array_bytes'] + 4*2**30,
            'Insufficient recorded allocation reserve')

    certificate = json.loads((directory / 'field_certificate.json').read_text())
    require((certificate['prime'], certificate['generator'], certificate['order']) == (P, G, N),
            'Wrong field or domain certificate')
    certified = set()
    nodes = certificate['certificate_nodes']
    for number in sorted(map(int, nodes)):
        node = nodes[str(number)]
        if node['method'] == 'trial division':
            require(2 <= number <= 4533259, 'Unexpected trial-division leaf')
            require(all(number % divisor for divisor in range(2, isqrt(number)+1)),
                    f'Composite certificate leaf: {number}')
        else:
            require(node['method'] == 'full Lucas order certificate', 'Unknown prime certificate')
            factors = {int(q): exponent for q, exponent in node['factorization'].items()}
            require(all(q in certified and type(e) is int and e > 0 for q, e in factors.items()),
                    'Unproved factor in Lucas certificate')
            require(prod(q**e for q, e in factors.items()) == number-1, 'Incomplete factorization')
            base = node['base']
            require(pow(base, number-1, number) == 1, 'Lucas full-power check failed')
            for q in factors:
                residue = pow(base, (number-1)//q, number)
                require(residue != 1 and residue == node['nonunit_power_residues'][str(q)],
                        'Lucas proper-order check failed')
        certified.add(number)
    require(P in certified, 'Modulus was not certified prime')
    require(pow(G, N, P) == 1 and pow(G, N//2, P) == P-1, 'Wrong root order')
    require(P == N*(2**128+192)+1 and P//2**128 == N, 'Wrong scalar budget')
    require((N+1)*2**128 > P, 'No strict budget violation')
    return dict(status='PASS_ARCHIVE_AND_EXACT_FIELD_CHECKS', run_id=33941607360,
                finite_value_lower_bound=N+1, field_certificate_nodes=len(certified),
                scalar_budget=N, radius_numerator=(N-1)//3, radius_denominator=N,
                production_scan_replayed=False, binary_retained=False,
                scope='Receipt consistency and field arithmetic; relies on reviewed execution and written MCA bridge, not Lean closure')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt-dir', type=Path, default=DEFAULT)
    args = parser.parse_args()
    print(json.dumps(verify(args.receipt_dir), sort_keys=True))


if __name__ == '__main__':
    main()
