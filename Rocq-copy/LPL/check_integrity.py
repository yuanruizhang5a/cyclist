#!/usr/bin/env python3
"""Audit every LPL source and build record; optionally recheck every module."""
from __future__ import annotations

import argparse
import ast
from collections import defaultdict
import json
from pathlib import Path
import re
import subprocess
import time

from build import COMMON, COQ_FLAGS, FOPL_BENCHMARKS, PPL_BENCHMARKS, HERE, ROOT, digest, inside


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def save(logs, name, data):
    (logs / name).write_text(json.dumps(data, indent=2) + '\n')


def uncomment(source):
    index, depth, quoted, result = 0, 0, False, []
    while index < len(source):
        if not quoted and source[index:index+2] == '(*':
            depth += 1
            index += 2
            continue
        if depth and source[index:index+2] == '*)':
            depth -= 1
            index += 2
            continue
        if not depth:
            if source[index] == '"':
                quoted = not quoted
            result.append(source[index])
        elif source[index] == '\n':
            result.append('\n')
        index += 1
    return ''.join(result)


def legacy_import(match):
    names = match.group(1).split()
    lines = []
    if 'Signature' in names:
        lines.append('From CyclistRocq.LPL.FOPL Require Import Signature.')
        names.remove('Signature')
    if names:
        lines.append('From CyclistRocq.LPL.FOPL.LegacyReference Require Import ' + ' '.join(names) + '.')
    return '\n'.join(lines)


def audit_sources(logs):
    sources = sorted(p for p in HERE.rglob('*.v') if '.build' not in p.parts)
    names = {str(p.relative_to(HERE)) for p in sources}
    expected = COMMON + [f'FOPL/Benchmarks/{n}.v' for n in FOPL_BENCHMARKS] + [
        f'Benchmarks/PPL/{n}.v' for n in PPL_BENCHMARKS]
    project = [s for s in (HERE / '_CoqProject').read_text().splitlines() if s.endswith('.v')]
    require(len(expected) == len(set(expected)) == len(sources) and set(expected) == names,
            'Build inventory does not match the source tree')
    require(len(project) == len(set(project)) == len(sources) and set(project) == names,
            '_CoqProject contains missing, repeated or unlisted sources')
    require(not (HERE / 'Core').exists(), 'Obsolete Core directory remains')
    groups = defaultdict(list)
    violations, imports = {}, {}
    forbidden = r'\b(?:Admitted|admit|Axiom|Axioms|Conjecture|Ltac|Ltac2|Tactic\s+Notation)\b|Unset\s+(?:Guard|Positivity|Universe)\s+Checking|\b\w+_no_check\b'
    for path in sources:
        name = str(path.relative_to(HERE))
        code = uncomment(path.read_text())
        groups[digest(path)].append(name)
        if re.search(forbidden, code):
            violations[name] = 'Admitted proof, custom tactic, axiom or disabled check'
        prefixes = re.findall(r'From\s+([\w.]+)\s+Require\s+(?:Import|Export)', code)
        imports[name] = prefixes
        if any(p not in ['Stdlib', 'CyclistRocq.LPL', 'CyclistRocq.Cyclic'] and
               not p.startswith(('Stdlib.', 'CyclistRocq.LPL.', 'CyclistRocq.Cyclic.')) for p in prefixes):
            violations[name] = 'Unexpected object theory or external library'
        if 'CyclistRocq.LPL.Core' in code:
            violations[name] = 'Obsolete namespace'
        if (path.parent == HERE or name == 'PPL/Instance.v') and 'CyclistRocq.LPL.FOPL' in code:
            violations[name] = 'Generic implementation depends on FOPL'
        if 'LegacyReference' in code and 'LegacyReference' not in path.parts and name != 'FOPL/Compatibility.v':
            violations[name] = 'Production code depends on the preservation oracle'
    duplicates = [v for v in groups.values() if len(v) > 1]
    require(not duplicates, f'Byte-identical source files: {duplicates}')
    require(not violations, f'Source audit violations: {violations}')
    shared_signature = (HERE / 'FOPL/Signature.v').read_bytes() == (ROOT / 'LPL-old/Signature.v').read_bytes()
    require(shared_signature, 'Shared first-order signature differs from the immutable reference')
    oracle = {}
    for name in ['Syntax', 'Semantics', 'Progress']:
        original = (ROOT / 'LPL-old' / (name + '.v')).read_text()
        adapted = re.sub(r'From CyclistRocq\.LPL Require Import ([\w\s]+)\.', legacy_import, original)
        oracle[name] = adapted == (HERE / 'FOPL/LegacyReference' / (name + '.v')).read_text()
    require(all(oracle.values()), 'Legacy reference changed beyond its import adaptation')
    report = json.loads((HERE / 'BENCHMARK_RESULTS.json').read_text())
    source_hashes = {str(p.relative_to(HERE)): digest(p) for p in sources}
    require(report['source_sha256'] == source_hashes, 'Benchmark report is stale')
    benchmarks = report['benchmarks']
    require(report.get('status') == 'passed' and len(benchmarks) == 29 and all(
        r['exit_status'] == 0 and r['elapsed_seconds'] < 600 for r in benchmarks), 'The full benchmark suite has not passed')
    units = {(r['suite'], r['benchmark']): r for r in benchmarks}
    require(set(units) == {('fopl', n) for n in FOPL_BENCHMARKS} | {('ppl', n) for n in PPL_BENCHMARKS},
            'Missing or duplicated benchmark units')
    require(units['fopl', 'RuleCoverage']['checked_premise_shape_examples'] == 50 and
            units['ppl', 'RuleCoverage']['checked_premise_shape_examples'] == 53, 'Rule coverage changed')
    records = report['common_build'] + benchmarks
    require({r['source'] for r in report['common_build']} == set(COMMON), 'Missing common build records')
    cache = json.loads((HERE / '.build/build-cache.json').read_text())
    for record in records:
        source = HERE / record['source']
        require(record['source_sha256'] == digest(source), f'Stale source record: {source}')
        require(source.with_suffix('.vo').is_file(), f'Missing compiled module: {source}')
        entry = cache[record['source']]
        require(entry['source'] == digest(source) and entry['artifact'] == digest(source.with_suffix('.vo')) and
                entry['compiler'] == report['compiler'] and entry['flags'] == COQ_FLAGS, f'Stale build cache: {source}')
        for dependency, value in record['dependency_sha256'].items():
            require(value == digest((ROOT / dependency).with_suffix('.vo')), f'Stale dependency: {dependency}')
    preservation = {}
    pattern = r'^\s*(Theorem|Lemma|Example)\s+(\w+)\b(.*?)\s*Proof\.'
    statements = lambda text: [(kind, name, ' '.join(body.split())) for kind, name, body in re.findall(
        pattern, text, re.MULTILINE | re.DOTALL)]
    for name in FOPL_BENCHMARKS:
        old = statements((ROOT / 'LPL-old/Benchmarks' / (name + '.v')).read_text())
        new = iter(statements((HERE / 'FOPL/Benchmarks' / (name + '.v')).read_text()))
        retained = all(any(candidate == item for candidate in new) for item in old)
        require(retained, f'Original benchmark statement missing: {name}')
        preservation[name] = {'original_statements': len(old), 'all_retained_in_order': True}
    for name in ['build.py', 'run_benchmarks.py', 'check_integrity.py']:
        ast.parse((HERE / name).read_text())
    save(logs, 'SourceAudit.json', {'source_count': len(sources), 'source_sha256': source_hashes,
         'common_build_count': len(COMMON), 'duplicates': duplicates, 'violations': violations,
         'imports': imports, 'shared_signature_matches_frozen_reference': shared_signature,
         'reference_import_only': oracle, 'build_and_project_inventories_complete': True})
    save(logs, 'BenchmarkPreservation.json', preservation)
    return sources


def audit_scope(logs):
    baseline_path = logs / 'OutsideBaseline.json'
    if not baseline_path.exists():
        return
    baseline = json.loads(baseline_path.read_text())
    workspace = ROOT.parent
    paths = subprocess.run(['rg', '--files', '--hidden', '--no-ignore', '-g', '!.git/**'],
        cwd=workspace, check=True, text=True, stdout=subprocess.PIPE).stdout.splitlines()
    current = {p: digest(workspace / p) for p in paths if not p.startswith('Rocq-copy/LPL/')}
    record = {'baseline_files': len(baseline), 'current_files': len(current),
              'added': sorted(current.keys() - baseline.keys()), 'missing': sorted(baseline.keys() - current.keys()),
              'changed': sorted(p for p in baseline.keys() & current.keys() if baseline[p] != current[p])}
    save(logs, 'OutsideAudit.json', record)
    require(not any(record[k] for k in ['added', 'missing', 'changed']), f'Outside-scope differences: {record}')


def audit_documents(logs):
    missing, count = [], 0
    for path in HERE.glob('*.md'):
        text = re.sub(r'```.*?```|`[^`]*`', '', path.read_text(), flags=re.DOTALL)
        for target in re.findall(r'\[[^\]]+\]\(([^)]+)\)', text):
            if target.startswith(('http:', 'https:', '#')):
                continue
            count += 1
            if not (path.parent / target.split('#')[0]).exists():
                missing.append([path.name, target])
    save(logs, 'DocumentationLinks.json', {'checked_local_links': count, 'missing': missing})
    require(not missing, f'Broken documentation links: {missing}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel', action='store_true')
    parser.add_argument('--scope', action='store_true', help='Compare outside files with the cleanup baseline')
    parser.add_argument('--log-dir', type=Path)
    args = parser.parse_args()
    cleanup_file = HERE / 'CLEANUP.json'
    default_logs = json.loads(cleanup_file.read_text())['log_dir'] if cleanup_file.exists() else 'validation-logs/current'
    logs = inside(args.log_dir or HERE / default_logs)
    logs.mkdir(parents=True, exist_ok=True)
    sources = audit_sources(logs)
    if args.scope:
        audit_scope(logs)
    if args.kernel:
        modules = ['CyclistRocq.LPL.' + '.'.join(p.relative_to(HERE).with_suffix('').parts) for p in sources]
        command = ['timeout', '--signal=KILL', '600s', 'rocq', 'check', '-silent', '-Q', '..', 'CyclistRocq', *modules]
        start = time.monotonic()
        with (logs / 'KernelCheck.log').open('w') as output:
            result = subprocess.run(command, cwd=HERE, stdout=output, stderr=subprocess.STDOUT)
        save(logs, 'KernelCheck.json', {'command': command, 'cwd': str(HERE), 'module_count': len(modules),
             'exit_code': result.returncode, 'elapsed_seconds': round(time.monotonic() - start, 3),
             'scope': 'All project modules and recursive dependencies', 'log': 'KernelCheck.log'})
        require(result.returncode == 0, f'Independent kernel check failed: {logs / "KernelCheck.log"}')
    audit_documents(logs)
    subprocess.run(['git', 'diff', '--check', '--', 'Rocq-copy/LPL'], cwd=ROOT.parent, check=True)
    print(f'Integrity checks pass: {len(sources)} sources, 29 benchmarks, complete build graph and frozen-reference preservation.')


if __name__ == '__main__':
    main()
