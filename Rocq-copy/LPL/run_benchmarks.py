#!/usr/bin/env python3
"""Run both process-logic suites with a hard 600-second limit per unit."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess
from build import Builder, BuildFailure, HERE, ROOT, FOPL_BENCHMARKS, PPL_BENCHMARKS, inside, digest


def proof_mode(suite: str, name: str) -> str:
    if name in ('Cyclic', 'CyclicTags'):
        return 'cyclic certificate'
    if name in ('CounterLoop', 'NestedProgram', 'SafetySystem', 'Nondeterminism', 'RegularPrograms', 'Instances'):
        return 'semantic proof / instance checks'
    if name in ('RuleCoverage', 'CheckerNegative', 'LabelsRelations'):
        return 'syntax / rule / checker checks'
    return 'semantic proof / generated certificate'


def execution_evidence(source_text: str) -> list[dict]:
    """Record checked statements, retaining conditional and negative cases."""
    statements = re.findall(
        r'\b(?:Example|Lemma|Theorem)\s+(\w+)\b(.*?)\.\s*Proof\.',
        source_text, flags=re.DOTALL)
    return [{'name': name, 'statement': ' '.join(statement.split())}
            for name, statement in statements
            if re.search(r'\b(?:admissible|left_holds|relations_hold|program_holds)\b', statement)]


def write_reports(report: Path, stamp: str, version: str, records: list[dict], common: list[dict],
                  common_failure: dict | None = None):
    passed = sum(r['exit_status'] == 0 for r in records)
    manifest = {'run_utc': stamp, 'compiler': version, 'benchmark_limit_seconds': 600,
                'status': 'failed' if common_failure or passed != len(records) else 'passed',
                'common_failure': common_failure,
                'common_build': common, 'benchmarks': records,
                'source_sha256': {str(p.relative_to(HERE)): digest(p)
                                  for p in HERE.rglob('*.v') if '.build' not in p.parts},
                'immutable_framework_sha256': {n: digest(ROOT / n)
                    for n in ('Cyclic/Framework.v', 'Cyclic/Relations.v')}}
    report.with_suffix('.json').write_text(json.dumps(manifest, indent=2) + '\n')
    outcome = ('**common build failed; benchmarks were not run**' if common_failure else
               f'**{passed}/{len(records)} attempted units passed**')
    lines = ['# Refinement benchmark results', '', f'UTC run `{stamp}`: {outcome}.', '',
             'Every unit was compiled with `timeout --signal=KILL 600s` after its dependencies. '
             'These records describe this run only; earlier reports/logs are historical evidence.', '',
             '```text', version, '```', '',
             '| Suite | Unit | Seconds | Exit | Proof mode | Output / assumptions |',
             '| --- | --- | ---: | ---: | --- | --- |']
    for r in records:
        lines.append(f"| {r['suite']} | {r['benchmark']} | {r.get('elapsed_seconds', 0):.3f} | "
                     f"{r['exit_status']} | {r['proof_mode']} | [log]({r['log']}) |")
    lines += ['', '## Checked coverage and graph sizes', '',
              '| Suite | Unit | Premise-shape examples | Graph/tag measurements |',
              '| --- | --- | ---: | --- |']
    for r in records:
        if r['checked_premise_shape_examples'] or r['checked_graph_metrics']:
            measurements = ', '.join(f'{key}={value}' for key, value in r['checked_graph_metrics'].items())
            lines.append(f"| {r['suite']} | {r['benchmark']} | {r['checked_premise_shape_examples']} | {measurements} |")
    lines += ['', '## Commands', '', 'Commands ran from `Rocq-copy/LPL/`.', '', '```sh']
    import shlex
    lines += [shlex.join(r['command']) for r in records]
    lines += ['```', '', '## Evidence and limits', '',
              'The source hashes and dependency hashes are retained in the JSON report. '
              '`Print Assumptions` output is in each compiler log; exported names are also listed in JSON. '
              'The JSON records admissibility, antecedent, relation, and execution example statements '
              'as nonvacuity evidence, retaining their conditions and negative cases. '
              'Concrete checker computations and semantic examples are distinguished from validity theorems in the source.', '',
              'Cyclic/CyclicTags require real backlinks and explicit finite tag/potential witnesses. '
              'The complex all-visited-state invariants use direct semantic proofs. '
              'The framework selects at most one tag per node; acceptance of every manuscript preproof is not claimed.', '',
              'T1 is resolved by the user: tests evaluate their guard on `[s; s]`. '
              'No benchmark is allowed to increase the 600-second cap. Failed/timed-out cases remain failures in this record.', '']
    report.write_text('\n'.join(lines))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--suite', choices=['fopl', 'ppl', 'all'], default='all')
    parser.add_argument('--report', type=Path, default=HERE / 'BENCHMARK_RESULTS.md')
    args = parser.parse_args()
    report = inside(args.report)
    report.parent.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    logs = HERE / 'benchmark-logs' / ('refine-' + stamp)
    logs.mkdir(parents=True)
    version = subprocess.run(['rocq', '--version'], text=True, stdout=subprocess.PIPE, check=True).stdout.strip()
    builder = Builder(logs)
    try:
        common = builder.common()
    except (BuildFailure, RuntimeError, FileNotFoundError) as error:
        print(error)
        (logs / 'CommonFailure.txt').write_text(str(error) + '\n')
        failure = dict(getattr(error, 'record', {}), message=str(error),
                       failure_log=str((logs / 'CommonFailure.txt').relative_to(HERE)))
        write_reports(report, stamp, version, [], [], common_failure=failure)
        return 1
    records = []
    suites = [('fopl', FOPL_BENCHMARKS, 'FOPL/Benchmarks'), ('ppl', PPL_BENCHMARKS, 'Benchmarks/PPL')]
    for suite, names, directory in suites:
        if args.suite not in (suite, 'all'):
            continue
        for name in names:
            source = HERE / directory / (name + '.v')
            try:
                record = builder.compile(source, force=True)
            except BuildFailure as error:
                record = dict(error.record)
                if record['source'] != str(source.relative_to(HERE)):
                    record['failed_dependency'] = record['source']
                    record['requested_source'] = str(source.relative_to(HERE))
            source_text = source.read_text()
            metrics = {metric: int(value) for metric, expression, value in re.findall(
                r'(?:Example|Lemma)\s+(\w+)\s*:\s*List\.length\s+([^=]+)=\s*(\d+)\.', source_text)
                if 'graph_nodes' in expression or 'all_graph_tags' in expression}
            record.update(suite=suite, benchmark=name, proof_mode=proof_mode(suite, name),
                          checked_graph_metrics=metrics if record['exit_status'] == 0 else {},
                          checked_premise_shape_examples=(len(re.findall(r'Example\s+\w+\s*:\s*has_shape\b', source_text))
                                                         if record['exit_status'] == 0 else 0),
                          nonvacuity_evidence=(execution_evidence(source_text) if record['exit_status'] == 0 else []),
                          assumption_theorems=re.findall(r'Print\s+Assumptions\s+([\w.]+)\s*\.', source.read_text()))
            records.append(record)
            write_reports(report, stamp, version, records, common)
    return 0 if all(r['exit_status'] == 0 for r in records) else 1


if __name__ == '__main__':
    raise SystemExit(main())
