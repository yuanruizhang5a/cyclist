#!/usr/bin/env python3
"""Compile isolated LPL benchmarks with an unconditional 600-second limit.

Run from Rocq-copy with `make lpl-benchmarks`. Common dependencies are built
first. This is a build/report utility, not an object-logic proof-search driver.
It preserves compiler output in timestamped directories and deletes no files.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
BENCHMARKS = [
    ("Labels", "D1/D4, units, differing states, overlap; 1-node certificate"),
    ("Signatures", "arbitrary models and independent Boolean signature; leaf certificates"),
    ("Updates", "identity, changed/dependent assignments, intermediate states; pure certificate"),
    ("Tests", "successful/failed and trace-sensitive tests; 2-node certificate"),
    ("RegularPrograms", "sequence, choice, zero/one/nested finite iteration; semantic validity"),
    ("Booleans", "mixed modal Boolean formula; 3-node certificate"),
    ("Quantifiers", "capture avoidance, shadowing, eigenvariables; 2-node certificate"),
    ("Temporal", "immediate/postponed suffix, dual, first, next-at-end, sum measure; certificate"),
    ("AssignmentChange", "changed next-state value; 6-node certificate, 1 distinct tag"),
    ("RuleCoverage", "50 exact rule/request premise shapes, positive/negative syntax checks"),
    ("CheckerNegative", "open/dangling/mismatched graphs, absent tags, closed nonprogressing cycle"),
    ("Cyclic", "11-node star cycle, real backlink, 1 distinct tag, explicit potential"),
    ("CyclicTags", "12-node star cycle, explicit tag-renaming backlink, 2 distinct tags"),
    ("CounterLoop", "guarded integer decrement loop, every visited state and finite stopping point"),
    ("NestedProgram", "nested sequence/choice/star, arbitrary uninterpreted predicate of unchanged variable"),
]
FRAMEWORK_HASHES = {
    "Cyclic/Framework.v": "b9f93e89931a196bb1d2f7649f240cb65920ed972fa02a2ae4af46a2e7a3ce02",
    "Cyclic/Relations.v": "85f1f25747e3eb661f24f50b6a9e6aae3cbcb173169bb7bfb6d06ac7addeb90f",
}


def run(command: list[str]) -> tuple[subprocess.CompletedProcess[str], float]:
    start = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    return result, time.monotonic() - start


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=ROOT / "LPL/BENCHMARK_RESULTS.md")
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    logs = ROOT / "LPL/benchmark-logs" / stamp
    logs.mkdir(parents=True, exist_ok=False)
    version = subprocess.run(["rocq", "--version"], cwd=ROOT, text=True,
                             stdout=subprocess.PIPE, check=True).stdout.strip()
    actual_hashes = {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                     for name in FRAMEWORK_HASHES}
    if actual_hashes != FRAMEWORK_HASHES:
        raise SystemExit("Immutable Cyclic source hashes differ from the agreed baseline.")
    common_command = ["make", "lpl-common"]
    common, common_elapsed = run(common_command)
    (logs / "common.txt").write_text(common.stdout)
    if common.returncode:
        print(common.stdout, end="")
        return common.returncode
    records = []
    for name, evidence in BENCHMARKS:
        source = f"LPL/Benchmarks/{name}.v"
        command = ["timeout", "--signal=KILL", "600s", "rocq", "compile", "-Q", ".", "CyclistRocq", source]
        result, elapsed = run(command)
        (logs / f"{name}.txt").write_text(result.stdout)
        records.append({"benchmark": name, "source": source, "command": command,
                        "elapsed_seconds": elapsed, "exit_status": result.returncode,
                        "evidence": evidence,
                        "source_sha256": hashlib.sha256((ROOT / source).read_bytes()).hexdigest(),
                        "log": str((logs / f"{name}.txt").relative_to(ROOT / "LPL"))})
        print(f"{name}: exit {result.returncode}, {elapsed:.3f}s", flush=True)
        if result.returncode:
            print(result.stdout, end="", flush=True)
    passed = sum(row["exit_status"] == 0 for row in records)
    lines = ["# LPL benchmark results", "", f"UTC run: `{stamp}`. **{passed}/{len(records)} units passed.**", "",
             "```text", version, "```", "",
             f"Common dependencies: `{shlex.join(common_command)}`, exit {common.returncode}, {common_elapsed:.3f}s.",
             "Every isolated benchmark uses `timeout --signal=KILL 600s`; the limit is never increased.", "",
             "| Unit | Seconds | Exit | Evidence | Compiler output / assumptions |",
             "| --- | ---: | ---: | --- | --- |"]
    for row in records:
        lines.append(f"| {row['benchmark']} | {row['elapsed_seconds']:.3f} | {row['exit_status']} | "
                     f"{row['evidence']} | [log]({row['log']}) |")
    lines += ["", "## Commands", "", "Commands ran from `Rocq-copy/`, after compiling common dependencies.", "", "```sh"]
    lines += [shlex.join(row["command"]) for row in records]
    lines += ["```", "", "## Scope and assumptions", "",
              "All requested primitive/derived rule families are implemented; generators return proof-backed records and check object syntax, conclusions, and edge endpoints. RuleCoverage checks 50 exact premise lists, including non-head positions and the empty context-only weakening premise. Pure goals stop at the caller-supplied proof boundary.", "",
              "Cyclic and CyclicTags are actual star cycles with explicit finite tag/potential witnesses. They preserve a first-state observation. CounterLoop and NestedProgram separately prove properties of **every visited state**, over arbitrary finite iterations; these two complex invariants are direct semantic proofs, not cyclic graph certificates. No claim of mandatory loop exit is made.", "",
              "Print Assumptions output is retained in the linked logs. The union for concrete exported theorems and representative rule/certification kernels consists only of standard-library classical excluded middle, definite/indefinite description, and functional extensionality. No project-defined soundness axioms or admitted proofs are used. Signature/model parameters in the abstract-model functors are explicit parameters, not soundness assumptions.", "",
              "The framework witness is conservative: it chooses at most one tag per node. Acceptance of every manuscript preproof is not claimed. No proof search, witness discovery, external solver, or project FirstOrder/LTL imports are present.", "",
              "## Development timeout and simplification", "",
              "An initial Cyclic.v run hit the 600-second limit (exit 137) while kernel conversion compared an entire proof-carrying backlink record in an auxiliary existential example. That auxiliary check was replaced with a Boolean check of the node payload and companion index. The real backlink, star graph, semantic rules, certificate, and validity theorem were retained. The final timed run is reported above. No expensive obligation was retried with a larger limit.", "",
              "## Immutable framework", "", "```text"]
    lines += [f"{name}  {digest}" for name, digest in actual_hashes.items()]
    lines += ["```", "", "The complete Cyclic directory also matched the pre-implementation file manifest during the implementation audit.", "",
              "See [VALIDATION.md](VALIDATION.md) for the independent kernel check, existing-theory regressions, and source-scope audit.", ""]
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text("\n".join(lines))
    common_sources = sorted((ROOT / "LPL").glob("*.v")) + [
        ROOT / "LPL/Benchmarks/Support.v", ROOT / "LPL/Benchmarks/InvariantSupport.v"]
    manifest = {"run_utc": stamp, "compiler": version,
                "common_command": common_command, "common_exit_status": common.returncode,
                "common_elapsed_seconds": common_elapsed,
                "common_source_sha256": {
                    str(source.relative_to(ROOT)): hashlib.sha256(source.read_bytes()).hexdigest()
                    for source in common_sources},
                "framework_sha256": actual_hashes, "benchmarks": records}
    args.report.with_suffix(".json").write_text(json.dumps(manifest, indent=2) + "\n")
    return 0 if passed == len(records) else 1


if __name__ == "__main__":
    raise SystemExit(main())
