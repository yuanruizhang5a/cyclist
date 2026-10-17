#!/usr/bin/env python3
"""Build only LPL sources; never invoke or modify the parent build files."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
COQ_FLAGS = ["-Q", "..", "CyclistRocq", "-noglob"]
CORE = [f"{name}.v" for name in
        ("Signature", "Syntax", "Semantics", "Progress", "Rules", "RuleGeneration", "Certification")]
FOPL = [f"FOPL/{name}.v" for name in
        ("Signature", "Syntax", "Semantics", "Progress", "Rules", "RuleGeneration", "Certification")]
REFERENCE = [f"FOPL/LegacyReference/{name}.v" for name in
             ("Syntax", "Semantics", "Progress")]
FOPL_BENCHMARKS = ["Labels", "Signatures", "Updates", "Tests", "RegularPrograms", "Booleans",
                   "Quantifiers", "Temporal", "AssignmentChange", "RuleCoverage", "CheckerNegative",
                   "Cyclic", "CyclicTags", "CounterLoop", "NestedProgram"]
PPL_BENCHMARKS = ["Instances", "LabelsRelations", "AtomicActions", "Nondeterminism", "Booleans",
                  "Tests", "RegularPrograms", "Temporal", "RuleCoverage", "CheckerNegative",
                  "Cyclic", "CyclicTags", "SafetySystem", "NestedProgram"]
COMMON = CORE + ["TraceSafety.v", "PPL/Instance.v"] + FOPL + REFERENCE + [
    "FOPL/Compatibility.v", "FOPL/Benchmarks/Support.v",
    "Benchmarks/PPL/Support.v"]
IMPORTS = re.compile(r"From\s+(CyclistRocq(?:\.\w+)+)\s+Require\s+(?:Import|Export)\s+([\w\s]+)\.")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inside(path: Path) -> Path:
    path = path.resolve()
    if not path.is_relative_to(HERE):
        raise ValueError(f"Output/source must stay inside {HERE}: {path}")
    return path


def dependencies(source: Path) -> list[Path]:
    result = []
    for prefix, names in IMPORTS.findall(source.read_text()):
        for name in names.split():
            parts = (prefix + "." + name).split(".")[1:]
            dependency = ROOT.joinpath(*parts).with_suffix(".v")
            if dependency not in result:
                result.append(dependency)
    return result


class Builder:
    def __init__(self, logs: Path | None = None):
        self.logs = inside(logs or HERE / ".build/build-logs")
        self.logs.mkdir(parents=True, exist_ok=True)
        self.cache_path = HERE / ".build/build-cache.json"
        self.cache = json.loads(self.cache_path.read_text()) if self.cache_path.exists() else {}
        self.version = subprocess.run(["rocq", "--version"], text=True, stdout=subprocess.PIPE, check=True).stdout.strip()
        self.built: set[Path] = set()
        self.active: set[Path] = set()

    def compile(self, source: Path, *, force: bool = False) -> dict:
        source = inside(source)
        if not source.is_file():
            raise FileNotFoundError(source)
        if source in self.active:
            raise RuntimeError(f"Dependency cycle: {source}")
        self.active.add(source)
        try:
            return self._compile(source, force=force)
        finally:
            self.active.remove(source)

    def _compile(self, source: Path, *, force: bool) -> dict:
        deps = dependencies(source)
        for dep in deps:
            if dep.is_relative_to(HERE):
                if dep not in self.built:
                    self.compile(dep)
            elif not dep.with_suffix(".vo").is_file():
                raise RuntimeError(f"Immutable dependency needs an LPL-local staged build: {dep}")
        key = str(source.relative_to(HERE))
        signature = {"compiler": self.version, "cwd": str(HERE), "flags": COQ_FLAGS, "source": digest(source), "dependencies": {
            str(dep.relative_to(ROOT)): digest(dep.with_suffix(".vo")) for dep in deps}}
        vo = source.with_suffix(".vo")
        if not force and vo.exists() and self.cache.get(key) == dict(signature, artifact=digest(vo)):
            self.built.add(source)
            return {"source": key, "cached": True, "exit_status": 0,
                    "compiler": self.version, "cwd": str(HERE),
                    "source_sha256": signature["source"],
                    "dependency_sha256": signature["dependencies"],
                    "artifact_sha256": digest(vo)}
        command = ["timeout", "--signal=KILL", "600s", "rocq", "compile", *COQ_FLAGS,
                   str(source.relative_to(HERE))]
        start = time.monotonic()
        result = subprocess.run(command, cwd=HERE, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - start
        log = self.logs / (key.replace("/", "-") + ".txt")
        log.write_text(result.stdout)
        record = {"source": key, "cached": False, "command": command, "cwd": str(HERE),
                  "elapsed_seconds": elapsed, "exit_status": result.returncode,
                  "timeout": result.returncode in (124, 137, -9), "source_sha256": signature["source"],
                  "dependency_sha256": signature["dependencies"], "log": str(log.relative_to(HERE))}
        log.with_suffix(".json").write_text(json.dumps(record, indent=2) + "\n")
        print(f"{key}: exit {result.returncode}, {elapsed:.3f}s", flush=True)
        if result.returncode:
            print(result.stdout, end="", flush=True)
            raise BuildFailure(record)
        self.cache[key] = dict(signature, artifact=digest(vo))
        self.cache_path.parent.mkdir(parents=True, exist_ok=True)
        self.cache_path.write_text(json.dumps(self.cache, indent=2, sort_keys=True) + "\n")
        self.built.add(source)
        return record

    def common(self):
        return [self.compile(HERE / source) for source in COMMON]


class BuildFailure(RuntimeError):
    def __init__(self, record: dict):
        super().__init__(f"Compilation failed: {record['source']}")
        self.record = record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common", action="store_true")
    parser.add_argument("--target", action="append", default=[])
    args = parser.parse_args()
    builder = Builder()
    try:
        if args.common or not args.target:
            builder.common()
        for source in args.target:
            builder.compile(HERE / source, force=True)
    except (BuildFailure, FileNotFoundError, RuntimeError, ValueError) as error:
        print(error)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
