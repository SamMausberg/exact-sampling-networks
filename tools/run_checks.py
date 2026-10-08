#!/usr/bin/env python3
"""Rerun the recorded finite checks and compare them with their recorded outputs.

Every script in `paper/checks/` that writes a JSON record is run in a temporary copy of the
directory, and the fresh JSON must be byte-identical to the recorded file. The checkpoint
worksheet is run on both bundled inputs and its output must equal the recorded output as JSON.
`document_structure.py` is skipped: it inspects built PDFs, not mathematics.

Usage: python tools/run_checks.py [--only NAME ...] [--timeout SECONDS]
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHECKS = ROOT / "paper" / "checks"
SKIP = {"document_structure.py", "checkpoint_cost_worksheet.py"}
WORKSHEETS = {
    "checkpoint_illustrative_input.json": "checkpoint_illustrative_output.json",
    "checkpoint_hadamard_input.json": "checkpoint_hadamard_output.json",
}


def run_script(script: Path, cwd: Path, timeout: int, args: list[str] | None = None):
    start = time.monotonic()
    proc = subprocess.run(
        [sys.executable, "-I", str(script), *(args or [])],
        cwd=cwd,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    return proc, time.monotonic() - start


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--only", nargs="*", help="script names to run (default: all)")
    parser.add_argument("--timeout", type=int, default=1200)
    opts = parser.parse_args()

    scripts = sorted(p for p in CHECKS.glob("*.py") if p.name not in SKIP)
    if opts.only:
        scripts = [p for p in scripts if p.name in opts.only or p.stem in opts.only]
    failures: list[str] = []
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp) / "checks"
        shutil.copytree(CHECKS, work)
        recorded = {p.name: p.read_bytes() for p in CHECKS.glob("*.json")}
        before = {p.name: p.stat().st_mtime_ns for p in work.glob("*.json")}
        for script in scripts:
            proc, seconds = run_script(work / script.name, work, opts.timeout)
            status = "ok" if proc.returncode == 0 else f"exit {proc.returncode}"
            print(f"{script.name:45s} {status:8s} {seconds:6.1f}s", flush=True)
            if proc.returncode != 0:
                failures.append(f"{script.name}: {proc.stderr.strip()[-500:]}")
        for path in sorted(work.glob("*.json")):
            if path.name in WORKSHEETS.values() or path.name in WORKSHEETS:
                continue
            if before.get(path.name) == path.stat().st_mtime_ns and not opts.only:
                continue
            if path.name in recorded and path.read_bytes() != recorded[path.name]:
                failures.append(f"{path.name}: differs from the recorded output")
        if not opts.only:
            worksheet = work / "checkpoint_cost_worksheet.py"
            for source, expected in WORKSHEETS.items():
                proc, seconds = run_script(
                    worksheet, work.parent, opts.timeout, [str(work / source)]
                )
                same = proc.returncode == 0 and json.loads(proc.stdout) == json.loads(
                    recorded[expected]
                )
                print(f"worksheet {source:35s} {'ok' if same else 'MISMATCH':8s} {seconds:6.1f}s")
                if not same:
                    failures.append(f"worksheet {source}: output differs from {expected}")
    if failures:
        print("\nFAILED:\n" + "\n".join(failures))
        return 1
    print("\nAll recorded outputs reproduced.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
