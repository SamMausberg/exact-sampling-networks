#!/usr/bin/env python3
"""Build the Lean development, audit its axioms, and check its paper references.

Run from this directory after `lake exe cache get`. The script
1. scans the Lean sources for forbidden tokens,
2. checks that `ExactSampling.lean` imports every module under `ExactSampling/`,
3. runs `lake build` (warnings are errors, see lakefile.toml),
4. runs `AxiomAudit.lean`, which enumerates every declaration of the library, and checks that
   each one depends only on `propext`, `Classical.choice` and `Quot.sound`,
5. checks that every TeX label cited in a docstring exists in a file that is compiled into
   `paper/conference.pdf` or `paper/exact_sampling_networks.pdf`.
It writes the results to lean-verification.json.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PAPER = ROOT.parent / "paper"
ENTRY_POINTS = ["conference.tex", "exact_sampling_networks.tex"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [
    r"\bsorry\b",
    r"\badmit\b",
    r"\baxiom\b",
    r"\bnative_decide\b",
    r"\bimplemented_by\b",
    r"\bunsafe\b",
    r"@\[extern",
    r"\bopaque\b",
    r"maxHeartbeats\s+0\b",
]
LABEL = re.compile(
    r"`((?:thm|lem|prop|cor|eq|sec|app|def|rem|tab|fig|page|alg|ex|subsec)"
    r":[A-Za-z0-9:_.\-]+)`"
)


def strip_comments(text: str) -> str:
    """Remove Lean comments and keep every newline, so line numbers are preserved.

    Block comments `/- ... -/` (including `/--` and `/-!`) nest. Line comments run from `--`
    to the end of the line. String literals are copied unchanged.
    """
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i : j + 1])
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def modules() -> list[Path]:
    return sorted((ROOT / "ExactSampling").rglob("*.lean"))


def scan() -> list[str]:
    hits = []
    for path in modules() + [ROOT / "ExactSampling.lean"]:
        text = path.read_text()
        raw = text.splitlines()
        code = strip_comments(text).splitlines()
        for lineno, line in enumerate(code, 1):
            for pattern in FORBIDDEN:
                if re.search(pattern, line):
                    hits.append(f"{path.relative_to(ROOT)}:{lineno}: {raw[lineno - 1].strip()}")
    return hits


def style() -> list[str]:
    """Lines of at most 100 characters, no tabs, no trailing whitespace, final newline."""
    issues = []
    for path in modules() + [ROOT / "ExactSampling.lean", ROOT / "AxiomAudit.lean"]:
        text = path.read_text()
        rel = path.relative_to(ROOT)
        if text and not text.endswith("\n"):
            issues.append(f"{rel}: missing final newline")
        for lineno, line in enumerate(text.splitlines(), 1):
            if len(line) > 100:
                issues.append(f"{rel}:{lineno}: line longer than 100 characters")
            if "\t" in line:
                issues.append(f"{rel}:{lineno}: tab character")
            if line != line.rstrip():
                issues.append(f"{rel}:{lineno}: trailing whitespace")
    return issues


def import_mismatch() -> dict[str, list[str]]:
    expected = {".".join(p.relative_to(ROOT).with_suffix("").parts) for p in modules()}
    root = (ROOT / "ExactSampling.lean").read_text()
    imported = set(re.findall(r"^import\s+(ExactSampling\.\S+)", root, re.M))
    return {
        "not_imported": sorted(expected - imported),
        "missing_file": sorted(imported - expected),
    }


def compiled_tex() -> list[Path]:
    """TeX files reachable from the two entry points through \\input or \\include."""
    seen: list[Path] = []
    stack = [PAPER / e for e in ENTRY_POINTS]
    while stack:
        path = stack.pop()
        if path in seen or not path.exists():
            continue
        seen.append(path)
        text = re.sub(r"(?<!\\)%.*", "", path.read_text())
        for name in re.findall(r"\\(?:input|include)\{([^}]+)\}", text):
            child = PAPER / name
            stack.append(child if child.suffix == ".tex" else child.with_suffix(".tex"))
    return seen


def paper_labels() -> dict[str, str]:
    labels = {}
    for path in compiled_tex():
        text = re.sub(r"(?<!\\)%.*", "", path.read_text())
        for label in re.findall(r"\\label\{([^}]+)\}", text):
            labels[label] = path.name
    return labels


def run(cmd: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)


def parse_audit(output: str) -> list[dict]:
    decls = []
    for line in output.splitlines():
        m = re.search(r"AUDIT (\S+) \| (\w+) \| (user|aux) \| ([^|]*) \| (.*)$", line)
        if m:
            name, kind, origin, axioms, doc = m.groups()
            decls.append(
                {
                    "name": name,
                    "kind": kind,
                    "user": origin == "user",
                    "axioms": [a.strip() for a in axioms.split(",") if a.strip()],
                    "doc": doc.strip(),
                }
            )
    return decls


def main() -> int:
    hits = scan()
    style_issues = style()
    mismatch = import_mismatch()
    build = run(["lake", "build"])
    audit_run = run(["lake", "env", "lean", "AxiomAudit.lean"])
    decls = parse_audit(audit_run.stdout)
    total = re.search(r"AUDIT-TOTAL (\d+)", audit_run.stdout)
    labels = paper_labels()

    theorems = [d for d in decls if d["kind"] == "theorem" and d["user"]]
    non_standard = {d["name"]: d["axioms"] for d in decls if not set(d["axioms"]) <= ALLOWED}
    label_map: dict[str, list[str]] = defaultdict(list)
    unknown: dict[str, list[str]] = defaultdict(list)
    for d in theorems:
        for label in sorted(set(LABEL.findall(d["doc"]))):
            if label in labels:
                label_map[label].append(d["name"])
            else:
                unknown[label].append(d["name"])
    cited = [d for d in theorems if LABEL.search(d["doc"])]

    ok = (
        not hits
        and not style_issues
        and not mismatch["not_imported"]
        and not mismatch["missing_file"]
        and build.returncode == 0
        and audit_run.returncode == 0
        and total is not None
        and int(total.group(1)) == len(decls)
        and not non_standard
        and not unknown
    )
    report = {
        "status": "passed" if ok else "failed",
        "forbidden_tokens": hits,
        "style_issues": style_issues,
        "import_mismatch": mismatch,
        "build_returncode": build.returncode,
        "modules": len(modules()),
        "audited_declarations": len(decls),
        "user_theorems": len(theorems),
        "theorems_citing_paper_labels": len(cited),
        "paper_labels_cited": len(label_map),
        "unknown_labels": dict(unknown),
        "non_standard_axioms": non_standard,
        "labels": {k: sorted(v) for k, v in sorted(label_map.items())},
        "theorems": {d["name"]: d["axioms"] for d in theorems},
    }
    (ROOT / "lean-verification.json").write_text(json.dumps(report, indent=2) + "\n")
    summary = {
        k: report[k]
        for k in (
            "status",
            "modules",
            "audited_declarations",
            "user_theorems",
            "theorems_citing_paper_labels",
            "paper_labels_cited",
            "forbidden_tokens",
            "style_issues",
            "import_mismatch",
            "unknown_labels",
            "non_standard_axioms",
        )
    }
    print(json.dumps(summary, indent=2))
    if build.returncode != 0:
        print(build.stdout[-6000:], build.stderr[-2000:], file=sys.stderr)
    if audit_run.returncode != 0:
        print(audit_run.stdout[-3000:], audit_run.stderr[-2000:], file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
