#!/usr/bin/env python3
"""Check document structure and optional PDF metadata, not mathematical truth.

Uses the Python standard library. If PyMuPDF is installed, it also records
page counts, PDF integrity, figures, and text outside the physical page.
The Lean formalization is checked separately by formalization/verify.py.
The script exits with status 1 if it finds a structural problem.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import re
from pathlib import Path


def clean_comments(source: str) -> str:
    return re.sub(r"(?<!\\)%[^\n]*", "", source)


def collect(root: Path, entry: str):
    records = []

    def visit(path: Path, ancestors: tuple[Path, ...]):
        path = path.resolve()
        if path in ancestors:
            raise ValueError(f"Cyclic TeX input at {path}")
        raw = path.read_text(encoding="utf-8")
        source = clean_comments(raw)
        records.append((path, raw, source))
        for name in re.findall(r"\\(?:input|include)\s*\{([^}]+)\}", source):
            child = root / name
            if not child.suffix:
                child = child.with_suffix(".tex")
            visit(child, ancestors + (path,))

    visit(root / f"{entry}.tex", ())
    return records


def check(root: Path, entry: str):
    records = collect(root, entry)
    bib_source = (root / "references.bib").read_text(encoding="utf-8")
    bib_keys = re.findall(r"@\w+\s*\{\s*([^,\s]+)", bib_source)
    labels, refs, citations, controls, proof_prefixes = [], [], [], [], []
    proof_count = 0
    for path, raw, source in records:
        relative = str(path.relative_to(root))
        labels.extend(re.findall(r"\\label\s*\{([^}]+)\}", source))
        refs.extend(re.findall(r"\\(?:eqref|ref|pageref|autoref)\*?\s*\{([^}]+)\}", source))
        for group in re.findall(r"\\cite\w*\*?(?:\[[^\]]*\])*\s*\{([^}]+)\}", source):
            citations.extend(x.strip() for x in group.split(","))
        controls.extend(
            {"file": relative, "offset": i, "code": ord(c)}
            for i, c in enumerate(raw)
            if ord(c) < 32 and c not in "\t\n\r"
        )
        last_proof = 0
        for match in re.finditer(r"\\begin\{proof\}", source):
            proof_count += 1
            explanation = source.rfind(r"\paragraph{Proof idea", last_proof, match.start())
            if explanation == -1:
                proof_prefixes.append(
                    {"file": relative, "line": source.count("\n", 0, match.start()) + 1}
                )
            last_proof = match.end()
    duplicate_labels = sorted(k for k, v in collections.Counter(labels).items() if v > 1)
    result = {
        "entry": entry,
        "compiled_tex_files": len(records),
        "compiled_inputs": [str(p.relative_to(root)) for p, _, _ in records],
        "labels": len(labels),
        "proofs": proof_count,
        "proofs_without_explanatory_prefix": proof_prefixes,
        "duplicate_labels": duplicate_labels,
        "missing_references": sorted(set(refs) - set(labels)),
        "missing_citations": sorted(set(citations) - set(bib_keys)),
        "bibliography_entries": len(bib_keys),
        "cited_bibliography_entries": len(set(citations)),
        "duplicate_bibliography_keys": sorted(
            k for k, v in collections.Counter(bib_keys).items() if v > 1
        ),
        "control_characters": controls,
        "scope": "Document consistency and layout only; no mathematical verification",
    }
    log = root / "qa" / f"{entry}_pass4.log"
    if log.exists():
        log_text = log.read_text(encoding="utf-8", errors="replace")
        result["latex_warnings"] = [
            line for line in log_text.splitlines() if "Warning" in line or "Overfull" in line
        ]
    pdf_path = root / f"{entry}.pdf"
    if pdf_path.exists():
        blob = pdf_path.read_bytes()
        result["pdf_sha256"] = hashlib.sha256(blob).hexdigest()
        result["pdf_has_eof"] = blob.rstrip().endswith(b"%%EOF")
        try:
            import fitz
        except ImportError:
            result["pdf_inspection"] = "PyMuPDF unavailable; metadata inspection skipped"
        else:
            pdf = fitz.open(pdf_path)
            result["total_pages"] = len(pdf)
            result["pdf_repaired"] = pdf.is_repaired
            result["figure_pages"] = []
            result["text_outside_physical_page"] = []
            all_text = []
            for index, page in enumerate(pdf):
                text = page.get_text()
                all_text.append(text)
                if re.search(r"\bFigure\s+\d+\s*:", text):
                    result["figure_pages"].append(index + 1)
                for block in page.get_text("dict")["blocks"]:
                    for line in block.get("lines", []):
                        for span in line.get("spans", []):
                            x0, y0, x1, y1 = span["bbox"]
                            if (
                                x0 < -0.5
                                or y0 < -0.5
                                or x1 > page.rect.width + 0.5
                                or y1 > page.rect.height + 0.5
                            ):
                                result["text_outside_physical_page"].append(
                                    {"page": index + 1, "text": span["text"], "bbox": span["bbox"]}
                                )
            (root / "qa" / f"{entry}_text.txt").write_text(
                "\n\f\n".join(all_text), encoding="utf-8"
            )
            aux = root / f"{entry}.aux"
            marker = "page:conf-main-end" if entry == "conference" else "page:main-end"
            if aux.exists():
                match = re.search(
                    r"\\newlabel\{" + re.escape(marker) + r"\}\{\{[^}]*\}\{(\d+)\}", aux.read_text()
                )
                if match:
                    result["main_body_pages"] = int(match.group(1))
            pdf.close()
    return result


PROBLEM_KEYS = (
    "proofs_without_explanatory_prefix",
    "duplicate_labels",
    "missing_references",
    "missing_citations",
    "duplicate_bibliography_keys",
    "control_characters",
    "latex_warnings",
    "text_outside_physical_page",
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("entries", nargs="*", default=["conference", "exact_sampling_networks"])
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    (root / "qa").mkdir(exist_ok=True)
    reports = {entry: check(root, entry) for entry in args.entries}
    destination = root / "structural_check.json"
    destination.write_text(json.dumps(reports, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                entry: {k: v for k, v in report.items() if k not in {"compiled_inputs", "scope"}}
                for entry, report in reports.items()
            },
            indent=2,
        )
    )
    problems = [
        f"{entry}: {key}"
        for entry, report in reports.items()
        for key in PROBLEM_KEYS
        if report.get(key)
    ]
    if problems:
        print("Structural problems: " + ", ".join(problems))
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
