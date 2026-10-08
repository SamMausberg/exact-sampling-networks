#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

# The build compiles documents only. It does not run Lean or verify mathematics.
# Optional arguments select one or both entry points; the default builds both.
if (( $# == 0 )); then
  set -- conference exact_sampling_networks
fi
mkdir -p qa
for paper_entry in "$@"; do
  case "$paper_entry" in
    conference|exact_sampling_networks) ;;
    *) printf 'Unknown document entry point: %s\n' "$paper_entry" >&2; exit 2 ;;
  esac
  rm -f -- "${paper_entry}.aux" "${paper_entry}.out"
  xelatex -no-pdf -interaction=nonstopmode -halt-on-error \
    "${paper_entry}.tex" > "qa/${paper_entry}_pass1.log" 2>&1
  bibtex "$paper_entry" > "qa/${paper_entry}_bibliography.log" 2>&1
  for paper_pass in 2 3 4; do
    xelatex -no-pdf -interaction=nonstopmode -halt-on-error \
      "${paper_entry}.tex" > "qa/${paper_entry}_pass${paper_pass}.log" 2>&1
  done
  xdvipdfmx -o "${paper_entry}.pdf" "${paper_entry}.xdv" \
    > "qa/${paper_entry}_conversion.log" 2>&1
  printf 'Built %s.pdf\n' "$paper_entry"
done
