.PHONY: all paper conference full checks structure lean lint format citation clean
PYTHON ?= python3

all: lint citation checks lean paper

# Both PDFs (XeLaTeX, BibTeX, xdvipdfmx); logs go to paper/qa/.
paper:
	cd paper && ./build.sh
conference:
	cd paper && ./build.sh conference
full:
	cd paper && ./build.sh exact_sampling_networks

# Rerun every recorded finite check and require identical outputs.
checks:
	$(PYTHON) tools/run_checks.py

# Labels, references, citations and layout of the built PDFs (needs PyMuPDF).
structure:
	$(PYTHON) paper/checks/document_structure.py

# Lean build with warnings as errors, axiom audit, and paper-label check.
lean:
	cd formalization && lake exe cache get && $(PYTHON) verify.py

lint:
	$(PYTHON) -m ruff check .
	$(PYTHON) -m ruff format --check .

format:
	$(PYTHON) -m ruff check --fix .
	$(PYTHON) -m ruff format .

citation:
	cffconvert --validate

clean:
	cd paper && rm -rf qa *.aux *.bbl *.blg *.log *.out *.toc *.xdv
