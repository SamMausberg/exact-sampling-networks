# Exact Sampling from Neural Networks: Depth, Attention, and Decoding

Samuel Mausberg, Independent Researcher.

A random output can require less information than the value of a function. The paper studies
this gap for neural networks, counting input probes, random bits, arithmetic, and every
precision refinement. Its main results are:

- **Depth.** A bounded tanh row admits an exact sample from a constant expected number of input
  coordinates. For zero-bias networks with absolute row sums at most one, the worst-case query
  cost lies between the square root of depth and depth. The sharp square-root law holds at every
  fixed first-layer rank and for a bounded column envelope, given sufficient input size.
- **Attention.** Supplied finite keys whose prefixes lie in an affine space of fixed dimension
  admit an appendable exact attention index. For fixed rank, temperature and coordinate bounds,
  its query cost depends on the context length only logarithmically. Without an index, standard
  score scaling can force a linear scan, and arbitrary growing-dimensional indexed queries face a
  conditional hardness barrier.
- **Decoding.** If every head's keys lie in a common affine space of fixed dimension, an exact
  decoder with positive RMSNorm stabilizers constructs and appends its own keys and values in
  expected time polynomial in model size and polylogarithmic in context length, and its outputs
  follow the original autoregressive law exactly. The polynomial degree grows with rank.

## Contents

- `paper/`: LaTeX sources of both versions and the compiled PDFs.
  - `conference.pdf`: 12 pages of main text plus references, with complete proofs of the
    maintained decoder theorem and its finite-cache building blocks.
  - `exact_sampling_networks.pdf`: the full version with every proof.
  - `checks/`: exact-arithmetic and high-precision numerical checks with their recorded JSON
    outputs, and the checkpoint cost worksheet (`checks/checkpoint_worksheet_readme.md`).
    These checks supplement the proofs; no proof depends on them.
  - `archive/`: optional or superseded sections that neither PDF includes.
- `formalization/`: a Lean 4 formalization with Mathlib. See `formalization/README.md` for its
  scope and `formalization/PAPER_MAP.md` for the paper label behind each theorem.
- `tools/`: `run_checks.py` reruns every recorded check and requires identical outputs;
  `lean_map.py` regenerates `formalization/PAPER_MAP.md`.

## Building

The paper needs XeLaTeX, BibTeX and `xdvipdfmx` with TikZ, PGFPlots, Latin Modern and
DejaVu Sans Mono (on Debian or Ubuntu: `texlive-xetex texlive-latex-extra texlive-pictures
texlive-fonts-recommended fonts-lmodern fonts-dejavu-core`).

```sh
make paper        # both PDFs; logs in paper/qa/
make checks       # rerun the finite checks (needs mpmath, see requirements-dev.txt)
make lean         # fetch the Mathlib cache, build with warnings as errors, audit axioms
make lint         # ruff check and format check
make structure    # labels, references and layout of the built PDFs (needs PyMuPDF)
```

The Lean development uses Lean `v4.34.0-rc2` and Mathlib at commit `2631d1cc`. Inside
`formalization/`, `lake exe cache get` followed by `python3 verify.py` rebuilds everything,
checks that every declaration depends only on `propext`, `Classical.choice` and `Quot.sound`,
and checks that every paper label cited in a docstring exists in a compiled TeX file.

## Citation

See `CITATION.cff`. In BibTeX:

```bibtex
@misc{mausberg2026exactsampling,
  author = {Samuel Mausberg},
  title  = {Exact Sampling from Neural Networks: Depth, Attention, and Decoding},
  year   = {2026},
  howpublished = {\url{https://github.com/SamMausberg/exact-sampling-networks}}
}
```

## License

Manuscripts and figures: CC BY 4.0. Code, checks and the Lean formalization: MIT.
See `LICENSE`.
