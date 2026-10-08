# Checkpoint certificate worksheet

Run either bundled illustration from the paper's source directory:

```sh
python checks/checkpoint_cost_worksheet.py checks/checkpoint_illustrative_input.json
python checks/checkpoint_cost_worksheet.py checks/checkpoint_hadamard_input.json
```

The first illustration contains attention, RMS-floor, and additive-update
parameters. Its original input and output are unchanged. The second is a
structural zero-bias tanh example with first matrix `H_32/32` and identity
matrices in subsequent layers. It has full first-layer rank and column
envelope one. Neither illustration contains measurements from a trained
model, and the worksheet does not inspect or verify a matrix.

## Optional critical-tanh record

A `critical_tanh` record can be added to an existing worksheet or supplied
alone. Its size fields default to the top-level `residual_width`, `depth`,
and `parameter_bits`; the record may override them with `n`, `D`, and
`parameter_bits`.

```json
{
  "residual_width": 32,
  "depth": 5,
  "parameter_bits": 100,
  "critical_tanh": {
    "zero_bias": true,
    "row_norm_max": "1",
    "first_layer_rank": 32,
    "column_envelope": "1",
    "first_layer_rank_is_uniform_constant": false,
    "column_envelope_is_uniform_constant": true
  }
}
```

`zero_bias` is a supplied certificate. The arithmetic check requires
that flag to be true and checks that the supplied row bound is at most
one. It cannot establish either fact about an unseen checkpoint. The two
family flags are optional metadata: a rank or an envelope measured on
one matrix does not certify that it stays bounded across a growing
family. A critical-tanh record describes the square tanh-network theorem;
measurements from one transformer sublayer do not by themselves certify
the assumptions for the entire transformer.

The output keeps the following expressions distinct, using
`B = 16 + b + ceil(log2(n*D+2))`:

| Expression | Meaning |
| --- | --- |
| `max(1,C_col^2)*sqrt(D+1)` | Probe-growth envelope, with an omitted absolute proof constant. |
| `min(D+1,max(1,C_col)^2*sqrt(D+1))` | The envelope selected by comparing `max(1,C_col)^4` with `D+1`; both constants remain unfitted. |
| `sqrt(D+1)*B^max(4,r+2)` | Fixed-rank bit-growth proxy, with an omitted rank-dependent constant. |
| `sqrt(D+1)*B^40` | Bounded-envelope specialization, with its envelope factor omitted. |
| `max(1,C_col)^7*sqrt(D+1)*B^40` | Uniform column-envelope bit-growth proxy, with an omitted absolute constant. |

The last expression uses the arbitrary-radius majority implementation,
so its dependence on the envelope is explicitly polynomial. The original
preprocessing budget is asserted in the logarithmic-depth and
logarithmic-precision regime stated in the paper. All omitted constants
are unfitted. These are sufficient asymptotic upper-bound expressions;
they are neither an instance complexity law nor estimates of seconds,
memory bandwidth, or GPU performance.

Supply integers, exact decimal strings such as `"0.125"`, or rational
strings such as `"1/8"`. Binary JSON floating-point numbers are rejected
for rational quantities. Coefficients and radicands are retained exactly;
fields ending in `display_approx` are numerical displays only. Large
powers are kept as exact factored expressions to avoid allocating an
enormous integer solely for its printed representation.
