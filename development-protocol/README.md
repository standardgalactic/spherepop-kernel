# Spherepop Development Protocol

Reference code and fixtures accompanying the Spherepop Development Protocol.

## Specification

This package holds the specification and the executable material that accompanies it. The specification is in [`spec/`](spec/) as LaTeX source and a compiled PDF.

It is a prospective protocol, and the code here is a limited reference implementation that exercises selected parts of it. It does not establish conformance with the complete specification.

The operations follow Chapter 6 of *Distinction Under Constraint*:

| Operation | Description |
| :--- | :--- |
| `POP` | Opens a sphere. |
| `BIND` | Attaches authorization and base version. |
| `TRANSFORM` | Performs transformations inside the sphere. |
| `VERIFY` | Performs verification inside the sphere. |
| `COLLAPSE` | Commits to the authoritative history. |
| `REFUSE` | Records why a continuation cannot proceed. |

`COLLAPSE` is the only operation that commits to the authoritative history.

## Fixtures

The fixtures in [`fixture/`](fixture/) are three small histories with expected outcomes.

| Fixture | Purpose |
| :--- | :--- |
| [Parser example](fixture/parser_example_fixture.json) | A four-event history with a refused proposal, a stale evidence case, a commit, and a repair. |
| [Nested spheres](fixture/nested_sphere_fixture.json) | Two subordinate spheres that each pass local certification while their composition violates a parent obligation. |
| Repair target | Demonstrates that a repair must name an existing event. |

The two make scripts in [`fixture/`](fixture/) regenerate the first two fixtures with real SHA-256 digests, and [`kernel/make_repair_fixture.py`](kernel/make_repair_fixture.py) regenerates the third.

Regeneration is deterministic and reproduces the shipped files byte for byte.

## Python Reference Kernel

The Python kernel in [`kernel/`](kernel/) is an executable specification that uses only the standard library.

Run the fixture checks from the repository root:

```sh
cd kernel
python3 -I spherepop_kernel.py \
    ../fixture/parser_example_fixture.json \
    ../fixture/nested_sphere_fixture.json
```

The kernel prints one line per check and exits with a nonzero status if any check fails.

With the `--script` option and a scenario file, it prints a transcript of dispositions instead.

```sh
python3 -I spherepop_kernel.py --script scenario.json
```

## Rust Reference Kernel

The Rust kernel in [`kernel-rs/`](kernel-rs/) is an independently written implementation of the same behavior.

Build it from the repository root:

```sh
cd kernel-rs
cargo build --release
```

The initial build requires network access to fetch the following dependencies:

- `serde_json`
- `sha2`

Run the compiled kernel against the same fixtures:

```sh
target/release/spherepop-kernel \
    ../fixture/parser_example_fixture.json \
    ../fixture/nested_sphere_fixture.json
```

The Rust kernel accepts the same `--script` option:

```sh
target/release/spherepop-kernel --script scenario.json
```

## Differential Testing

The differential harness, [`kernel/differential.py`](kernel/differential.py), generates random scenarios, runs them through both kernels, and requires the resulting transcripts to match line for line.

Build the Rust kernel first, then run the harness from inside `kernel/`:

```sh
python3 -I differential.py 300 40 1
```

The positional arguments are:

| Argument | Value | Description |
| :--- | ---: | :--- |
| Scenarios | `300` | Number of generated scenarios. |
| Steps | `40` | Number of steps per scenario. |
| Seed | `1` | Random seed for reproducibility. |

A divergence is written to:

```text
/tmp/diverging_scenario.json
```

The harness was checked by deliberately breaking the Rust budget rule, which it detected.

## Known Limitations

The kernels do not model provisional journals, rebasing as an operation, authorization time, or the receipt context index.

The canonical encoding relies on `serde_json` key ordering in Rust and on sorted keys in Python. This is correct only for ASCII strings and integers as used in the fixtures. A full [RFC 8785](https://www.rfc-editor.org/rfc/rfc8785) implementation would be needed beyond that restricted domain.

Both kernels share one author and the same fixtures. Their agreement shows that the specification can be implemented twice without ambiguity in these cases and does not independently validate the fixtures.

**Agreement between the reference implementations does not establish conformance with the complete protocol.**