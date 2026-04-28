# AGENTS.md

Repository guidance for coding agents working on SPARK 2014.

## Build And Test

Assume the environment is already set up.

- Build and install with `make` and `make install-all`.
- Format Ada code with `make format`; verify formatting with `make check-format`.
- Run tests from `testsuite/gnatprove/` with `./run-tests`.
- Useful test commands:
  - `./run-tests <test_name>`
  - `./run-tests -j8`
  - `./run-tests --discriminants=large`
  - `./run-tests <test_name> -d temp` to keep the generated work directory for manual inspection

## Relevant Areas

- `src/gnatprove/`: main verification driver
- `src/flow/`, `src/spark/`, `src/why/`: analysis and Why3 translation
- `gnat2why/`: Ada-to-Why3 translator
- `why3/`: Why3 submodule with SPARK-specific changes
- `testsuite/gnatprove/tests/`: regression tests
- `docs/`: user and reference documentation

## Developer Documentation

- `docs/develguide/` is the developer documentation for GNATprove internals.
- Before changing behavior or architecture in `src/gnatprove/`, `gnat2why/`,
  `src/flow/`, `src/spark/`, `src/why/`, or `why3/`, read the relevant page(s)
  in `docs/develguide/`.
- Start with the mapped page in `docs/develguide/` and only read additional
  pages when the change clearly crosses subsystem boundaries or the mapped page
  points elsewhere.
- If a change affects documented behavior, architecture, data flow, debug
  workflow, or developer procedures, update the corresponding page in
  `docs/develguide/` in the same change.
- If no existing page is a good fit, update the closest page or add a new page
  and link it from `docs/develguide/index.rst`.

### Developer Guide Routing

- `src/gnatprove/`: `docs/develguide/tool_structure.rst`
- `gnat2why/` general pipeline: `docs/develguide/tool_structure.rst`
- Legality rules and marking: `docs/develguide/legality_checking.rst`
- Flow analysis: `docs/develguide/flow_analysis.rst`
- Generated globals: `docs/develguide/gg.rst`
- Ada to Why3 translation: `docs/develguide/translation_why3.rst`
- `gnatwhy3/` and prover pipeline: `docs/develguide/gnatwhy3.rst`
- Counterexamples, RAC, and model handling:
  `docs/develguide/counterexamples.rst`
- Explanations for unproved checks and related interaction:
  `docs/develguide/tool_interaction.rst`
- GNAT Studio integration: `docs/develguide/gps_integration.rst`

## Test Conventions

- Tests live in `testsuite/gnatprove/tests/<test_name>/`.
- `test.out` stores expected output; `test.yaml` or `test.py` customize execution.
- Tests with `__flow` in the name run flow analysis; most others run proof.
- `ug__` tests mirror User's Guide examples and use fixed commands.
- Most tests don't need a ".gpr" file - the test harness creates one.
- Manual repro usually uses `test.gpr` inside the kept temporary directory.

## Ada Conventions

- Comments start with a capital letter.
- Multi-line comments end with a period; single-line comments do not.
- Each subprogram definition should keep its header comment box.
- Do not add `--  Start of processing for <Name>` comments before `begin`.
- Use `???` for TODOs, open questions, or follow-up work.
- Prefer clear names over purpose-based or type-repeating names.
- Prefer `for Elt of Container loop` over iterator-plus-`Element` patterns.
- Avoid double lookups on containers; use cursors when needed.
- Use `with P; use P;` by default unless qualification is needed to resolve ambiguity.
