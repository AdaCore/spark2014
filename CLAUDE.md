# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

SPARK 2014 is a verification toolset for high-reliability Ada applications. It consists of:
- **gnatprove**: Main verification driver (Ada/Python)
- **gnat2why**: Translator from Ada to Why3 intermediate language (Ada)
- **why3**: Verification framework with prover integration (OCaml, git submodule)

The toolset enables formal verification of Ada code through automated and interactive theorem proving.

## Building

Assume the environment is already set up. Use "make" and "make install-all" to build and install.


## Testing

### Running Tests

```bash
# Run full testsuite (from testsuite/gnatprove/)
cd testsuite/gnatprove
./run-tests

# Run with options
./run-tests --help           # Show all options
./run-tests -j8              # Run with 8 parallel jobs
./run-tests <test_name>      # Run specific test
./run-tests --discriminants=large  # Include large tests (skipped by default)
```

### Test Structure

- Tests are in `testsuite/gnatprove/tests/<test_name>/`
- Each test directory contains:
  - Ada source files
  - `test.out`: Expected output
  - `test.yaml`: Configuration (optional)
  - `test.py`: Custom test driver (optional, overrides yaml)
- Tests with `__flow` in name run flow analysis (`do_flow()`)
- Other tests run proof (`prove_all()`)
- Tests with `ug__` prefix are User's Guide examples with fixed commands

### Running Individual Tests

To manually run a test:
```bash
cd testsuite/gnatprove/
./run-tests <testname> -d temp
cd temp/testname
gnatprove -P <project>.gpr [options]
```

Generally the project file is `test.gpr`.

## Code Formatting

### Format Ada Code

```bash
# Format all Ada code
make format

# Check formatting without modifying files
make check-format
```

### Python Code

Python code uses black and flake8 (configured in `.flake8` and `.pre-commit-config.yaml`).

## Architecture

### Directory Structure

```
spark2014/
├── src/                      # GNATprove and backend components
│   ├── gnatprove/           # Main driver (Ada)
│   ├── common/              # Shared utilities
│   ├── flow/                # Flow analysis
│   ├── spark/               # SPARK semantic analysis
│   ├── why/                 # Why3 translation backend
│   ├── counterexamples/     # Counterexample generation
│   └── utils/               # General utilities
├── gnat2why/                # Ada to Why3 translator
│   ├── gnat_src/           # Symlink to GNAT compiler sources (required)
│   ├── obj/                # Build artifacts
│   └── Makefile            # Build configuration
├── why3/                    # Why3 framework (git submodule)
├── testsuite/gnatprove/    # Comprehensive test suite
├── docs/                    # Documentation (Sphinx)
│   ├── ug/                 # User's Guide
│   └── lrm/                # Language Reference Manual
├── include/                # SPARK library files
├── share/                  # Runtime files, configurations
└── install/                # Installation directory (created by make install)
```

### Component Interaction

1. **gnatprove** (Ada): Main entry point, orchestrates verification
   - Parses project files and command-line options
   - Calls gnat2why for translation

2. **gnat2why** (Ada): Translates Ada to Why3
   - Uses GNAT compiler frontend for parsing/semantic analysis
   - Generates Why3 intermediate verification conditions
   - Invokes Why3 for proof generation and prover scheduling

3. **why3/gnatwhy3** (OCaml): Verification condition manager
   - Manages prover interactions (Alt-Ergo, CVC5, Z3)
   - Handles proof sessions and caching
   - Submodule with SPARK-specific modifications

### Key Project Files

- `gnatprove.gpr`: GPR project file for gnatprove driver
- `gnat2why/gnat2why.gpr`: GPR project for Ada-to-Why3 translator

## Development Workflow

### Common Development Tasks

**Modify gnatprove driver:**
1. Edit files in `src/gnatprove/` or related `src/` directories
2. Run `make && make install-all` to rebuild

**Modify gnat2why translator:**
1. Edit files in `gnat2why/` or `src/why/`, `src/flow/`, `src/spark/`
2. Run `make && make install-all` to rebuild

**Modify Why3:**
1. Edit files in `why3/` submodule
3. Run `make && make install-all` to build and install

### Git Workflow

- Base pull requests on `master` branch
- Pre-commit hooks enforce formatting and check test markers
- If pre-commit hooks modify files, just `git add` the changes and try again

## Important Notes

- **gnat_src symlink**: The `gnat2why/gnat_src` symbolic link to GNAT sources is required before building gnat2why
- **Branch matching**: SPARK sources are tied to specific GNAT compiler versions - use matching branches
