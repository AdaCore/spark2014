---
name: validate-explain-codes
description: >
  Validates the bad and good Ada/SPARK code examples in one or more explain
  code markdown files (E00NN.md) by running gnatprove --mode=stone against
  each snippet in the ec-test project. Can be invoked standalone or called
  as a step from the explain-code skill.
license: Apache-2.0
metadata:
  version: "0.1.0"
---

# validate-explain-codes

This skill validates the Ada/SPARK code examples embedded in explain code
markdown files (`share/spark/explain_codes/E00NN.md`). It checks that:

- **Bad examples** (illegal code) produce at least one `gnatprove` message on
  a line marked `-- error`.
- **Good examples** (fixes/workarounds) produce zero `gnatprove` messages.

Validation uses `gnatprove --mode=stone`, which covers SPARK legality and flow
analysis but not proof. This is appropriate because all explain code violations
are legality errors that appear before proof starts.

## Invocation

The user provides one or more `E00NN.md` file paths, a range ("validate E0028
through E0037"), or asks to validate all explain codes. When invoked from
`/explain-code`, the draft markdown content is passed directly rather than read
from disk.

---

## Phase 1: Parse the markdown

For each target `.md` file, read its content and reason about the Ada code
blocks it contains. Do not use regex — use judgment.

### Identifying bad vs. good blocks

There is no explicit tag on code fences. Use context to determine role:

- **Bad (illegal) example**: Introduced by text like "Example of illegal
  code:" or similar. This is almost always the first code block in the file.
  Lines within this block ending with `-- error` (or `-- error: ...`) identify
  the specific offending constructs; note their line numbers within the snippet.

- **Good (fix/workaround) examples**: All subsequent code blocks. These show
  corrected or restructured code.

### Grouping multi-file good examples

Some fixes require multiple compilation units that must be compiled together
(e.g., a package spec and its body). Reason about grouping:

- If block N is a package spec (`package Foo is`) and block N+1 is its body
  (`package body Foo is`), they form one group and must be written and checked
  together in a single gnatprove run.
- If block N+1 is a completely independent unit (different package/procedure
  name, or a clearly separate alternative fix), treat it as an independent
  example with its own run.
- When uncertain, prefer grouping: checking together what could be separate is
  harmless; checking separately what requires both files will produce spurious
  errors and mask the real result.

### Placeholder substitution

Before writing any snippet to disk, scan for lines whose non-whitespace
content is exactly `...`. Replace each such line with `null;`, preserving the
leading indentation. `...` is informal Ada notation meaning "some statements
go here; details don't matter". Substituting `null;` is the correct minimal
valid statement for validation purposes.

Note any substitutions made when reporting results.

### Deriving filenames

Derive the filename from the compilation unit name using Ada conventions:
- `package Foo` → `foo.ads`
- `package body Foo` → `foo.adb`
- `package Foo.Bar` → `foo-bar.ads`
- `package body Foo.Bar` → `foo-bar.adb`
- `procedure Foo` → `foo.adb`

If a snippet is a fragment with no `package` or `procedure` header, wrap it in
a minimal procedure:

```ada
procedure Snippet_N is
begin
   <fragment here>
end Snippet_N;
```

and name the file `snippet_n.adb`.

---

## Phase 2: Run each check

The test project is at `ec-test/default.gpr` in the repository root. Source
files go in `ec-test/src/` (the GPR specifies `Source_Dirs := ("src")`).

**Never run two gnatprove instances concurrently.**

For each example group (bad or good), follow this sequence:

### Step 1 — Clean

Delete and recreate `ec-test/src/` to remove all previous snippets:

```bash
rm -rf ec-test/src && mkdir ec-test/src
```

### Step 2 — Write

Write the snippet(s) to `ec-test/src/` using the derived filenames.

### Step 3 — Run gnatprove

```bash
cd /it/repos/spark2014 && gnatprove -P ec-test/default.gpr --mode=stone -j0 --output=oneline 2>&1
```

Set the Bash timeout to at least 120000ms.

### Step 4 — Assess

**For a bad example:**

First, determine which lines in the written file carry `-- error`. A gnatprove
message "matches" a `-- error` line if it is reported on that line **or on any
of the 1–2 lines immediately preceding it**. This window handles multi-line
constructs (instantiations, declarations split across lines) where gnatprove
anchors the error at the opening token while the `-- error` annotation sits on
a later line of the same construct — which is the natural reading position.

Next, classify each matching message:
- **SPARK legality error**: the message text contains phrases like "not allowed
  in SPARK", "SPARK RM", "violation of aspect SPARK_Mode", or "violation of
  pragma SPARK_Mode". These are the errors explain codes are designed to
  document.
- **Non-SPARK error**: parse errors, "not yet supported", Ada legality errors,
  or any other message that does not mention SPARK explicitly.

Then choose the result:
- **PASS** — at least one matching message is a SPARK legality error, and no
  non-SPARK errors appear anywhere in the output (neither on `-- error` lines
  nor elsewhere).
- **PASS\*** — at least one matching message is a SPARK legality error, but
  non-SPARK errors also appear. Flag with an asterisk and list the extra
  messages; they may indicate the example needs adjustment (e.g., a missing
  `with Import`, a stricter Ada legality check firing first).
- **FAIL** — no messages match any `-- error` line, or all matching messages
  are non-SPARK errors (the SPARK violation was never triggered).

**For a good example:**
- **PASS** if gnatprove produces no error or check messages. Warnings (e.g.,
  "pragma Annotate" suggestions) are acceptable and do not count as failures.
  Only hard errors and SPARK legality/flow violations count as failures.
- **FAIL** if gnatprove produces any error or check message.

---

## Phase 3: Report

After all runs, print a summary:

```
E0023  bad: PASS    good-1: PASS
E0024  bad: PASS    good-1: FAIL    good-2: PASS
E0026  bad: PASS*   good-1: FAIL
```

Possible outcomes per snippet: `PASS`, `PASS*`, `FAIL`.

For each `FAIL` or `PASS*`:
- Identify which snippet (bad or good-N) and what outcome.
- Quote the gnatprove output for that run.
- Give a brief assessment:
  - FAIL (bad): wrong `-- error` annotation, missing SPARK_Mode, SPARK
    violation not triggered, or only non-SPARK errors produced.
  - FAIL (good): actual SPARK error in the "fix" code, filename mismatch,
    grouping mistake.
  - PASS\*: list the unexpected non-SPARK messages and note what they suggest
    (e.g., example may need `with Import`, or a precondition is not met).
- Note any `...` → `null;` substitutions that were applied.

Do not auto-fix failures. Report and let the user decide.

---

## Integration with /explain-code

When invoked from `/explain-code`, run this validation after Step 6 (draft)
and before Step 7 (review/confirm):

- Validate the bad example and all good examples from the draft content.
- Include the result (PASS/FAIL per snippet) in the Step 7 presentation.
- If any good example **FAIL**s, treat it as an open question and do not
  proceed to Phase 2 without user input, even if you would otherwise be
  confident enough to proceed automatically.
- If the bad example **FAIL**s (no error triggered), also treat it as an open
  question — the illegal example may not actually be illegal, or may need
  additional context to trigger the violation.
- If the bad example is **PASS\***, surface the extra messages in the Step 7
  presentation alongside the SPARK error; the user may want to revise the
  example to avoid them.
