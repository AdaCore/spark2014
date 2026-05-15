---
name: explain-code
description: >
  Use this skill when the user wants to add a new GNATprove explain code for a
  SPARK violation. Covers validation, research, drafting the markdown explanation,
  user confirmation, and all four code changes needed to wire the new code up.
license: Apache-2.0
metadata:
  version: "0.1.0"
---

# Explain Code Skill

This skill adds a new explain code (E00NN) for a `Violation_Kind` in the
spark2014 repository. Explain codes appear in GNATprove error messages as
`[E00NN]` and are accompanied by a continuation message directing the user
to run `gnatprove --explain=E00NN` for a detailed explanation.

## Invocation

Two modes:

- **New code**: the user provides a `Violation_Kind` name (e.g.,
  `Vio_Controlled_Types`). Follow Phase 1 → Phase 2.
- **Fix mode**: the user provides an existing code number and says to fix it
  (e.g., "fix E0024"). Follow Phase 0 → Phase 1 (Steps 4–6a only) → Phase 2
  (Change 1 only).

---

## Phase 0: Fix Mode — Diagnose and Research

*Only for fix mode. Skip entirely for new codes.*

### Step F1 — Read and validate the existing file

Read `share/spark/explain_codes/E00NN.md`. Run `/validate-explain-codes` on it
to confirm which examples fail and record the gnatprove output for each FAIL.
If everything passes, tell the user and stop — nothing to fix.

### Step F2 — Research a correct workaround

Using the failing good example(s) and the gnatprove error output as a starting
point, research the correct fix:

- Identify the SPARK RM rule the failing example violates (the error message
  usually cites it).
- Fetch the relevant SPARK RM section and User's Guide discussion (same URLs
  as Step 5 of Phase 1).
- Draft a replacement for the failing section of the file only. Keep the bad
  example and the explanation prose unchanged unless they are also wrong.

Then proceed to Step 6 (draft the replacement content) and Step 6a (validate
it). If validation passes, go to Phase 2 Fix — Change 1 only.

### Phase 2 Fix — Update the markdown file

Write the corrected content to `share/spark/explain_codes/E00NN.md`.
No changes to `vc_kinds.ads`, `vc_kinds.adb`, or `README.md` are needed.

After writing, show the user the `git diff` to review before committing.

---

## Phase 1: Validate and Research

Do all of the following before presenting anything to the user.

### Step 1 — Validate the choice

Grep `src/common/vc_kinds.adb` for the `Explain_Code` case expression (search
for `function Explain_Code`). Confirm that the given `Violation_Kind` falls
through to the `when others => EC_None` arm and is not already mapped to a
specific code. If it already has a code, tell the user and stop.

Also confirm that no `.md` file exists in `share/spark/explain_codes/` whose
content visibly covers this violation. If one does, tell the user and stop.

### Step 2 — Gather the violation's metadata

In `src/common/vc_kinds.adb`, find:

- The **violation message**: the string returned by `Violation_Message` for
  this kind (in the large case expression that maps `Violation_Kind` to
  strings).
- The **SRM reference**: the string returned by `SRM_Reference` for this kind
  (in the second large case expression). Note the SPARK RM section number
  (e.g., `"SPARK RM 7.6(1)"`).

### Step 3 — Determine the next code number

Look at the tail of the `Explain_Code_Kind` enumeration in
`src/common/vc_kinds.ads` and its representation clause. The next number is
one more than the current maximum.

### Step 4 — Study existing explain codes for style

Read the two or three most recently added `.md` files in
`share/spark/explain_codes/` (sort by modification time or by highest number).
Note the structure: illegal code example with `-- error` comments, "This error
is issued on..." opening sentence, explanation of the rule and its rationale,
fix or workaround with a code example, optional link to the SPARK RM.

### Step 5 — Research the violation

Using the SRM section number from Step 2:

- Fetch the relevant section of the SPARK Reference Manual. The base URL is:
  `https://docs.adacore.com/live/wave/spark2014/html/spark2014_rm/`
  The HTML filename corresponds to the Ada RM chapter (e.g., section 7.x →
  `packages.html`, section 6.x → `subprograms.html`, section 3.x →
  `declarations-and-types.html`, section 5.x → `statements.html`).
  Append `#<anchor>` using the section title in lowercase with hyphens.
  The user-provided URL for the violation's topic (if any) takes precedence.

- Search the SPARK User's Guide for discussion of this violation:
  `https://docs.adacore.com/live/wave/spark2014/html/spark2014_ug/en/`

Record what you found in each source, noting any rationale, examples, or
suggested workarounds.

### Step 6 — Draft the markdown file

Draft the content for `share/spark/explain_codes/E00NN.md` following the style
from Step 4. The file should contain:

1. **Illegal code example** — the minimal Ada snippet that triggers this
   violation, with `-- error` on the offending line(s).
2. **"This error is issued on..."** — what construct triggers it and why the
   rule exists. Explain the rationale, not just the rule.
3. **Fix or workaround** — a concrete Ada example showing the corrected code.
   If no clean fix exists, acknowledge that and describe the best available
   workaround (e.g., encapsulating in `SPARK_Mode => Off`).

   If you offer more than one fix, each fix must have its own complete,
   self-contained Ada code example — never prose-only. Step 6a then validates
   every example. If a candidate fix is too unwieldy to give as a small
   example, that is a signal to drop it rather than leave it as a bare
   suggestion.
4. **Optional SPARK RM link** — if the RM section is informative, link to it
   using a Markdown reference link at the bottom of the file, following the
   pattern in `share/spark/explain_codes/E0001.md`.

Do not add a "See also `E00NN`" block cross-referencing sibling explain codes.
Existing explain codes do not use them, and they are easy to make inconsistent
across a batch (some codes listed, some not). The README index already lets
readers find related codes.

### Step 6a — Validate examples

Before presenting the draft to the user, run the `/validate-explain-codes`
skill against the draft markdown content (bad example and all good examples).
See that skill for the full procedure; the short version:

1. Write the bad example to `ec-test/`, run `gnatprove -P ec-test/default.gpr
   --mode=check -j0 --output=oneline`, confirm at least one message lands on
   a `-- error` line.
2. For each good example (or group of files that belong together), clean
   `ec-test/src/` (`rm -rf ec-test/src && mkdir ec-test/src`), write the snippet(s) to `ec-test/src/`, and confirm
   gnatprove produces zero messages.

Record the result (PASS/FAIL per snippet) to include in Step 7.

### Step 7 — Review and confirm (or proceed automatically)

Present to the user:

1. The proposed **E00NN.md content** in full.
2. The **validation results** from Step 6a (PASS/FAIL per snippet).
3. A brief **"Sources used"** note: which SPARK RM section and UG section you
   consulted, and what each contributed.
4. Any **open questions** — e.g., uncertainty about the right workaround,
   whether the illegal code example is the most representative one, or any
   validation FAILs that need resolution.

**If you have open questions or any validation FAILs**, stop here and wait for
the user to answer them before proceeding.

**If you are confident** in the draft (no unresolved questions, all validation
checks PASS), proceed directly to Phase 2 without waiting for confirmation.

---

## Phase 2: Implement

Proceed only after user confirmation. Make all four changes:

### Change 1 — Create the markdown file

Write the confirmed content to `share/spark/explain_codes/E00NN.md`.

### Change 2 — Add the enum value (`src/common/vc_kinds.ads`)

In the `Explain_Code_Kind` type declaration, add `EC_Xxx` as the new last
value (before the closing `)`) and add `EC_Xxx => NN` to the representation
clause, aligned with the existing entries.

The naming convention for `EC_Xxx` is to derive it from the `Violation_Kind`
name with `Vio_` replaced by `EC_`: e.g., `Vio_Controlled_Types` →
`EC_Controlled_Types`.

### Change 3 — Wire the case arm (`src/common/vc_kinds.adb`)

In the `Explain_Code (Kind : Violation_Kind)` case expression, add:

```ada
when Vio_Xxx => EC_Xxx,
```

Insert it before the `when others => EC_None` arm, aligned with existing
entries.

### Change 4 — Update the README index

Append to `share/spark/explain_codes/README.md`:

```
- E00NN: `<short description matching the violation message>`
```

The short description should be a condensed version of the violation message,
suitable as a one-line index entry.

---

## Completion

After all four changes, show the user the `git diff` so they can review the
full changeset before committing.
