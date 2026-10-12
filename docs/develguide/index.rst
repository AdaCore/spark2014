.. GNATprove Developer Guide documentation master file, created by
   sphinx-quickstart on Tue Aug  1 17:08:02 2017.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

GNATprove Developer's Guide
===========================

   Copyright (C) 2017-2022, AdaCore and Capgemini Engineering

   Permission is granted to copy, distribute and/or modify this document
   under the terms of the GNU Free Documentation License, Version 1.1
   or any later version published by the Free Software Foundation;
   with no Invariant Sections, with no Front-Cover Texts, and with no
   Back-Cover Texts.
   A copy of the license is included in the section entitled 'GNU
   Free Documentation License'.

..
   devguide-meta:
   covers: develguide scope, chapter responsibilities, and table of contents
   primary_code: docs/develguide/
   when_to_read: locating the right developer guide page or adding a new one

Purpose and Organization
------------------------

This guide is for developers changing GNATprove. It explains the architecture,
design decisions, and constraints needed to understand a change and its effects
on other parts of the tool. It complements the source code, the SPARK Reference
Manual, and the User's Guide. Readers are assumed to be familiar with Ada and
the use of GNATprove.

What to Document
^^^^^^^^^^^^^^^^

Document subsystem responsibilities, information exchanged between stages,
and the invariants on which analysis depends. Explain why a design was chosen,
including soundness requirements, performance tradeoffs, and limitations that
are difficult to infer from the code. Describe an alternative when it helps
explain a constraint of the chosen design.

Use small examples or diagrams to expose a subtlety. Include code pointers so
readers can find the implementation, and selected debugging workflows that
explain how to investigate a problem across analysis stages.

Keep detailed implementation explanations beside the code. Do not reproduce
routine bodies, API inventories, data structure definitions, exhaustive file
formats, or generated output that readers can obtain from their authoritative
sources. An interface's meaning and constraints belong here; its field-by-field
definition belongs with its producer and consumer. User-facing options and
workflows belong in the User's Guide, language rules in the SPARK Reference
Manual, and build or test procedures with the tooling that owns them. Refer to
upstream Why3 documentation for general Why3 concepts and APIs.

Chapter Responsibilities
^^^^^^^^^^^^^^^^^^^^^^^^

The following map assigns each topic a primary home. It describes the intended
coverage, including areas that remain incomplete. Explain a shared mechanism
in its primary chapter and use cross-references elsewhere for context.

.. list-table::
   :header-rows: 1
   :widths: 25 75

   * - Chapter
     - Responsibility
   * - :doc:`tool_structure`
     - Executable and stage boundaries, orchestration, configuration precedence,
       artifact lifecycles, concurrency, and the path from analysis to reports.
   * - :doc:`legality_checking`
     - Frontend and marking responsibilities, SPARK boundaries, entity
       classification, and the origins of legality diagnostics.
   * - :doc:`flow_analysis`
     - Flow representations and analyses, visibility, and the division between
       local and inter-unit reasoning.
   * - :doc:`gg`
     - Contract inference, propagation of effects through calls, and preservation
       of abstract-state boundaries. Refer to Flow Analysis for the common
       infrastructure and two-phase organization.
   * - :doc:`ownership_checking`
     - Ownership and borrowing permissions, the separate borrow-checking phase,
       and its relationships with marking, flow contracts, and proof encodings.
   * - :doc:`translation_why3`
     - Translation architecture, semantic encodings, verification contexts, and
       the soundness and solver-performance reasons behind them. Ownership
       encodings belong here; the permission analysis belongs in Ownership
       Checking.
   * - :doc:`gnatwhy3`
     - GNATprove's use of Why3: VC generation and splitting, proof strategy,
       scheduling, sessions and proof reuse, and debugging the prover pipeline.
   * - :doc:`gps_integration`
     - The boundary between analysis and IDE presentation, selection of analysis
       targets, and association of displayed messages with analysis artifacts.
   * - :doc:`counterexamples`
     - Model provenance, counterexample validation with runtime assertion
       checking, classification, and investigation of misleading results.
   * - :doc:`tool_interaction`
     - Diagnostic explanations and heuristics that help users understand an
       analysis result, including their precision and limitations.
   * - :doc:`miscellaneous`
     - Cross-project developer concerns that have no suitable home above.
       Link to procedures maintained by their owning project.

Maintaining the Guide
^^^^^^^^^^^^^^^^^^^^^

Describe the current design and retain history only when it explains an
enduring constraint. Update the relevant explanation when a change affects
architecture, data flow, soundness assumptions, or a documented workflow.
Verify code pointers and examples when revising a section. Add a section when
there is a useful explanation to give, rather than an empty outline of possible
topics. Consolidate overlapping explanations before expanding the guide.

Contents
--------

.. toctree::
   :maxdepth: 6

   tool_structure
   legality_checking
   flow_analysis
   gg
   ownership_checking
   translation_why3
   gnatwhy3
   gps_integration
   counterexamples
   tool_interaction
   miscellaneous
