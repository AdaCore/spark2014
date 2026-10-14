##################
Ownership Checking
##################

..
   devguide-meta:
   covers: ownership and borrowing overview and borrow-checking phase
   primary_code: src/why/gnat2why-borrow_checker.*, src/why/gnat2why-driver.adb
   when_to_read: changes to ownership analysis, permission tracking, moves,
   borrows, or observations

Ownership checking enforces the SPARK restrictions on pointer aliasing using
permissions on paths. Moves transfer ownership, borrows temporarily restrict
access to the borrowed structure, and observations permit shared read access.
These restrictions provide the aliasing guarantees on which the proof encodings
of access values and borrowing depend.

The borrow checker is a separate AST analysis implemented in
:file:`src/why/gnat2why-borrow_checker.adb`. It maintains a permission environment
as it processes the program. It is distinct from the graph-based flow analyses.
The analysis driver runs flow analysis first, then ownership checking, before
proceeding to proof translation. Ownership errors stop processing before proof.
The phase boundary is defined in :file:`src/why/gnat2why-driver.adb`.
