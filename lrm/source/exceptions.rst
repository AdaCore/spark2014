Exceptions
==========

Raising and handling of exceptions allow forms of control flow that complicate
both specification and verification of a program's behavior. This is the reason
explicit uses of exceptions are excluded from |SPARK|.

Note that the reserved word *exception* is not allowed in |SPARK|, thus
handlers are not in |SPARK| either.

Exceptions can still be raised implicitly (for example, by the failure of a
language-defined check). Pragmas ``Assert``, ``Assertion_Policy``,
``Suppress``, and ``Unsuppress`` are allowed in |SPARK|.
