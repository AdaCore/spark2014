Program Structure and Compilation Issues
========================================

Because functions and expressions in |SPARK| must be side-effect free, it may
be necessary to analyze the bodies of all subprograms called to determine if a
function or an expression is in |SPARK|.

Limited Package Views
---------------------

Any state abstractions declared within a given package are present in
the limited view of the package.

[This means that, for example, a Globals aspect specification for a
subprogram declared in a library unit package P1 could refer to a state
abstraction declared in a package P2 if P1 has a limited with of P2.]

