Program Structure and Compilation Issues
========================================

Data flow analysis, unlike compilation, does not follow Ada's separate
compilation model. For example, functions in |SPARK| must be side-effect free;
this rule is enforced as part of data flow analysis. Suppose that a function
calls a procedure which in turn calls another procedure, which in turn calls
yet another. In the absence of Global aspect specifications for the
procedures in question, it would be necessary to analyze the bodies
of all subprograms called in order to determine whether the function
is side-effect free.

Limited Package Views
---------------------

Any state abstractions declared within a given package are present in
the limited view of the package.

[This means that, for example, a Globals aspect specification for a
subprogram declared in a library unit package P1 could refer to a state
abstraction declared in a package P2 if P1 has a limited with of P2.]

