Globals and Parameter aspects
=============================

For a subprogram, the following aspects may be defined with an aspect
specification:

 Global_In
     The global names that are read by the subprogram
 Global_Out
     The global names that are written by the subprogram
 Global_In_Out
     The global names that are read and written by the subprogram
 Param_In
     The parameter names that are read by the subprogram
 Param_Out
     The parameter names that are written by the subprogram
 Param_In_Out
     The parameter names that are read and written by the subprogram


The definition of such an aspect is a comma-separated list of names, including
own variables, potentially guarded by a condition.

Legality rules
--------------

The parameter aspects should refine the regular Ada 2012 parameter modes, for
example when a parameter X appears in the Param_In_Out aspect, its parameter
mode should be ``in out``.

Meaning
-------

Globals and parameter aspects describe the set of names that is modified by
the subprogram. If an implementation for the subprogram exists, it is checked
that the actual set of modified names is included in the set of names that is
declared using these aspects. The aspects do not have any dynamic semantics.

Examples
--------

The following example illustrates simple and advanced uses of globals and
parameter aspects::

    type A is array (Integer range 1 .. 10) of Integer;

    type R is record
       F_1 : A;
       F_2 : Integer;
    end;

    G : Integer;

    --  These aspects describe that P always reads global variable G, --
    --  always reads and writes parameter I, and reads and writes the Ith cell
    --  of field F_1 of the argument R_Arg, but only when I is equal to 0.

    procedure P (I : in out Integer; R_Arg : in out R)
    with
      Global_In => (G),
      Param_In_Out => (I, if I = 0 then R_Arg.F_1 (I));

