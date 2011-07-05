Getting started with GNATprove
==============================

This chapter describes some simple ways of using GNATprove to formally
prove properties on programs. A more detailed description of
GNATprove's capabilities should follow in the next sections; here,
only a taste of them will be given.

We will be running GNATprove on a simple program that computes how
much money is left after paying an income tax. The rate is a
percentage, so it should be inferior to 100. One may also want to
check that such a function does decrease the original amount of money
(sadly). So the specification of this function may be::

    function After_Tax
      (Before_Tax : Natural;
       Rate       : Natural) return Natural with
      Pre  => (Rate <= 100),
      Post => (After_Tax'Result <= Before_Tax);

This specification should be in a file named ``after_tax.ads``. This function
can then be implemented as follow::

    function After_Tax
      (Before_Tax : Natural;
       Rate       : Natural) return Natural is
    begin
       return Before_Tax - Before_Tax * Rate / 100;
    end After_Tax;

The body of this function should be in a file named
``after_tax.adb``. Once these two files are created, one may want to
prove that its contract and implementation are consistent. To do so,
a GNAT project should be created::

    project Taxes is
       for Source_Dirs use (".");

       package Compiler is
          for Default_Switches ("Ada") use ("-gnat12");
       end Compiler;
    end Taxes;

This project should be in file ``taxes.gpr``. It specifies that the
source code to inspect is in the current directory; as this particular
example uses an Ada 2012 feature (aspects), it is also needed to add
an additional compiler option (-gnat12). GNAT Projects are used by
many other tools of GNAT Pro; for an in-depth documentation of this
technology, you may consult the GNAT Pro user's guide.

You can then invoke GNATprove on this project::

    gnatprove -P taxes.gpr

By default, GNATprove is in ``detect`` mode and tells us which part of
the application it can handle. It generates a set of files:
   * a file ``gnatprove.out`` that contains project statistics; this
     information also shows up on the standard output.
   * a directory ``gnatprove`` containing per-unit information (in files with
     extension ``.alfa``)

In this simple case, one subprogram is not supported::

    Subprograms in Alfa       :   0% (0/1)
      ... already supported   :   0% (0/1)
      ... not yet supported   :   0% (0/1)
    Subprograms not in Alfa   : 100% (1/1)

    Subprograms not in Alfa due to (possibly more than one reason):
     ambiguous expr           : 100% (1/1)

The implementation indeed uses an ambiguous expression: the operators
'/' and '*' may be evaluated in any order. GNATprove does not support
such constructs and requires to make the evaluation order explicit,
using parenthesis.

Still, we may have a closer look to details; those are in
gnatprove/after_tax.alfa. This file reads::

    -+ after_tax after_tax.ads:1 (ambiguous expr)

This lists the subprograms defined in the project; here, ``after_tax``,
defined at line 1 in file ``after_tax.ads``. The first '-' means that
the body of this subprogram is not in Alfa, implying that GNATprove
will not be able to prove properties on this body. However, as the
second '+' implies, ``After_Tax``'s specification is in Alfa; which means
that it will not prevent its callers from being handled by GNATprove.

As the specification is in Alfa, GNATprove can check that its
precondition is complete. This is given by the ``check`` mode::

    gnatprove --mode=check -P taxes.gpr

No error will be returned in this case; so this precondition cannot
raise a run-time error (for more information about the ``check`` mode,
please consult the section Completeness of Preconditions).

This concludes our quick tour of this tool; the following chapters
will detail further Alfa, GNATprove, GNATtest and the functionalities
that these tools provides, making a clear separation between what
is already there, what will be implemented in a near future, and what
is outside the scope of this technology.

