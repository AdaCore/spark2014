ALFA Subset of Ada
==================

Fine-grain Integration with Full-Ada Code
-----------------------------------------

A subprogram spec is in ALFA

A subprogram is in ALFA

Automatic Detection of Subprograms in ALFA
------------------------------------------

GNATprove automatically detects which subprograms are in ALFA, and which
subprograms are not in ALFA. Thus, the user does not have to annotate the code
to provide this information. However, the user can review the results of this
automatic detection, and require that some subprograms are in ALFA (leading to
an error if not).

Summary File
^^^^^^^^^^^^

The information of which subprograms are in ALFA and which are not in ALFA is
stored in a file with extension .alfa for review by the user. For those
subprograms not in ALFA, it also records in the same file whether:

* the subprogram uses constructs definitely not in ALFA;
* the subprogram uses constructs in ALFA but not yet implemented;
* the subprogram uses constructs not currently in ALFA, but that could be added
  to ALFA in the future.

The last case groups various possible extensions:

* slice: allow slices;
* discriminant: allow discriminant records;
* dispatch: allow dispatching;
* block statement: allow block declare statements;
* any return: allow return statements anywhere;
* any exit: allow exit statements anywhere;
* generic: allow generics;
* impure function: allow functions which write to global variables.

As an example, consider the following code::

    package P is
       X : access Boolean;
       procedure P0;
    end P;

    package body P is
       procedure Set is
       begin
	  X.all := True;
       end Set;

       procedure P0 is
	  Y : Boolean;

	  function Get return Boolean is
	  begin
	     return X.all;
	  end Get;

	  procedure P1 is
	  begin
	     if not Get then
		return;
	     end if;
	     Y := True;
	  end P1;
       begin
	  Set;
	  P1;
       end P0;
    end P;

On this code, GNATprove outputs the following information in file p.alfa::

    -p__set p.adb:2
    -p__p0__get p.adb:10
    -p__p0__p1 p.adb:15 (any return)
    +p__p0 p.adb:7

The first character denotes whether the subprogram is in ALFA (+) or not (-).
The name that follows is a unique name for the subprogram. The location of the
subprogram is given next with its file and line. Subprograms not in ALFA may be
followed by a set of extensions in parentheses, whose implementation would make
the subprogram in ALFA.

In the example above, P.Set and P.P0.Get are not in ALFA because they both
contain pointer dereferences. P.P0.P1 is not in ALFA because it contains a
return statement (not allowed in procedures). However, since P.Set spec and
P.P0.P1 spec are both in ALFA, P.P0 is in ALFA. Notice that implementing the
extension "any return" would put P.P0.P1 in ALFA, hence the parenthesized
extension on the line for P.P0.P1.

The purpose of defining possible extensions early is to allow users to
experiment and see which extensions are more beneficial in their context, in
order to prioritize efficiently their implementation.

User-specified Compliance
^^^^^^^^^^^^^^^^^^^^^^^^^

The user may require that some subprograms are in ALFA by inserting a specific
pragma Annotate in the body of the subprogram. He may also insert this pragma
in a package declaration (spec or body) to require that all subprogram
declarations in this package (spec or body) are in ALFA.

On the following example::

    package P is
       pragma Annotate (Formal_Proof, On);
       X : access Boolean;
       procedure P0;
    end P;

    package body P is
       pragma Annotate (Formal_Proof, On);

       procedure Set is
       begin
	  X.all := True;
       end Set;

       procedure P0 is
	  Y : Boolean;

	  function Get return Boolean is
	     pragma Annotate (Formal_Proof, Off);
	  begin
	     return X.all;
	  end Get;

	  procedure P1 is
	  begin
	     if not Get then
		return;
	     end if;
	     Y := True;
	  end P1;
       begin
	  Set;
	  P1;
       end P0;
    end P;

GNATprove outputs the following errors::

    p.adb:6:07: explicit dereference is not in ALFA
    p.adb:18:07: "return" in procedure is not yet in ALFA (any return)
    p.adb:21:13: "return" in the middle of subprogram is not yet in ALFA (any return)
    p.ads:3:08: access type is not in ALFA

Notice that no error is given for the dereference in P.P0.Get, as another
pragma Annotate specifies that formal proof should not be done on this
subprogram.

A Non-ambiguous Subset of Ada
-----------------------------

Pure Specifications
-------------------

Current Definition of ALFA
--------------------------

Possible Extensions
-------------------
