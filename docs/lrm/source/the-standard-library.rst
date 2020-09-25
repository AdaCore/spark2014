Predefined Language Environment (Annex A)
=========================================

This chapter describes how |SPARK| treats the Ada predefined
language environment and standard libraries, corresponding
to appendices A through H of the Ada RM.

|SPARK| programs are able to use much of the Ada predefined language
environment and standard libraries. The standard libraries are not
necessarily mathematically, formally proven in any way, unless
specifically stated, and should be treated as tested code.

In addition many standard library subprograms have checks on the
consistency of the actual parameters when they are called.  If they
are inconsistent in some way they will raise an exception.  It is
strongly recommended that each call of a standard library subprogram
which may raise an exception due to incorrect actual parameters should
be immediately preceded by a pragma Assert to check that the actual
parameters meet the requirements of the called subprogram.
Alternatively the called subprogram may be wrapped in a user defined
subprogram with a suitable precondition.  Examples of these approaches
are given in :ref:`example_of_assert`.

No checks or warnings are given that this protocol is followed.  The
onus is on the user to ensure that a library subprogram is called with
consistent actual parameters.

.. todo:: Provide suitable preconditions on library subprograms using
          raise expressions for compatibility with Ada. Post release 1.

.. todo:: Provide detail on Standard Libraries.
          To be completed in a post-Release 1 version of this document. This targeting applies
          to all ToDos in this chapter.

The Package Standard (A.1)
--------------------------

|SPARK| supports all of the types, subtypes and operators declared in package Standard.
The predefined exceptions are considered to be declared in Standard, but their use is
constrained by other language restrictions.

The Package Ada (A.2)
---------------------

No additions or restrictions.

.. todo:: Should we say here which packages are supported in |SPARK| or which ones aren't
   supported?  How much of the standard library will be available, and in which run-time
   profiles?

Character Handling (A.3)
------------------------

The Packages Characters, Wide_Characters, and Wide_Wide_Characters (A.3.1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No additions or restrictions.  As in Ada, the wide character sets
provided are |SPARK| tool, compiler and platform dependent.


The Package Characters.Handling (A.3.2)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No additions or restrictions.

The Package Characters.Latin_1 (A.3.3)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No additions or restrictions.

The Package Characters.Conversions (A.3.4)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No Additions or restrictions.

The Package Wide_Characters.Handling (A.3.5)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No additions or restrictions.

The Package Wide_Wide_Characters.Handling (A.3.6)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No additions or restrictions.

String Handling (A.4)
---------------------

No additions or restrictions.

The Package Strings (A.4.1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~

No additions or restrictions.

The predefined exceptions are considered to be declared in Stings, but their use is
constrained by other language restrictions.

.. _example_of_assert:

The Package Strings.Maps (A.4.2)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


1. The type declaration Character_Mapping_Function is not in |SPARK| and
   cannot be referenced within |SPARK| program text.


The function To_Mapping may raise the exception Translation_Error if
its actual parameters are inconsistent.  To guard against this
exception each call of To_Mapping should be immediately preceded by an
assert statement checking that the actual parameters are correct.

.. centered:: **Examples**

.. code-block:: ada

   --  From the Ada RM for To_Mapping: "To_Mapping produces a
   --  Character_Mapping such that each element of From maps to the
   --  corresponding element of To, and each other character maps to
   --  itself. If From'Length /= To'Length, or if some character is
   --  repeated in From, then Translation_Error is propagated".

   --  Each call should be preceded with a pragma Assert, checking the
   --  actual parameters, of the form:
   pragma Assert (Actual_From'Length = Actual_To'Length and then
                    (for all I in Actual_From'Range =>
                       (for all J in Actual_From'Range =>
                          (if I /= J then Actual_From (I) /= Actual_From (J)))));
   CM := To_Mapping (From => Actual_From,
                     To   => Actual_To);

   --  Alternatively To_Mapping could be wrapped in a user defined
   --  subprogram with a suitable precondition and used to call
   --  To_Mapping indirectly.  For example:
   function My_To_Mapping (From, To : in Character_Sequence)
                          return Character_Mapping
     with Pre => (From'Length = To'Length and then
                    (for all I in From'Range =>
                       (for all J in From'Range =>
                          (if I /= J then From (I) /= From (J)))));
   is
   begin
      return Ada.Strings.Maps.To_Mapping (From, To);
   end My_To_Mapping;

Fixed-Length String Handling (A.4.3)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


1. Translate (with Maps.Character_Mapping_Function formal parameter)
   is not callable from |SPARK| as it has a an access to function type
   parameter.


All other subprograms may be called but the subprograms Move, Index,
Count (with a mapping formal parameter), Find_Token, Replace_Slice,
Insert, Overwrite, Head (with Justify formal parameter), Tail (with
Justify formal parameter) may raise an exception if they are called
with inconsistent actual parameters. Each call of these subprograms
should be preceded with a pragma Assert to check that the actual
parameters are consistent.

Bounded-Length String Handling (A.4.4)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


1. The subprograms Index, Count and Translate with
   Maps.Character_Mapping_Function formal parameters are not callable
   from |SPARK|.


The other subprograms in Bounded-Length String Handling are callable
from |SPARK| program texts but many of them may raise an exception if
they are called with inconsistent actual parameters.  Each call of
these subprograms should be preceded with a pragma Assert to check
that the actual parameters are consistent.

Unbounded-Length String Handling (A.4.5)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


1. The type String_Access and the procedure Free are not in |SPARK| as
   they require non-owning access types and cannot be denoted in
   |SPARK| program text.


2. The subprograms Index, Count and Translate with
   Maps.Character_Mapping_Function formal parameters are not callable
   from |SPARK|.


The function and procedure Unbounded_Slice both may propagate
Index_Error if Low > Length(Source)+1 or High > Length(Source) and so
every call to each of these subprograms should be immediately preceded
by a pragma Assert of the form:

.. code-block:: ada

   pragma Assert (Actual_Low  <= Length (Actual_Source) and
                  Actual_High <= Length (Actual_Source));

String-Handling Sets and Mappings (A.4.6)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No additions or restrictions.

Wide_String Handling (A.4.7)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~


1. The types Wide_String_Access and Wide_Character_Mapping_Function
   are not in |SPARK| nor are the subprograms which have formal
   parameters of these types and cannot be denoted in |SPARK| program
   texts.


Each call of a subprogram which may raise an exception if it is called
with inconsistent actual parameters should be immediately preceded by
a pragma Assert checking the consistency of the actual parameters.

Wide_Wide_String Handling (A.4.8)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


1. The types Wide_Wide_String_Access and Wide_Wide_Character_Mapping_Function
   are not in |SPARK| nor are the subprograms which have formal
   parameters of these types and cannot be denoted in |SPARK| program
   texts.


Each call of a subprogram which may raise an exception if it is called
with inconsistent actual parameters should be immediately preceded by
a pragma Assert checking the consistency of the actual parameters.

String Hashing (A.4.9)
~~~~~~~~~~~~~~~~~~~~~~

No additions or restrictions.

String Comparison (A.4.10)
~~~~~~~~~~~~~~~~~~~~~~~~~~

No additions or restrictions.

String Encoding (A.4.11)
~~~~~~~~~~~~~~~~~~~~~~~~

The subprograms of this package are callable from |SPARK| but those
that may raise an exception due to inconsistent parameters should have
a pragma Assert confirming that the actual parameters are consistent
immediately preceding each call of such a subprogram.

The Numerics Packages (A.5)
---------------------------

No additions or restrictions

Elementary Functions (A.5.1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Most of the elementarty functions may raise an exception.  The
functions have no preconditions to guard against an exception being
raised. The functions should be treated as tested code and call of an
elementary function should be immediately preceded by a pragma assert
in lieu of a precondition.

For instance a call to Log (X, Base) should be immediately preceded by
the assert statement:

.. code-block:: ada

  pragma Assert (X > 0  and Base > 1);

Even with such a guard certain elementary functions may raise a
constraint error. The onus is on the user to ensure this does not
happen or is handled in non-|SPARK| text in a manner compatible with
|SPARK|.

Random Number Generation (A.5.2)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The package Ada.Numerics.Float_Random and an instantiation of package
Ada.Numerics.Discrete_Random is ostensibly in |SPARK| but the functions
have side effects and should not be called from |SPARK| text.

Input-Output (A.6)
------------------

No additions or restrictions.

External Files and File Objects (A.7)
-------------------------------------

No additions or restrictions.

Sequential and Direct Files (A.8)
---------------------------------

No additions or restrictions.

The Generic Package Sequential_IO (A.8.1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An instantiation of Sequential_IO will ostensibly be in |SPARK| but in
use it may give rise to flow-errors as the effect of reads and writes
is not captured in the subprogram contracts. Calls to its subprograms
may raise IO_Exceptions based on external events.

File Management (A.8.2)
~~~~~~~~~~~~~~~~~~~~~~~

No additions or restrictions.

Sequential Input-Output Operations (A.8.3)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
No additions or restrictions.

The Generic Package Direct_IO (A.8.4)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An instantiation of Direct_IO will ostensibly be in |SPARK| but in use
it may give rise to flow-errors as the effect of reads and writes is
not captured in the subprogram contracts. Calls to its subprograms may
raise IO_Exceptions based on external events.


Direct Input-Output Operations (A.8.5)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No additions or restrictions.

The Generic Package Storage_IO (A.9)
------------------------------------

An instantiation of Storage_IO will ostensibly be in |SPARK| but in
use it may give rise to flow-errors as the effect of reads and writes
is not captured in the subprogram contracts. Calls to its subprograms
may raise IO_Exceptions based on external events.

Text Input-Output (A.10)
------------------------

No additions or restrictions.

The Package Text_IO (A.10.1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Ada.Text_IO is ostensibly in |SPARK| except for the type File_Access, a
generalized access type, thus preventing Ada.Text_IO from being declared with
SPARK_Mode On explicitly in the visible part. The following subprograms are
explicitly marked as SPARK_Mode Off:

- The functions Current_Input, Current_Output, Current_Error, Standard_Input,
  Standard_Output and Standard_Error because they create aliasing, by returning
  the corresponding file.

- The procedures Set_Input, Set_Output and Set_Error because they also create
  aliasing, by assigning a File_Type variable to respectively Current_Input,
  Current_Output or Current_Error.

- Functions Get_Line because they have a side effect of reading data from a
  file and updating its file pointers.

The abstract state File_System declared in Ada.Text_IO is used to model the
memory on the system and the file handles (Line_Length, Col, etc.). This is
made necessary by the fact that almost every procedure in Text_IO that actually
modifies attributes of its File_Type parameter takes it as an **in** parameter.

All functions and procedures are annotated with Global, and Pre/Post when
possible. The Global contracts are typically In_Out for File_System,
even in Put or Get procedures that update the current column and/or
line. Functions have an Input global contract. The only functions with Global
=> null are the functions Get and Put in the generic packages that have
the same behavior as sprintf and sscanf.

Preconditions are not always complete, as not all conditions
leading to run-time exceptions can be effectively modelled in SPARK:

- Status_Error (due to a file already open/not open) is fully modelled

- Mode_Error (due to a violation of the internal state machine) is fully
  modelled

- Layout_Error is partially modelled

- Use_Error is not modelled (it is related to the external environment)

- Name_Error is not modelled (it would require checking availability on disk
  beforehand)

- End_Error is not modelled (it is raised when a file terminator is read while
  running the procedure)

In the exceptional cases that are not fully modelled, it is possible that SPARK
tools do not issue a possible precondition failure message on a call, yet an
exception can be raised at run-time. See the spec files for the exact
contracts.

Text File Management (A.10.2)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The possibility of errors related to the actual content or limitations of the
file system are not modelled (e.g. when trying to create an already existing
file, or open a file that does not exist).

Preconditions and postconditions are added to describe other constraints.

Default Input, Output and Error Files (A.10.3)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Apart from procedure Flush, all other subprograms are explicitly marked as
SPARK_Mode Off, as described above, because they create aliasing.

Specification of Line and Page Lengths (A.10.4)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Global, preconditions and postconditions are added to subprograms.

Operations on Columns, Lines and Pages (A.10.5)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Global, preconditions and postconditions are added to subprograms.

Get and Put Procedures (A.10.6)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Global, preconditions and postconditions are added to subprograms.

Input-Output of Characters and Strings (A.10.7)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Functions Get_Line are explicitly marked as SPARK_Mode Off, as described above,
because they have side effects.

Global, preconditions and postconditions are added to other subprograms.

Input-Output for Integer Types (A.10.8)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Global, preconditions and postconditions are added to subprograms.

Input-Output for Real Types (A.10.9)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Global, preconditions and postconditions are added to subprograms.

Input-Output for Enumeration Types (A.10.10)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Global, preconditions and postconditions are added to subprograms.

Input-Output for Bounded Strings (A.10.11)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An instantiation of Bounded_IO will ostensibly be in |SPARK| but in
use it may give rise to flow-errors as the effect of reads and writes
is not captured in the subprogram contracts. Calls to its subprograms
may raise IO_Exceptions based on external events.

Input-Output of Unbounded Strings (A.10.12)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Ada.Text_IO.Unbounded_IO is ostensibly in |SPARK| but in use it may
give rise to flow-errors as the effect of reads and writes is not
captured in the subprogram contracts. Calls to its subprograms may
raise IO_Exceptions based on external events.

The functions Ada.Text_IO.Unbounded_IO.Get_Line should not be called
from |SPARK| program text as the functions have a side effect of
reading from a file.

Wide Text Input-Output and Wide Wide Text Input-Output (A.11)
-------------------------------------------------------------

These packages have the same constraints as was discussed for Ada.Text_IO.

Stream Input-Output (A.12)
--------------------------

Stream input and output is not supported by |SPARK| and the use of the
package Ada.Streams.Stream_IO and the child packages of Ada.Text_IO
concerned with streams is not permitted in |SPARK| program text.

Exceptions in Input-Output (A.13)
---------------------------------

The exceptions declared in package Ada.IO_Exceptions which are raised
by the Ada input-output subprograms are in |SPARK| but the exceptions
cannot be handled in |SPARK| program text.

File Sharing (A.14)
-------------------

File sharing is not permitted in |SPARK|, since it may introduce an alias.

The Package Command_Line (A.15)
-------------------------------

The package Command_Line is in |SPARK| except that the function
Argument may propagate Constraint_Error. To avoid this exception each
call to Argument should be immediately preceded by the assertion:

.. code-block:: ada

   pragma Assert (Number <= Argument_Count);

where Number represents the actual parameter to the function Argument.

The Package Directories (A.16)
------------------------------

The package Directories is ostensibly in |SPARK| but in use it may
give rise to flow-errors as the effect of reads and writes is not
captured in the subprogram contracts. Calls to its subprograms may
raise IO_Exceptions based on external events.

The Package Environment_Variables (A.17)
----------------------------------------

The package Environment_Variables is ostensibly mostly in |SPARK| but
in use it may give rise to flow-errors as the effect of reads and
writes is not captured in the subprogram contracts. Calls to its
subprograms may raise IO_Exceptions based on external events.

The procedure Iterate is not in |SPARK|.

Containers (A.18)
-----------------

The standard Ada container libraries are not supported in |SPARK|.

An implementation may choose to provide alternative container
libraries whose specifications are in |SPARK| and are intended to
support formal verification.

The Package Locales (A.19)
--------------------------

No additions or restrictions.

Interface to Other Languages (Annex B)
--------------------------------------

This section describes features for mixed-language programming in
|SPARK|, covering facilities offered by Ada's Annex B.

Package ``Interfaces`` can be used in |SPARK|, including its
intrinsic "Shift" and "Rotate" functions.

Other packages are not directly supported.

Systems Programming (Annex C)
-----------------------------

This section describes features for systems programming in
|SPARK|, covering facilities offered by Ada's Annex C.

Almost all of the facilities offered by this Annex are
out of scope for |SPARK| and so are not supported.

Pragma Discard_Names (C.5)
~~~~~~~~~~~~~~~~~~~~~~~~~~

Pragma Discard_Names is not permitted in |SPARK|, since its
use can lead to implementation defined behaviour at run time.

Shared Variable Control (C.6)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following restrictions are applied to the declaration of volatile types
and objects in |SPARK|:

.. centered:: **Legality Rules**


1. A volatile representation aspect may only be applied to an
   ``object_declaration`` or a ``full_type_declaration``.


2. A type which is not effectively volatile shall not have a
   volatile subcomponent.

.. todo:: This may require determining whether a private type is volatile.

.. todo:: The above two rules may be relaxed in a future version.


3. A discriminant shall not be volatile.


4. Neither a discriminated type nor an object of such a type shall be volatile.


5. Neither a tagged type nor an object of such a type shall be volatile.


6. An effectively volatile object shall only be declared at library-level.


Real-Time Systems (Annex D)
---------------------------

|SPARK| supports the parts of the real-time systems annex that comply with the
Ravenscar profile (see Ada RM D.13) or the Extended Ravenscar profile
(see docs.adacore.com/gnathie_ug-docs/html/gnathie_ug/gnathie_ug/the_predefined_profiles.html#the-extended-ravenscar-profiles). See section
:ref:`tasks-and-synchronization`.

Distributed Systems (Annex E)
-----------------------------

|SPARK| does not support the distributed systems annex.

Information Systems (Annex F)
-----------------------------

The ``Machine_Radix`` aspect and attribute are permitted in |SPARK|.

The package ``Ada.Decimal`` may be used, although it declares
constants whose values are implementation defined.

The packages ``Ada.Text_IO.Editing`` and its "Wide" variants are
not directly supported in |SPARK|.

Numerics (Annex G)
------------------

This section describes features for numerical programming in |SPARK|,
covering facilities offered by Ada's Annex G.

Packages declared in this Annex are usable in |SPARK|, although
many details are implementation defined.

Implementations (both compilers and verification tools) should
document how both *strict mode* and *relaxed mode* are implemented
and their effect on verification and performance.

High Integrity Systems (Annex H)
--------------------------------

|SPARK| fully supports the requirements of Ada's Annex H.
