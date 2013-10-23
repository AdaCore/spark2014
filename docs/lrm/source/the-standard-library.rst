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

[A future version of |SPARK| may provide suitable preconditions on
library subprograms but to avoid semantic differences between the Ada
and |SPARK| and views of the library subprograms such preconditions
require the use of exception expressions which are not currently
supported by |SPARK|.]


.. todo:: Provide detail on Standard Libraries.
          To be completed in a post-Release 1 version of this document. This targeting applies
          to all ToDos in this chapter.

.. todo:: In particular, it is intended that predefined container generics
          suitable for use in |SPARK| will be provided. These will
          have specifications as similar as possible to those of
          Ada's bounded containers (i.e., Ada.Containers.Bounded_*), but with
          constructs removed or modified as needed in order to maintain the
          language invariants that |SPARK| relies upon in providing
          formal program verification.

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

The Package SPARK (A.2.1)
~~~~~~~~~~~~~~~~~~~~~~~~~

The package SPARK serves essentially the same purpose in |SPARK| as
the package Ada in Ada.  It is the root of SPARK library packages
which are either unique to SPARK or are an alternative to an
equivalent Ada package which is not compatible with SPARK.

It contains the declaration of the file types used in |SPARK| for the
input-output packages which are children of SPARK.

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

.. _tu-nk-the-package-strings.maps-01:

1. The type declaration Character_Mapping_Function is not in |SPARK| and 
   cannot be referenced within |SPARK| program text.

.. _etu-the-package-strings.maps:

The function To_Mapping may raise the exception Translation_Error if
its actual parameters are inconsistent.  To guard against this
exception each call of To_Mapping should be immediately preceded by an
assert statement checking that the actual parameters are correct.

.. centered:: **Examples**

.. code-block:: ada

   -- From the Ada RM for To_Mapping: "To_Mapping produces a
   -- Character_Mapping such that each element of From maps to the
   -- corresponding element of To, and each other character maps to
   -- itself. If From'Length /= To'Length, or if some character is
   -- repeated in From, then Translation_Error is propagated".

   -- Each call should be preceded with a pragma Assert, checking the actual 
   -- parameters, of the form:
   pragma Assert (Actual_From'Length = Actual_To'Length and then 
                    (for all I in Actual_From'Range => (for all J in Actual_From'Range => 
                        if I /= J then Actual_From (I) /= Actual_From (J))));
   CM := To_Mapping (From => Actual_From, To => Actual_To);

   -- Alternatively To_Mapping could be wrapped in a user defined subprogram with a 
   -- suitable precondition and used to call To_Mapping indirectly.  For example:
   function My_To_Mapping (From, To : in Character_Sequence)
      return Character_Mapping with
      Pre => (From'Length = To'Length and then 
                       (for all I in From'Range => (for all J in From'Range => 
                           if I /= J then From (I) /= From (J))));
    is
    begin
      return (Ada.Strings.Maps.To_Mapping (From, To);
    end My_To_Mapping;

Fixed-Length String Handling (A.4.3)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _tu-nk-fixed-length-string-handling-01:

1. Translate (with Maps.Character_Mapping_Function formal parameter)
   is not callable from |SPARK| as it has a an access to function type
   parameter.

.. _etu-fixed-length-string-handling:

All other subprograms may be called but the subprograms Move, Index,
Count (with a mapping formal parameter), Find_Token, Replace_Slice,
Insert, Overwrite, Head (with Justify formal parameter), Tail (with
Justify formal parameter) may raise an exception if they are called
with inconsistent actual parameters.  Each call of these subprograms
should be preceded with a pragma Assert to check that the actual
parameters are consistent.

Bounded-Length String Handling (A.4.4)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _tu-nk-bounded-length-string-handling-01:

1. The subprograms Index, Count and Translate with
   Maps.Character_Mapping_Function formal parameters are not callable
   from |SPARK|.

.. _etu-bounded-length-string-handling:

The other subprograms in Bounded-Length String Handling are callable
from |SPARK| program texts but many of them may raise an exception if
they are called with inconsistent actual parameters.  Each call of
these subprograms should be preceded with a pragma Assert to check
that the actual parameters are consistent.

Unbounded-Length String Handling (A.4.5)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _tu-nk-unbounded-length-string-handling-01:

1. The type String_Access and the procedure Free are not in |SPARK| as
   they require access types and cannot be denoted in |SPARK| program text.

.. _tu-nk-unbounded-length-string-handling-02:

2. The subprograms Index, Count and Translate with
   Maps.Character_Mapping_Function formal parameters are not callable
   from |SPARK|.

.. _etu-unbounded-length-string-handling:

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

.. _tu-nk-wide-string-handling-01:

1. The types Wide_String_Access and Wide_Character_Mapping_Function
   are not in |SPARK| nor are the subprograms which have formal
   parameters of these types and cannot be denoted in |SPARK| program
   texts.

.. _teu-wide-string-handling:

Each call of a subprogram which may raise an exception if it is called
with inconsistent actual parameters should be immediately preceded by
a pragma Assert checking the consistency of the actual parameters.

Wide_Wide_String Handling (A.4.8)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. _tu-nk-wide-wide-string-handling-01:

1. The types Wide_String_Access and Wide_Character_Mapping_Function
   are not in |SPARK| nor are the subprograms which have formal
   parameters of these types and cannot be denoted in |SPARK| program
   texts.

.. _teu-wide-wide-string-handling:

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

Input-Output (A.6)
------------------

Alternative |SPARK| language-defined packages are provided for input and
output to be used rather than the standard Ada input and output
packages.  Each |SPARK| input and output package is a child of the root
package SPARK.  Details of the |SPARK| input output packages are given
in the following subsections.
   
External Files and File Objects (A.7)
-------------------------------------

Equivalent |SPARK| types are derived from the types described in this section.

Sequential and Direct Files (A.8)
---------------------------------

No additions or restrictions.

The Generic Package Sequential_IO (A.8.1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An instantiation of Sequential_IO will ostensibly be in |SPARK| but in
use it may give rise to flow-errors as the effect of reads and writes
is not captured in the subprogram contracts. Calls to its subprograms
may raise IO_Exceptions based on external events.

A |SPARK| version of this generic package is not yet available.

File Management (A.8.2)
~~~~~~~~~~~~~~~~~~~~~~~

Equivalent |SPARK| versions of the subprograms described in this
section are provided where required.

Sequential Input-Output Operations (A.8.3)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Equivalent |SPARK| versions of the subprograms described in this
section are provided where required.

The Generic Package Direct_IO (A.8.4)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An instantiation of Direct_IO will ostensibly be in |SPARK| but in
use it may give rise to flow-errors as the effect of reads and writes
is not captured in the subprogram contracts. Calls to its subprograms
may raise IO_Exceptions based on external events.

A |SPARK| version of this generic package is not yet available.

Direct Input-Output Operations (A.8.5)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Equivalent |SPARK| versions of the subprograms described in this
section are provided where required.

The Generic Package Storage_IO (A.9)
------------------------------------

An instantiation of Storage_IO will ostensibly be in |SPARK| but in
use it may give rise to flow-errors as the effect of reads and writes
is not captured in the subprogram contracts. Calls to its subprograms
may raise IO_Exceptions based on external events.

A |SPARK| version of this generic package is not yet available.

Text Input-Output (A.10)
------------------------

Equivalent |SPARK| types are derived from the types described in this section.

The Package Text_IO (A.10.1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Ada.Text_IO is ostensibly in |SPARK| except for the type File_Access
and the functions which return this type. The use Ada.Text_IO may give
rise to flow-errors as the effect of reads and writes is not captured
in the subprogram contracts.  The Ada.Text_IO.Get_Line functions
should not be called as they have a side effect of reading data from a
file and updating its file pointers.  The subprograms Set_Input,
Set_Output and Set_Error should not be called as they introduce an
alias to the file passed as a parameter.  Calls to the subprograms of
Ada.Text_IO may raise IO_Exceptions based on external events.

A |SPARK| version of this package, SPARK.Text_IO, is available and it
is strongly recommended that this is used instead of Ada.Text_IO.

The Package SPARK.Text_IO (A.10.1.1)
####################################

The package SPARK.Text_IO provides equivalent types and subprograms to
nearly all of the types and subprograms declared in Ada.Text_IO.  The
differences are:

   - the subprograms of SPARK.Text_IO do not raise the predefined
     IO_Exceptions each file has a status that may be queried to
     ascertain the success or failure of an operation.  The possible
     Status of a file correspond to the IO_Exceptions that may be
     raised by subprograms of Ada.Text_IO;

   - the formal parameters of File_Type for Create and Open are mode
     **out** rather than **in out** avoiding flow errors regarding the
     use of uninitialized variables;

   - the formal parameters of File_Type of subprograms which read and
     write to files or change the properties of a file are mode **in
     out** rather than mode **in** to indicate that the operation has
     an effect on the file;

   - the use of **in out** parameters means that Standard_Input,
     Standard_Output and Standard_Error are variables rather than
     functions.  These variables are pre-declared in SPARK.Text_IO;

   - the results of read operations are a discriminated type, the
     returned object only has a value if the operation is a success;

   - using a discriminated result type allows the Get_Line procedure
     to return a dynamically sized string and subsume the need for a
     Get_Line function which is not allowed in |SPARK|;

   - The default file is always Standard_Input for read operations or
     Standard_Output for write operations and cannot be changed; and

   - the subprograms have pre and postconditions to support formal
     proofs to demonstrate that they are used correctly.

For details of SPARK.Text_IO see the comments in the package specification.

Text File Management (A.10.2)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

|SPARK| equivalents of the subprograms mentioned in this section are
 provided in SPARK.Text_IO.  They provide the same functionality but
 return a status rather than raising an exception.

Default Input, Output and Error Files (A.10.3)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The subprograms Ada.Text_IO.Set_Input, Ada.Text_IO.Set_Output and
Ada.Text_IO.Set_Error should not be called from |SPARK| program text
as they introduce an alias of the file parameter.  

In SPARK.Text_IO the default input is always Standard_Input and the
default output is always Standard_Output and so the above subprograms
are not supported, neither are the functions Current_Input,
Current_Output or Current_Error.  The subprogram Flush is supported by
SPARK.Text_IO.

Specification of Line and Page Lengths (A.10.4)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

|SPARK| equivalents of the subprograms described in this section are
provided in SPARK.Text_IO.

Operations on Columns, Lines and Pages (A.10.5)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

|SPARK| equivalents of the subprograms described in this section are
provided in SPARK.Text_IO.

Get and Put Procedures (A.10.6)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

|SPARK| equivalents of the subprograms described in this section are
provided in SPARK.Text_IO.
 
Input-Output of Characters and Strings (A.10.7)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The functions Ada.Text_IO.Get_Line should not be called from |SPARK|
program text as the functions have a side effect of reading from a file.

|SPARK| equivalents of the subprograms described in this section are
provided in SPARK.Text_IO. The SPARK.Text_IO.Get_Line provides the
functionality of the function Ada.Text_IO.Get_Line.
 
Input-Output for Integer Types (A.10.8)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

|SPARK| equivalents of the subprograms described in this section are
provided in SPARK.Text_IO.
 
Input-Output for Real Types (A.10.9)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

|SPARK| equivalents of the subprograms described in this section are
provided in SPARK.Text_IO.
 
Input-Output for Enumeration Types (A.10.10)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

|SPARK| equivalents of the subprograms described in this section are
provided in SPARK.Text_IO.
 
Input-Output for Bounded Strings (A.10.11)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An instantiation of Bounded_IO will ostensibly be in |SPARK| but in
use it may give rise to flow-errors as the effect of reads and writes
is not captured in the subprogram contracts. Calls to its subprograms
may raise IO_Exceptions based on external events.

A |SPARK| version of this generic package is not yet available.
 
Input-Output of Unbounded Strings (A.10.12)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Ada.Text_IO.Unbounded_IO is ostensibly in |SPARK| but in
use it may give rise to flow-errors as the effect of reads and writes
is not captured in the subprogram contracts. Calls to its subprograms
may raise IO_Exceptions based on external events.

The functions Ada.Text_IO.Unbounded_IO.Get_Line should not be called
from |SPARK| program text as the functions have a side effect of
reading from a file.

|SPARK| equivalents of the subprograms described in this section are
provided in SPARK.Text_IO.Unbounded_IO. The
SPARK.Text_IO.Unbounded_IO.Get_Line provides the functionality of the
function Ada.Text_IO.Unbounded_IO.Get_Line.
 
Wide Text Input-Output and Wide Wide Text Input-Output (A.11)
-------------------------------------------------------------

These packages have the same constraints as was discussed for Ada.Text_IO.

Currently there is no |SPARK| version of these packages.

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

The package SPARK.Text_IO provides an equivalent set of subprograms
that do not raise these exceptions.  Instead the file affected by a
subprogram call has a status that can be read.  The status values
correspond in name to the exceptions declared in this package.

File Sharing (A.14)
-------------------

File sharing is not permitted in |SPARK|, it introduces an alias.

The Package Command_Line (A.15)
-------------------------------

The package Command_Line is in |SPARK| except that the function Argument may propagate Constraint_Error.  To avoid this exception each call to Argument should be immediately preceded by the assertion:

.. code-block:: ada

  pragma Assert (Number <= Argument_Count);

where Number represents the actual parameter to the function Argument.

The Package Directories (A.16)
------------------------------

The package Directories is ostensibly in |SPARK| but in
use it may give rise to flow-errors as the effect of reads and writes
is not captured in the subprogram contracts. Calls to its subprograms
may raise IO_Exceptions based on external events.

A |SPARK| equivalent of this package is not provided yet.

The Package Environment_Variables (A.17)
----------------------------------------

The package Environment_Variables is ostensibly mostly in |SPARK| but
in use it may give rise to flow-errors as the effect of reads and
writes is not captured in the subprogram contracts. Calls to its
subprograms may raise IO_Exceptions based on external events.

The procedure Iterate is not in |SPARK|.

A |SPARK| equivalent of this package is not provided yet.

Containers (A.18)
-----------------

Work in progress.

The Package Locales (A.19)
--------------------------

No additions or restrictions.

Interface to Other Languages 
----------------------------

This section describes features for mixed-language programming in |SPARK|, covering facilities
offered by Ada's Annex B.

.. todo:: How much to say here?  S95 supports a subset of Interfaces, and a very small subset of
   Interfaces.C but that's about it. 

.. todo:: What is status of supported for pragma ``Unchecked_Union`` in GNATProve at present?

Systems Programming
-------------------

tbd.

Real-Time Systems
-----------------

This section describes features for real-time programming in |SPARK|, covering facilities
offered by Ada's Annex D.

.. todo:: RCC: Need to think about Ada.Real_Time.  It's important for all S95 customers, to get
   at monotonic clock, even if not using RavenSPARK.  It does depend on support for external
   variables, though, since Ada.Real_Time.Clock is most definitely Volatile. TN [LB07-024]
   raised to discuss this.

Distributed Systems
-------------------

TBD.

Information Systems
-------------------

TBD.

Numerics
--------

This section describes features for numerical programming in |SPARK|, covering facilities
offered by Ada's Annex G.

.. todo:: How much here can be supported?  Most S95 customers want Ada.Numerics.Generic_Elementary_Functions
   plus its predefined instantiation for Float, Long_Float and so on.  How far should we go?

High Integrity Systems
----------------------

|SPARK| fully supports the requirements of Ada's Annex H.




