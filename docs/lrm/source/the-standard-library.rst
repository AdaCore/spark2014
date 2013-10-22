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

External Files and File Objects (A.7)
-------------------------------------

Sequential and Direct Files (A.8)
---------------------------------

The Generic Package Storage_IO (A.9)
------------------------------------

Text Input-Output (A.10)
------------------------

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




