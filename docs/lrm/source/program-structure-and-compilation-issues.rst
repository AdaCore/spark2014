Program Structure and Compilation Issues
========================================

|SPARK| supports constructive, modular analysis. This means that analysis may be
performed before a program is complete based on unit interfaces. For instance,
to analyze a subprogram which calls another all that is required is a
specification of the called subprogram including, at least, its
``global_specification`` and if formal verification of the calling program is to
be performed, then the Pre and Postcondition of the called subprogram need to
be provided. The body of the called subprogram does not need to be implemented
to analyze the caller. The body of the called subprogram is checked to be
conformant with its specification when its implementation code is available and
analyzed.

The separate compilation of Ada ``compilation_units`` is consistent with
|SPARK| modular analysis except where noted in the following subsections but,
particularly with respect to incomplete programs, analysis does not involve the
execution of the program.


Separate Compilation
--------------------

.. centered:: **Legality Rules**

.. _tu-separate_compilation-01:

1. A program unit cannot be a task unit, a protected unit or a protected entry.

.. _etu-separate_compilation:

Compilation Units - Library Units
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No restrictions or extensions.

Context Clauses - With Clauses
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**

.. _tu-context_clauses_with_clauses-01:

1. With clauses are always in |SPARK|, even if the unit mentioned is
   not completely in |SPARK|.

.. _etu-context_clauses_with_clauses-lr:

Abstract Views
^^^^^^^^^^^^^^

State abstractions are visible in the limited view of packages in |SPARK|. The
notion of an *abstract view* of an object declaration is also introduced, and
the limited view of a package includes the abstract view of any objects
declared in the visible part of that package. The only allowed uses of an
abstract view of an object are where the use of a state abstraction would be
allowed (for example, in a Global ``aspect_specification``).

.. centered:: **Legality Rules**

.. _tu-context_clauses_with_clauses-02:

2. A name denoting the abstract view of an object shall occur only:

   a. as a ``global_item`` in a Global or Refined_Global aspect
      specification; or

   b. as an ``input`` or ``output`` in a Depends or Refined_Depends
      aspect specification; or

   c. in an ``input_list`` of an Initializes aspect.

.. _etu-context_clauses_with_clauses_abstract_view-lr:

.. centered:: **Static Semantics**

.. _tu-context_clauses_with_clauses-03:

3. Any state abstractions declared within a given package are present in
   the limited view of the package.
   [This means that, for example, a Global ``aspect_specification`` for a
   subprogram declared in a library unit package *P1* could refer to a state
   abstraction declared in a package *P2* if *P1* has a limited with of *P2*.]

.. _tu-context_clauses_with_clauses-04:

4. For every object declared by an ``object_declaration`` occurring
   immediately within the visible part of a given package, the limited
   view of the package contains an *abstract view* of the object.

.. _tu-context_clauses_with_clauses_abstract_view-ss:


Subunits of Compilation Units
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No restrictions or extensions.

The Compilation Process
~~~~~~~~~~~~~~~~~~~~~~~

The analysis process in |SPARK| is similar to the compilation process in Ada
except that the ``compilation_units`` are analyzed, that is flow analysis and
formal verification is performed, rather than compiled.

Pragmas and Program Units
~~~~~~~~~~~~~~~~~~~~~~~~~

No restrictions or extensions.

Environment-Level Visibility Rules
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No restrictions or extensions.

Program Execution
-----------------

|SPARK| analyses do not involve program execution.  However, |SPARK| programs
are executable including those new language defined aspects and pragmas where
they have dynamic semantics given.

Elaboration Control
~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.
