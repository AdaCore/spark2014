``Ada.Text_IO``
===============

State abstraction
-----------------

There is only one abstract state in the library, ``File_System``. It
includes the "memory" on the system, but also the file handles.
(``Line_Length``, ``Col``, etc.) This is explained by the fact that
almost every procedure in ``Text_IO`` has ``in File_Type`` as input and
not ``in out``, in procedures that actually modify attributes of the
``File_Type``. Therefore, it was mandatory to have a ``In_Out`` global
contract on an abstract state which includes the files handles. No
information is lost when including the file handles as well in the
``File_System``.

``Is_Open`` and ``Mode`` are not included in ``File_System`` because
every procedure that modifies these predicates and attributes have a
``in out
File_Type``, which is correct.

I also have considered that the abstract state was not volatile.

Errors Handling
---------------

Full handling
~~~~~~~~~~~~~

``Status_Error`` (due to a file already open/not open) are fully
handled. This is happening because we consider that the "openness" of a
file is stored in the ``File_Type``.

``Mode_Error`` are also fully handled. The mode of a file is actually
stored in the ``File_Type``.

This is possible to do because every procedure that modifies the
``Is_Open`` predicate or the ``Mode`` of a file has a ``in out File`` in
input. It is great because this error is the most common (almost every
procedure has a precondition on ``Is_Open`` and ``Mode``).

Partial handling
~~~~~~~~~~~~~~~~

For an ``Out_File``, it is possible to set a ``Line_Length`` and
``Page_Length``. When writing in this file, the procedures will add Line
markers and Page markers each ``Line_Length`` characters or
``Page_Length`` lines respectively. ``Layout_Error`` occurs when trying
to set the current column or line to a value that is greater than
``Line_Length`` or ``Page_Length`` respectively. This error is handled
when using ``Set_Col`` or ``Set_Line`` procedures.

However, this error is not handled when no ``Line_Length`` or
``Page_Length`` has been specified.

    The column number, line number, or page number are allowed to exceed
    Count'Last (as a consequence of the input or output of sufficiently
    many characters, lines, or pages). These events do not cause any
    exception to be propagated. However, a call of ``Col``, ``Line``, or
    ``Page`` propagates the exception ``Layout_Error`` if the
    corresponding number exceeds ``Count'Last``. ---ADA RM A.10.5(51)

e.g, if the lines are unbounded, it is possible to have a ``Col``
greater than ``Count'Last`` and therefore have a ``Layout_Error`` raised
when calling ``Col``.

No handling
~~~~~~~~~~~

All other errors are not handled:

-  ``Use_Error`` is related to the external environment.

-  ``Name_Error`` would require to check availability on disk beforehand
   and this would complicate the process to check.

-  ``End_Error`` is raised when a file terminator is read while running
   the procedure. I don't think it is possible to specify precondition
   easily without running the procedure itself.

Trade-offs
~~~~~~~~~~

The main trade-off is about the handling of ``Layout_Error``. Not only
the handling is partial, but it is also impossible to prove
preconditions when working with two files or more. Since ``Line_Length``
etc. attributes are stored in the ``File_System``, it is not posible to
prove that the ``Line_Length`` of ``File_2`` has not been modified when
running a procedure on ``File_1``. As said Yannick in a mail, it's more
on the safe side. It is important to keep in mind that ``Layout_Error``
will not be handled fully.

GNAT patch
----------

Abstract state and global contracts
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Refinement of the abstract state was necessary because it is not possible
to put ``SPARK_Mode`` on the spec: there is an access type in the public
part of the spec. All functions and procedures were annoted with Global,
and Pre, Post if necessary. The Global contracts are most of the time
``In_Out`` for ``File_System``, even in ``Put`` or ``Get`` procedures
that update the current column and/or line. Functions have an ``Input``
global contract. The only functions with ``Global => null`` are the
functions ``Get`` and ``Put`` in the generic packages that have a
similar behaviour as sprintf and sscanf.

``SPARK_Mode => Off``
~~~~~~~~~~~~~~~~~~~~~

Some functions and procedures were removed from SPARK because they
created problems.

#. Aliasing

   The functions ``Current_Input``, ``Current_Output`` and
   ``Current_Error``, ``Standard_Input``, ``Standard_Output`` and
   ``Standard_Error`` were turned off in ``SPARK_Mode`` because they
   created aliasing (they return the corresponding file).

   ``Set_Input``, ``Set_Output`` and ``Set_Error`` were turned off
   because they also created aliasing, when assigning a ``File`` to
   ``Current_Input`` or the other two.

   It is still possible to use ``Set_Input`` and the 3 others to make
   the code clearer. This is doable by calling ``Set_Input`` in a
   different subprogram whose body has ``SPARK_Mode => Off``. However,
   users have to ensure themselves that the file is open and the mode is
   correct, because there are no checks made on procedures that does not
   take a file in input. (i.e. implicit, so it will write to/read from
   the current output/input)

#. ``Get_Line`` function

   The function ``Get_Line`` was removed from SPARK because it is a
   function with side effects. Even with the volatile attribute, it was
   not possible to modelize its action on the files and global variables
   in SPARK. The function is very convenient because it returns an
   unconstrained string, but a workaround with Unbounded strings and a
   loop will be possible to do and is safer.

Evolution
---------

Data races
~~~~~~~~~~

One of the remaining diffs I have to deal when calling ``Text_IO``
procedures from different tasks. I get the high: possible data race when
running a proof on the file. I asked ada-lawyers@ whether the procedures
in ``Text_IO`` were thread safe or not. The explicit (when specifying a
file) ones are thread safe, but functions that have an effect on
``Current_Input`` or ``Current_Output``, i.e the implicit ones, are not.

Consequences for the abstract state
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If we decide to mark the abstract state as ``Synchronous``, I have to
remove the ``Current_Files`` from it and create a different abstract
state for these, but I won't mark it as ``Synchronous``. I would also
have to set ``Async_Writers``, ``Async_Readers``, ``Effective_Reads``
and ``Effective_Writes`` to false for ``File_System``, which is
currently not possible.

I suggest that I push the modifications with what I have done, and if
later you allow all 4 aspects to be set to false, I'll come back to add
more precision on multitasking.h
