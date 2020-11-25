Object Oriented Programming and Liskov Substitution Principle
=============================================================

|SPARK| supports safe Object Oriented Programming by checking behavioral
subtyping between parent types and derived types, a.k.a. Liskov Substitution
Principle: every overriding operation of the derived type should behave so that
it can be substituted for the corresponding overridden operation of the parent
type anywhere.

.. index:: Pre'Class
           Post'Class
           precondition; on dispatching operation
           postcondition; on dispatching operation

Class-Wide Subprogram Contracts
-------------------------------

[Ada 2012]

Specific :ref:`Subprogram Contracts` are required on operations of tagged
types, so that |GNATprove| can check Liskov Substitution Principle on every
overriding operation:

* The `class-wide precondition` introduced by aspect ``Pre'Class`` is similar
  to the normal precondition.
* The `class-wide postcondition` introduced by aspect ``Post'Class`` is similar
  to the normal postcondition.

Although these contracts are defined in Ada, they have a stricter meaning
in |SPARK| for checking Liskov Substitution Principle:

* The class-wide precondition of an overriding operation should be weaker (more
  permissive) than the class-wide precondition of the corresponding overridden
  operation.
* The class-wide postcondition of an overriding operation should be stronger
  (more restrictive) than the class-wide postcondition of the corresponding
  overridden operation.

For example, suppose that the ``Logging`` unit introduced in :ref:`Ghost
Packages` defines a tagged type ``Log_Type`` for logs, with corresponding
operations:

.. literalinclude:: /examples/tests/logging/logging.ads
   :language: ada
   :linenos:

and that this type is derived in ``Range_Logging.Log_Type`` which additionally
keeps track of the minimum and maximum values in the log, so that they can be
accessed in constant time:

.. literalinclude:: /examples/tests/range_logging/range_logging.ads
   :language: ada
   :linenos:

|GNATprove| proves that the contracts on ``Logging.Append_To_Log`` and its
overriding ``Range_Logging.Append_To_Log`` respect the Liskov Substitution
Principle:

.. literalinclude:: /examples/tests/range_logging/test.out
   :language: none

Units ``Logging`` and ``Range_Logging`` need not be implemented, or available,
or in |SPARK|. It is sufficient that the specification of ``Logging`` and
``Range_Logging`` are in |SPARK| for this checking. Here, the postcondition of
``Range_Logging.Append_To_Log`` is strictly stronger than the postcondition of
``Logging.Append_To_Log``, as it also specifies the new expected value of the
minimum and maximum values. The preconditions of both procedures are exactly
the same, which is the most common case, but in other cases it might be useful
to be more permissive in the overriding operation's precondition. For example,
``Range_Logging.Append_To_Log`` could allocate dynamically additional memory
for storing an unbounded number of events, instead of being limited to
``Max_Count`` events like ``Logging.Append_To_Log``, in which case its
precondition would be simply ``True`` (the default precondition).

A derived type may inherit both from a parent type and from one or more
interfaces, which only provide abstract operations and no
components. |GNATprove| checks Liskov Substitution Principle on every
overriding operation, both when the overridden operation is inherited from the
parent type and when it is inherited from an interface.

|GNATprove| separately checks that a subprogram implements its class-wide
contract, like for a specific contract.

Mixing Class-Wide and Specific Subprogram Contracts
---------------------------------------------------

[Ada 2012]

It is possible to specify both a specific contract and a class-wide contract on
a subprogram, in order to use a more precise contract (the specific one) for
non-dispatching calls and a contract compatible with the Liskov Substitution
Principle (the class-wide contract) for dispatching calls. In that case,
|GNATprove| checks that:

* The specific precondition is weaker (more permissive) than the class-wide precondition.
* The specific postcondition is stronger (more restrictive) than the class-wide
  postcondition.

For example, ``Logging.Append_To_Log`` could set a boolean flag
``Special_Value_Logged`` when some ``Special_Value`` is appended to the log,
and express this property in its specific postcondition so that it is available
for analyzing non-dispatching calls to the procedure:

.. code-block:: ada

   procedure Append_To_Log (Log : in out Log_Type; Incr : in Integer) with
     Pre'Class  => Log.Log_Size < Max_Count,
     Post'Class => Log.Log_Size = Log.Log_Size'Old + 1,
     Post       => Log.Log_Size = Log.Log_Size'Old + 1 and
                   (if Incr = Special_Value then Special_Value_Logged = True);

This additional postcondition would play no role in dispatching calls, thus it
is not involved in checking the Liskov Substitution Principle. Note that the
absence of specific precondition on procedure ``Append_To_Log`` does not mean
that the default precondition of ``True`` is used: as a class-wide precondition
is specified on procedure ``Append_To_Log``, it is also used as specific
precondition. Similarly, if a procedure has a class-wide contract and a
specific precondition, but no specific postcondition, then the class-wide
postcondition is also used as specific postcondition.

When both a specific contract and a class-wide contract are specified on a
subprogram, |GNATprove| only checks that the subprogram implements its specific
(more precise) contract.

Dispatching Calls and Controlling Operands
------------------------------------------

[Ada 2012]

In a dispatching call, the *controlling operand* is the parameter of class-wide
type whose dynamic type determinates the actual subprogram called. The dynamic
type of this controlling operand may be any type derived from the specific type
corresponding to the class-wide type of the parameter (the specific type is
``T`` when the class-wide type is ``T'Class``). Thus, in general it is not
possible to know in advance which subprograms may be called in a dispatching
call, when separately analyzing a unit.

In |SPARK|, there is no need to know all possible subprograms called in order
to analyze a dispatching call, which makes it possible for |GNATprove| to
perform this analysis without knowledge of the whole program. As |SPARK|
enforces Liskov Substitution Principle, the class-wide contract of an
overriding operation is always less restrictive than the class-wide contract of
the corresponding overridden operation. Thus, |GNATprove| uses the class-wide
contract of the operation for the specific type of controlling operand to
analyze a dispatching call.

For example, suppose a global variable ``The_Log`` of class-wide type defines
the log that should be used in the program:

.. code-block:: ada

   The_Log : Logging.Log_Type'Class := ...

The call to ``Append_To_Log`` in procedure ``Add_To_Total`` may dynamically
call either ``Logging.Append_To_Log`` or ``Range_Logging.Append_To_Log``:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) is
   begin
      Total := Total + Incr;
      The_Log.Append_To_Log (Incr);
   end Add_To_Total;

Because |GNATprove| separately checks Liskov Substitution Principle for
procedure ``Append_To_Log``, it can use the class-wide contract of
``Logging.Append_To_Log`` for analyzing procedure ``Add_To_Total``.

.. index:: Extensions_Visible

Dynamic Types and Invisible Components
--------------------------------------

[|SPARK|]

The :ref:`Data Initialization Policy` in |SPARK| applies specially to objects
of tagged type. In general, the dynamic type of an object of tagged type may be
different from its static type, hence the object may have invisible components,
that are only revealed when the object is converted to a class-wide type.

For objects of tagged type, modes on parameters and data dependency contracts
have a different meaning depending on the object's static type:

* For objects of a specific (not class-wide) tagged type, the constraints
  described in :ref:`Data Initialization Policy` apply to the visible
  components of the object only.

* For objects of a class-wide type, the constraints described in :ref:`Data
  Initialization Policy` apply to all components of the object, including
  invisible ones.

|GNATprove| checks during flow analysis that no uninitialized data is read in
the program, and that the specified data dependencies and flow dependencies are
respected in the implementation, based on the semantics above for objects of
tagged type. For example, it detects no issues during flow analysis on
procedure ``Use_Logging`` which initializes parameter ``Log`` and then updates
it:

.. literalinclude:: /examples/tests/use_logging/use_logging.adb
   :language: ada
   :linenos:

If parameter ``Log`` is of dynamic type ``Logging.Log_Type``, then the call to
``Init_Log`` initializes all components of ``Log`` as expected, and the call to
``Append_To_Log`` can safely read those. If parameter ``Log`` is of dynamic
type ``Range_Logging.Log_Type``, then the call to ``Init_Log`` only initializes
those components of ``Log`` that come from the parent type
``Logging.Log_Type``, but since the call to ``Append_To_Log`` only read those,
then there is no read of uninitialized data. This is in contrast with what
occurs in procedure ``Use_Logging_Classwide``:

.. literalinclude:: /examples/tests/use_logging_classwide/use_logging_classwide.adb
   :language: ada
   :linenos:

on which |GNATprove| issues a check message during flow analysis:

.. literalinclude:: /examples/tests/use_logging_classwide/test.out
   :language: none
   :lines: 2-4

Indeed, the call to ``Init_Log`` (a non-dispatching call to
``Logging.Init_Log`` due to the conversion on its parameter) only initializes
those components of ``Log`` that come from the parent type
``Logging.Log_Type``, but the call to ``Append_To_Log`` may read other
components from ``Range_Logging.Log_Type`` which may not be initialized.

A consequence of these rules for data initialization policy is that a parameter
of a specific tagged type cannot be converted to a class-wide type, for example
for a dispatching call. A special aspect ``Extensions_Visible`` is defined in
|SPARK| to allow this case. When ``Extensions_Visible`` is specified on a
subprogram, the data initialization policy for the subprogram parameters of a
specific tagged type requires that the constraints described in :ref:`Data
Initialization Policy` apply to all components of the object, as if the
parameter was of a class-wide type. This allows converting this object to a
class-wide type.
