Tasks and Synchronization
=========================

Tasks and protected types are in |SPARK|, but are subject to the
restrictions of the Ravenscar profile (see Ada RM D.13). In particular,
task entry declarations are never in |SPARK|.

Tasks may communicate with each other via synchronized objects; these include
protected objects, suspension objects, atomic objects, constants, and
“constant after elaboration” objects (described later).

Other objects are said to be unsynchronized and may only be referenced
(directly or via intermediate calls) by a single task (including the
environment task) or by the protected operations of a single protected object.

These rules statically eliminate the possibility of erroneous concurrent
access to shared data (i.e., "data races").
 
Tagged task types, tagged protected types, and the various forms of
synchronized interface types are in |SPARK|.

.. centered:: **Static Semantics**

1.  A type is said to be *yield synchronized objects* if it is
    a task type, a protected type, a synchronized interface type,
    an array type whose element type yields synchronized objects,
    an undiscriminated type (or a discriminated type
    whose discriminants lack default values) all of whose
    non-discriminant component types
    (including, in the case of a type extension, inherited components),
    yield synchronized objects, or it is a descendant of the type
    Ada.Synchronous_Task_Control.Suspension_Object;

   An object is said to be *synchronized* if it is

  * of a type which yields synchronized objects; or

  * an atomic object; or

  * a variable which is "constant after elaboration" (see TBD); or

  * a constant.

  [Synchronized objects may be referenced by multiple tasks without causing
  erroneous execution.]

.. centered:: **Legality Rules**

.. _tu-tasks_and_synchronization-01:

2. Task and protected units are in |SPARK|, but their use requires
   the Ravenscar Profile. [In other words, a task or protected unit
   is not in |SPARK| if the Ravenscar profile does not apply to the
   enclosing compilation unit.] Similarly, the use of task or protected units
   also requires a Partition_Elaboration_Policy of Sequential. [This
   is to prevent race conditions during library unit elaboration.]

3. A ''global_item'' occurring in a Global aspect specification of a
   task unit or of a protected operation shall not denote an object
   or state abstraction which is not synchronized unless the
   Part_Of aspect of the object or state abstraction denotes the
   task or protected unit.

4. A ``global_item`` occurring in the Global aspect specification of
   the main subprogram shall not denote an object or state abstraction
   whose Part_Of aspect denotes a task or protected unit. [In other words,
   the environment task cannot reference objects which "belong" to other
   tasks.]
   
5. If a variable or a package which declares a state abstraction is declared
   within the same declarative region as a ``single_task_declaration`` or a
   ``single_protected_declaration``, then the Part_Of aspect of the variable
   or state abstraction may denote the protected or task object. This indicates
   that the object or state abstraction is not part of the visible state
   or private state of its enclosing package. [Loosely speaking, flow
   analysis will treat the object as though it were declared within
   its "owner". This can be useful if, for example, a protected object's
   operations need to reference an object whose Address aspect is specified.
   The protected (as opposed to task) case corresponds to RavenSpark's
   "virtual protected" objects.]

6. A protected type shall define full default initialization.
   A variable whose Part_Of aspect specifies a task unit or protected unit
   shall be of a type which defines full default initialization, or
   shall be declared with an initial value expression, or shall be
   imported.
   A state abstraction whose Part_Of aspect specifies a task unit or
   protected unit shall be named in the Initializes aspect of its
   enclosing package.

7. A type which does not yield synchronized objects shall not have
   a component type which yields synchronized objects.
   [Roughly speaking, no mixing of synchronized and unsynchronized
   component types.]

8. A constituent of a synchronized state abstraction shall be a
   synchronized object or a synchronized state abstraction.
   
.. centered:: **Verification Rules**

9. A ``global_item`` occurring in the Global aspect specification of the
   main subprogram or of a task unit having a mode of Output or In_Out shall
   not denote a variable whose Constant_After_Elaboration aspect is True.

10. At most one task (including the environment task)
    shall ever call (directly or via intermediate calls) the protected
    entry (if any) of a given protected object. [Roughly speaking, each
    protected object which has an entry can be statically identified with
    its "suspender task" and no other task shall call the entry of that 
    protected object. This rule is enforced via (potentially conservative)
    flow analysis, as opposed to by introducing verification conditions.
    This rule discharges the proof obligation associated with Ravenscar's
    "Max_Entry_Queue_Length => 1" restriction.]

    For purposes of this rule, Ada.Synchronous_Task_Control.Suspension_Object
    is assumed to be a protected type having an entry and the procedure
    Suspend_Until_True is assumed to contain a call to the entry of its
    parameter. [This rule discharges the proof obligation associated with
    the Ada rule that two tasks cannot simultaneously suspend on one
    suspension object (see Ada RM D.10(10)).]

11. The proof obligation associated with the Ada rule that it is a bounded
    error to invoke an operation that is potentially blocking during a
    protected action (see Ada RM 9.5.1(8)) is discharged via (potentially
    conservative) flow analysis, as opposed to by introducing verification
    conditions. [Support for the "Nonblocking" aspect discussed in AI12-0064
    may be incorporated into |SPARK| at some point in the future.].

12. The end of a task body shall not be reachable. [This follows from
    from Ravenscar's No_Task_Termination restriction.]

13. A non-volatile function shall not contain a delay statement,
    a call to Suspend_Until_True, a call a protected entry,
    a call a volatile function, or a call (directly or via dispatching)
    a subprogram which contains such a construct.

14. The following language-defined functions are defined to be
    volatile functions:

  * Ada.Real_Time.Clock

  * Ada.Execution_Time.Clock

  * Ada.Execution_Time.Interrupts.Clock and Clock_For_Interrupts

  * Ada.Execution_Time.Interrupts.Clock_For_Interrupts

  * Ada.Task_Identification.Current_Task

  * Ada.Task_Identification.Is_Terminated

  * Ada.Task_Identification.Is_Callable

  * Ada.Task_Identification.Activation_Is_Complete

  * Ada.Dispatching.EDF.Get_Deadline

  [Functions already excluded by Ravenscar, such as Ada.Calendar.Clock, are
  not on this list.]

15. Preconditions are added to suprogram specifications as needed in order
    to avoid the failure of language-defined runtime checks for the
    following subprograms:

  * TBD (e.g., Ada.Execution_Time.Clock must not be passed a null Task_Id)

.. _etu-tasks_and_synchronization:

