.. _tasks-and-synchronization:

Tasks and Synchronization
=========================

Tasks and protected types are in |SPARK|, but are subject to the
restrictions of the Ravenscar profile (see Ada RM D.13). In particular,
task entry declarations are never in |SPARK|.

Tasks may communicate with each other via synchronized objects; these include
protected objects, suspension objects, atomic objects, constants, and
"constant after elaboration" objects (described later).

Other objects are said to be unsynchronized and may only be referenced
(directly or via intermediate calls) by a single task (including the
environment task) or by the protected operations of a single protected object.

These rules statically eliminate the possibility of erroneous concurrent
access to shared data (i.e., "data races").

Tagged task types, tagged protected types, and the various forms of
synchronized interface types are in |SPARK|. Subject to the restrictions
of Ravenscar, delay statements and protected procedure handlers are
in |SPARK|. The attributes Callable, Caller, Identity and Terminated
are in |SPARK|.

.. centered:: **Static Semantics**

1.  A type is said to *yield synchronized objects* if it is
    a task type, a protected type, a synchronized interface type,
    an array type whose element type yields synchronized objects,
    an undiscriminated type (or a discriminated type
    whose discriminants lack default values) all of whose
    nondiscriminant component types
    (including, in the case of a type extension, inherited components),
    yield synchronized objects, or it is a descendant of the type
    Ada.Synchronous_Task_Control.Suspension_Object;

   An object is said to be *synchronized* if it is

  * of a type which yields synchronized objects; or

  * an atomic object whose Async_Writers aspect is True; or

  * a variable which is "constant after elaboration" (see section
    :ref:`object-declarations`); or

  * a constant.

  [Synchronized objects may be referenced by multiple tasks without causing
  erroneous execution. The declaration of a synchronized stand-alone
  variable shall be a library-level declaration.]

.. centered:: **Legality Rules**

.. _tu-tasks_and_synchronization-01:

2. Task and protected units are in |SPARK|, but their use requires
   the Ravenscar Profile. [In other words, a task or protected unit
   is not in |SPARK| if the Ravenscar profile does not apply to the
   enclosing compilation unit.] Similarly, the use of task or protected units
   also requires a Partition_Elaboration_Policy of Sequential. [This
   is to prevent data races during library unit elaboration.]
   Similarly, the use of any subprogram which references the
   predefined state abstraction Ada.Task_Identification.Tasking_State
   (described below) as a global requires the Ravenscar Profile.

3. If a variable or a package which declares a state abstraction is declared
   within the same declarative region as a ``single_task_declaration`` or a
   ``single_protected_declaration``, then the Part_Of aspect of the variable
   or state abstraction may denote the protected or task object. This indicates
   that the object or state abstraction is not part of the visible state
   or private state of its enclosing package. [Loosely speaking, flow
   analysis will treat the object as though it were declared within
   its "owner". This can be useful if, for example, a protected object's
   operations need to reference an object whose Address aspect is specified.
   The protected (as opposed to task) case corresponds to the previous notion
   of "virtual protected" objects in RavenSPARK.]

4. A protected type shall define full default initialization.
   A variable whose Part_Of aspect specifies a task unit or protected unit
   shall be of a type which defines full default initialization, or
   shall be declared with an initial value expression, or shall be
   imported.

5. A type which does not yield synchronized objects shall not have
   a component type which yields synchronized objects.
   [Roughly speaking, no mixing of synchronized and unsynchronized
   component types.]

6. A constituent of a synchronized state abstraction shall be a
   synchronized object or a synchronized state abstraction.

.. centered:: **Verification Rules**

7. A ``global_item`` occurring in a Global aspect specification of a
   task unit or of a protected operation shall not denote an object
   or state abstraction which is not synchronized unless the
   Part_Of aspect of the object or state abstraction denotes the
   task or protected unit.

8. A ``global_item`` occurring in the Global aspect specification of
   the main subprogram shall not denote an object or state abstraction
   whose Part_Of aspect denotes a task or protected unit. [In other words,
   the environment task cannot reference objects which "belong" to other
   tasks.]

9. A state abstraction whose Part_Of aspect specifies a task unit or
   protected unit shall be named in the Initializes aspect of its
   enclosing package.

10. A ``global_item`` occurring in the Global aspect specification of the
    main subprogram or of a task unit having a mode of Output or In_Out shall
    not denote a variable whose Constant_After_Elaboration aspect is True.

11. At most one task (including the environment task)
    shall ever call (directly or via intermediate calls) the protected
    entry (if any) of a given protected object. [Roughly speaking, each
    protected object which has an entry can be statically identified with
    its "suspender task" and no other task shall call the entry of that
    protected object. This rule is enforced via (potentially conservative)
    flow analysis, as opposed to by introducing verification conditions.
    This rule discharges the verification condition associated with Ravenscar's
    "Max_Entry_Queue_Length => 1" restriction.]

    For purposes of this rule, Ada.Synchronous_Task_Control.Suspension_Object
    is assumed to be a protected type having an entry and the procedure
    Suspend_Until_True is assumed to contain a call to the entry of its
    parameter. [This rule discharges the verification condition associated with
    the Ada rule that two tasks cannot simultaneously suspend on one
    suspension object (see Ada RM D.10(10)).]

12. The verification condition associated with the Ada rule that it is a bounded
    error to invoke an operation that is potentially blocking during a
    protected action (see Ada RM 9.5.1(8)) is discharged via (potentially
    conservative) flow analysis, as opposed to by introducing verification
    conditions. [Support for the "Potentially_Blocking" aspect discussed in
    AI12-0064 may be incorporated into |SPARK| at some point in the future.]

    The verification condition associated with the Ada rule that
    it is a bounded error to call the Current_Task function from an
    entry_body, or an interrupt handler is discharged similarly.

13. The end of a task body shall not be reachable. [This follows from
    from Ravenscar's No_Task_Termination restriction.]

14. A nonvolatile function shall not be potentially blocking.
    [Strictly speaking this rule is already implied by other rules of |SPARK|,
    notably the rule that a nonvolatile function cannot depend on a volatile
    input.]
    [A dispatching call which statically denotes a primitive subprogram
    of a tagged type T is a potentially blocking operation if
    the corresponding primitive operation of any descendant of T is
    potentially blocking.]

15. The package Ada.Task_Identification declares a synchronized
    external state abstraction named Tasking_State. The package
    Ada.Real_Time declares a synchronized external state abstraction named
    Clock_Time. The Async_Readers and Async_Writers aspects of both state
    abstractions are True, and their Effective_Reads and Effective_Writes
    aspects are False.
    For each of the following language-defined functions, the
    Volatile_Function aspect of the function is defined to be True
    and the Global aspect of the function specifies that one of these
    two state abstractions is referenced as an Input global:

  * Ada.Real_Time.Clock references Ada.Real_Time.Clock_Time;

  * Ada.Execution_Time.Clock references Ada.Real_Time.Clock_Time;

  * Ada.Execution_Time.Interrupts.Clock
    references Ada.Real_Time.Clock_Time;

  * Ada.Execution_Time.Interrupts.Clock_For_Interrupts
    references Ada.Real_Time.Clock_Time;

  * Ada.Task_Identification.Current_Task
    references Ada.Task_Identification.Tasking_State;

  * Ada.Task_Identification.Is_Terminated
    references Ada.Task_Identification.Tasking_State;

  * Ada.Task_Identification.Is_Callable
    references Ada.Task_Identification.Tasking_State;

  * Ada.Task_Identification.Activation_Is_Complete
    references Ada.Task_Identification.Tasking_State;

  * Ada.Dispatching.EDF.Get_Deadline
    references Ada.Task_Identification.Tasking_State.

  * Ada.Interrupts.Is_Reserved
    references Ada.Task_Identification.Tasking_State.

  * Ada.Interrupts.Is_Attached
    references Ada.Task_Identification.Tasking_State.

  * Ada.Interrupts.Detach_Handler
    references Ada.Task_Identification.Tasking_State.

  * Ada.Interrupts.Get_CPU
    references Ada.Task_Identification.Tasking_State.

  * Ada.Synchronous_Task_Control.Current_State
    references Ada.Task_Identification.Tasking_State;

  [Functions already excluded by Ravenscar, such as Ada.Calendar.Clock, are
  not on this list.]

16. For each of the following language-defined procedures, the
    Global aspect of the procedure specifies that the
    state abstraction Ada.Task_Identification.Tasking_State
    is referenced as an In_Out global:

  * Ada.Interrupts.Detach_Handler.

17. For purposes of determining global inputs and outputs, a delay
    statement is considered to reference the state abstraction
    Ada.Real_Time.Clock_Time as an input.
    [In other words, a delay statement can be treated like a call to
    a procedure which takes the delay expression as an actual parameter
    and references the Clock_Time state abstraction as an Input global.]

18. For purposes of determining global inputs and outputs, a use of
    any of the Callable, Caller, Count, or Terminated attributes is considered
    to reference the state abstraction
    Ada.Task_Identification.Tasking_State as an Input.
    [In other words, evaluation of one of these attributes can be treated
    like a call to a volatile function which takes the attribute prefix
    as a parameter (in the case where the prefix denotes an object or value)
    and references the Tasking_State state abstraction as an Input global.]
    [On the other hand, use of the Identity, Priority, or Storage_Size
    attributes introduces no such dependency.]

19. Preconditions are added to suprogram specifications as needed in order
    to avoid the failure of language-defined runtime checks for the
    following subprograms:

  * for Ada.Execution_Time.Clock, T does not equal
    Task_Identification.Null_Task_Id .

  * for Ada.Execution_Time.Interrupts.Clock,
    Separate_Interrupt_Clocks_Supported is True.

  * for Ada.Execution_Time's arithmetic and conversion operators (including
    Time_Of), preconditions are defined to ensure that the result belongs to
    the result type.

  * for Ada.Real_Time's arithmetic and conversion operators (including Time_Of),
    preconditions are defined to ensure that the result belongs to the
    result type.

20. All procedures declared in the visible part of Ada.Synchronous_Task_Control
    have a dependency "(S => null)" despite the fact that S has mode **in
    out**. Procedure Suspend_Until_True is defined to be potentially blocking.

.. _etu-tasks_and_synchronization:
