.. _tasks-and-synchronization:

Tasks and Synchronization
=========================

Tasks and protected types are in |SPARK|, but are subject to the
restrictions of the Ravenscar profile (see Ada RM D.13) or
the more permissive Extended Ravenscar profile (see
http://docs.adacore.com/gnathie_ug-docs/html/gnathie_ug/gnathie_ug/the_predefined_profiles.html#the-extended-ravenscar-profiles ). In particular,
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
of (extended) Ravenscar, delay statements and protected procedure handlers are
in |SPARK|. The attributes Callable, Caller, Identity and Terminated
are in |SPARK|.

.. centered:: **Static Semantics**

1. A type is said to *yield synchronized objects* if it is

   * a task type; or

   * a protected type; or

   * a synchronized interface type; or

   * an array type whose element type yields synchronized objects; or

   * a record type or type extension whose discriminants, if any, lack default
     values, which has at least one nondiscriminant component (possibly
     inherited), and all of whose nondiscriminant component types
     yield synchronized objects; or

   * a descendant of the type Ada.Synchronous_Task_Control.Suspension_Object; or

   * a private type whose completion yields synchronized objects.

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

.. _tu-tasks_and_synchronization-02:

2. Task and protected units are in |SPARK|, but their use requires
   the (extended) Ravenscar profile. [In other words, a task or protected unit
   is not in |SPARK| if neither the Ravenscar profile nor the Extended
   Ravenscar profile apply to the enclosing compilation unit.]
   Similarly, the use of task or protected units
   also requires a Partition_Elaboration_Policy of Sequential. [This
   is to prevent data races during library unit elaboration.]
   Similarly, the use of any subprogram which references the
   predefined state abstraction Ada.Task_Identification.Tasking_State
   (described below) as a global requires the (extended) Ravenscar profile.

.. _tu-tasks_and_synchronization-03:

3. If the declaration of a variable or a package which declares a
   state abstraction follows (within the same immediately enclosing
   declarative region) a ``single_task_declaration`` or a
   ``single_protected_declaration``, then the Part_Of aspect of the variable
   or state abstraction may denote the task or protected unit. This indicates
   that the object or state abstraction is not part of the visible state
   or private state of its enclosing package. [Loosely speaking, flow
   analysis will treat the object as though it were declared within
   its "owner". This can be useful if, for example, a protected object's
   operations need to reference an object whose Address aspect is specified.
   The protected (as opposed to task) case corresponds to the previous notion
   of "virtual protected elements" in RavenSPARK.]

   An object or state abstraction which "belongs" to a task unit in this way
   is treated as a local object of the task (e.g., it cannot be
   named in a Global aspect specification occurring outside of the body
   of the task unit, just as an object declared immediately within the task
   body could not be).
   An object or state abstraction which "belongs" to a protected unit in this
   way is treated as a component of the (anonymous) protected type
   (e.g., it can never be named in any Global aspect specification, just as
   a protected component could not be). [There is one obscure exception
   to these rules, described in the next paragraph: a subprogram which
   is declared within the statement list of the body of the immediately
   enclosing package (this is possible via a block statement).]

   Any name denoting such an object or state abstraction
   shall occur within either

   * the body of the "owning" task or protected unit; or

   * the statement list of the object's immediately enclosing package; or

   * an Initializes or Initial_Condition aspect specification for
     the object's immediately enclosing package.

   [Roughly speaking, such an object can only be referenced from
   within the "owning" unit or during the execution of the statement
   list of its enclosing package].

   The notional equivalences described above break down in the case of
   package elaboration.
   The presence or absence of such a Part_Of aspect specification
   is ignored in determining the legality of an Initializes or
   Initial_Condition aspect specification.
   [Very roughly speaking, the restrictions implied by such
   a Part_Of aspect specification are not really "in effect" during
   library unit elaboration; or at least that's one way to view it. For example
   such an object can be accessed from within the elaboration code of its
   immediately enclosing package. On the other hand, it could not be accessed
   from within a subprogram unless the subprogram is declared within either
   the task unit body in question (in the task case) or within
   the statement list of the body of the immediately enclosing package
   (in either the task or the protected case).]

.. _tu-tasks_and_synchronization-04:

4. A protected type shall define full default initialization.
   A variable whose Part_Of aspect specifies a task unit or protected unit
   shall be of a type which defines full default initialization, or
   shall be declared with an initial value expression, or shall be
   imported.

.. _tu-tasks_and_synchronization-05:

5. A type which does not yield synchronized objects shall not have
   a component type which yields synchronized objects.
   [Roughly speaking, no mixing of synchronized and unsynchronized
   component types.]

.. _tu-tasks_and_synchronization-06:

6. A constituent of a synchronized state abstraction shall be a
   synchronized object or a synchronized state abstraction.

.. _etu-tasks_and_synchronization-lr:

.. centered:: **Verification Rules**

.. _tu-tasks_and_synchronization-07:

7. A ``global_item`` occurring in a Global aspect specification of a
   task unit or of a protected operation shall not denote an object
   or state abstraction which is not synchronized.

.. _tu-tasks_and_synchronization-08:

8. A ``global_item`` occurring in the Global aspect specification of
   the main subprogram shall not denote an object or state abstraction
   whose Part_Of aspect denotes a task or protected unit. [In other words,
   the environment task cannot reference objects which "belong" to other
   tasks.]

.. _tu-tasks_and_synchronization-09:

9. A state abstraction whose Part_Of aspect specifies a task unit or
   protected unit shall be named in the Initializes aspect of its
   enclosing package.

.. _tu-tasks_and_synchronization-10:

10. The precondition of a protected operation shall not reference a global
    variable, unless it is *constant after elaboration*.

.. _tu-tasks_and_synchronization-11:

11. The Ravenscar profile includes "Max_Entry_Queue_Length => 1" and
    "Max_Protected_Entries => 1" restrictions.
    The Extended Ravenscar profile does not, but does allow use of
    pragma Max_Queue_Length to specify the maximum entry queue length
    for a particular entry. If the maximum queue length for some given
    entry of some given protected object is specified (via either mechanism)
    to have the value N, then at most N distinct tasks (including the
    environment task) shall ever call (directly or via intermediate calls)
    the given entry of the given protected object. [Roughly speaking, each
    such protected entry can be statically identified with a set of at most N
    "caller tasks" and no task outside that set shall call the entry.
    This rule is enforced via (potentially conservative)
    flow analysis, as opposed to by introducing verification conditions.]

    For purposes of this rule, Ada.Synchronous_Task_Control.Suspension_Object
    is assumed to be a protected type having one entry and the procedure
    Suspend_Until_True is assumed to contain a call to the entry of its
    parameter. [This rule discharges the verification condition associated with
    the Ada rule that two tasks cannot simultaneously suspend on one
    suspension object (see Ada RM D.10(10)).]

.. _tu-tasks_and_synchronization-12:

12. The verification condition associated with the Ada rule that it is a bounded
    error to invoke an operation that is potentially blocking
    (including due to cyclic locking) during a
    protected action (see Ada RM 9.5.1(8)) is discharged via (potentially
    conservative) flow analysis, as opposed to by introducing verification
    conditions. [Support for the "Potentially_Blocking" aspect discussed in
    AI12-0064 may be incorporated into |SPARK| at some point in the future.]

    The verification condition associated with the Ada rule that
    it is a bounded error to call the Current_Task function from an
    entry_body, or an interrupt handler (see Ada RM C.7.1(17/3))
    is discharged similarly.

    The verification condition associated with the Ada rule that
    the active priority of a caller of a protected operation is not higher
    than the ceiling of the corresponding protected object (see Ada RM
    D.3(13)) is dependent on (potentially conservative) flow analysis.
    This flow analysis is used to determine which tasks potentially call
    (directly or indirectly)
    a protected operation of which protected objects, and similarly
    which protected objects have protected operations that potentially
    perform calls (directly or indirectly) on the operations of other
    protected objects.  A verification condition is created for each
    combination of potential (task or protected object) caller and called
    protected object to ensure that the (task or ceiling) priority of the
    potential caller is no greater than the ceiling priority of the called
    protected object.

.. _tu-tasks_and_synchronization-13:

13. The end of a task body shall not be reachable. [This follows from
    from (extended) Ravenscar's No_Task_Termination restriction.]

.. _tu-nt-tasks_and_synchronization-14:

14. A nonvolatile function shall not be potentially blocking.
    [Strictly speaking this rule is already implied by other rules of |SPARK|,
    notably the rule that a nonvolatile function cannot depend on a volatile
    input.]
    [A dispatching call which statically denotes a primitive subprogram
    of a tagged type T is a potentially blocking operation if
    the corresponding primitive operation of any descendant of T is
    potentially blocking.]

.. _tu-nt-tasks_and_synchronization-15:

15. The package Ada.Task_Identification declares (and initializes)
    a synchronized external state abstraction named Tasking_State.
    The packages Ada.Real_Time and Ada.Calendar declare (and initialize)
    synchronized external state abstractions named Clock_Time.
    The Async_Readers and Async_Writers aspects of all those state
    abstractions are True, and their Effective_Reads and Effective_Writes
    aspects are False.
    Each is listed in the Initializes aspect of its respective package.
    For each of the following language-defined functions, the
    Volatile_Function aspect of the function is defined to be True
    and the Global aspect of the function specifies that one of these
    two state abstractions is referenced as an Input global:

  * Ada.Real_Time.Clock references Ada.Real_Time.Clock_Time;

  * Ada.Execution_Time.Clock references Ada.Real_Time.Clock_Time;

  * Ada.Execution_Time.Clock_For_Interrupts
    references Ada.Real_Time.Clock_Time;

  * Ada.Execution_Time.Interrupts.Clock
    references Ada.Real_Time.Clock_Time;

  * Ada.Calendar.Clock (which is excluded by the Ravenscar profile
    but not by the Extended Ravenscar profile) references
    Ada.Calendar.Clock_Time;

  * Ada.Task_Identification.Current_Task
    references Ada.Task_Identification.Tasking_State;

  * Ada.Task_Identification.Is_Terminated
    references Ada.Task_Identification.Tasking_State;

  * Ada.Task_Identification.Is_Callable
    references Ada.Task_Identification.Tasking_State;

  * Ada.Task_Identification.Activation_Is_Complete
    references Ada.Task_Identification.Tasking_State;

  * Ada.Dispatching.EDF.Get_Deadline
    references Ada.Task_Identification.Tasking_State;

  * Ada.Interrupts.Is_Reserved
    references Ada.Task_Identification.Tasking_State;

  * Ada.Interrupts.Is_Attached
    references Ada.Task_Identification.Tasking_State;

  * Ada.Interrupts.Detach_Handler
    references Ada.Task_Identification.Tasking_State;

  * Ada.Interrupts.Get_CPU
    references Ada.Task_Identification.Tasking_State;

  * Ada.Synchronous_Task_Control.Current_State
    references Ada.Task_Identification.Tasking_State.

  [Functions excluded by the Extended Ravenscar profile (and
  therefore also by the Ravenscar profile) are not on this list.]

.. _tu-nt-tasks_and_synchronization-16:

16. For each of the following language-defined procedures, the
    Global aspect of the procedure specifies that the
    state abstraction Ada.Task_Identification.Tasking_State
    is referenced as an In_Out global:

  * Ada.Interrupts.Detach_Handler.

.. _tu-tasks_and_synchronization-17:

17. For purposes of determining global inputs and outputs, a delay
    statement is considered to reference the state abstraction
    Ada.Real_Time.Clock_Time as an input.
    [In other words, a delay statement can be treated like a call to
    a procedure which takes the delay expression as an actual parameter
    and references the Clock_Time state abstraction as an Input global.]

.. _tu-tasks_and_synchronization-18:

18. For purposes of determining global inputs and outputs, a use of
    any of the Callable, Caller, Count, or Terminated attributes is considered
    to reference the state abstraction
    Ada.Task_Identification.Tasking_State as an Input.
    [In other words, evaluation of one of these attributes can be treated
    like a call to a volatile function which takes the attribute prefix
    as a parameter (in the case where the prefix denotes an object or value)
    and references the Tasking_State state abstraction as an Input global.]
    [On the other hand, use of the Identity or Storage_Size
    attributes introduces no such dependency.]

.. _tu-nt-tasks_and_synchronization-19:

19. Preconditions are added to suprogram specifications as needed in order
    to avoid the failure of language-defined runtime checks for the
    following subprograms:

  * for Ada.Execution_Time.Clock, T does not equal
    Task_Identification.Null_Task_Id.

  * for Ada.Execution_Time.Clock_For_Interrupts,
    Interrupt_Clocks_Supported is True.

  * for Ada.Execution_Time.Interrupts.Clock,
    Separate_Interrupt_Clocks_Supported is True.

  * for Ada.Execution_Time's arithmetic and conversion operators (including
    Time_Of), preconditions are defined to ensure that the result belongs to
    the result type.

  * for Ada.Real_Time's arithmetic and conversion operators (including Time_Of),
    preconditions are defined to ensure that the result belongs to the
    result type.

.. _tu-nt-tasks_and_synchronization-20:

20. All procedures declared in the visible part of Ada.Synchronous_Task_Control
    have a dependency "(S => null)" despite the fact that S has mode **in
    out**.

.. _etu-tasks_and_synchronization-vr:
