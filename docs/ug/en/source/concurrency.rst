.. index:: Ravenscar, concurrency

Concurrency and Ravenscar Profile
=================================

Concurrency in |SPARK| requires enabling the Ravenscar profile (see `Guide for
the use of the Ada Ravenscar Profile in high integrity systems` by Alan Burns,
Brian Dobbing, and Tullio Vardanega). This profile defines a subset of the Ada
concurrency features suitable for hard real-time/embedded systems requiring
stringent analysis, such as certification and safety analyses. In particular,
it is concerned with determinism, analyzability, and memory-boundedness.

In addition to the subset defined by the Ravenscar profile, concurrency in |SPARK|
also requires that tasks do not start executing before
the program has been completely elaborated, which is expressed by setting
pragma ``Partition_Elaboration_Policy`` to the value ``Sequential``. Together
with the requirement to apply the Ravenscar profile, this means that a concurrent
|SPARK| program should define the following configuration pragmas, either in a
configuration pragma file (see :ref:`Setting the Default SPARK_Mode` for an
example of defining a configuration pragma file in your project file) or at the
start of files:

.. code-block:: ada

   pragma Profile (Ravenscar);
   pragma Partition_Elaboration_Policy (Sequential);

GNATprove also supports the Jorvik profile, as defined in Ada 202X RM, D.13. To
use this profile simply replace ``Ravenscar`` with ``Jorvik`` in the pragma
``Profile`` in the above code. The extended profile is intended for hard
real-time/embedded systems that may require schedulability analysis but not the
most stringent analyses required for other domains.

In particular, to increase expressive power the Jorvik profile relaxes certain
restrictions defined by the standard Ravenscar profile. Notably, these relaxed
constraints allow multiple protected entries per protected object, multiple
queued callers per entry, and more expressive protected entry barrier
expressions. The profile also allows the use of relative delay statements in
addition to the absolute delay statements allowed by Ravenscar. The two forms
of delay statement are processed by GNATprove based on the type of their
expression, as follows (absolute and relative delays, respectively):

* If the expression is of the type Ada.Real_Time.Time then for the purposes of
  determining global inputs and outputs the absolute delay statement is considered
  just like the relative delay statement, i.e., to reference the state abstraction
  Ada.Real_Time.Clock_Time as an input (see SPARK RM 9(17) for details).

* If the expression is of the type Ada.Calendar.Time then it is considered to
  reference the state abstraction Ada.Calendar.Clock_Time, which is defined
  similarly to Ada.Real_Time.Clock_Time but represents a different time base.

.. index:: tasking, data race

Tasks and Data Races
--------------------

[Ravenscar/Jorvik]

Concurrent Ada programs are made of several `tasks`, that is, separate threads
of control which share the same address space. In Ravenscar, only
library-level, nonterminating tasks are allowed.

Task Types and Task Objects
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Like ordinary objects, tasks have a type in Ada and can be stored in composite
objects such as arrays and records. The definition of a task type looks like
the definition of a subprogram. It is made of two parts: a declaration, usually
empty as Ravenscar does not allow tasks to have entries (for task rendezvous),
and a body containing the list of statements to be executed by objects of the
task type. The body of nonterminating tasks (the only ones allowed in
Ravenscar) usually takes the form of an infinite loop. For task objects of a
given type to be parameterized, task types can have discriminants. As an
example, a task type ``Account_Management`` can be declared as follows:

.. code-block:: ada

   package Account is
      Num_Accounts : Natural := 0;

      task type Account_Management;
   end Account;

   package body Account is

      task body Account_Management is
      begin
         loop
            Get_Next_Account_Created;
            Num_Accounts := Num_Accounts + 1;
         end loop;
      end Account_Management;

   end Account;

Then, tasks of type ``Account_Management`` can be created at library level,
either as complete objects or as components of other objects:

.. code-block:: ada

   package Bank is
      Special_Accounts : Account_Management;

      type Account_Type is (Regular, Premium, Selective);
      type Account_Array is array (Account_Type) of Account_Management;
      All_Accounts : Account_Array;
   end Bank;

If only one object of a given task type is needed, then the task object can be
declared directly giving a declaration and a body. An anonymous task type is
then defined implicitly for the declared type object. For example, if we only
need one task ``Account_Management`` then we can write:

.. code-block:: ada

   package Account is
      Num_Accounts : Natural := 0;

      task Account_Management;
   end Account;

   package body Account is

      task body Account_Management is
      begin
         loop
            Get_Next_Account_Created;
            Num_Accounts := Num_Accounts + 1;
         end loop;
      end Account_Management;

   end Account;

.. index:: protected object; and data races
           Suspension_Object; and data races
           Constant_After_Elaboration; and data races

Preventing Data Races
^^^^^^^^^^^^^^^^^^^^^

In Ravenscar, communication between tasks can only be done through shared
objects (tasks cannot communicate through rendezvous as task entries are not
allowed in Ravenscar). In |SPARK|, the language is further restricted to avoid
the possibility of erroneous concurrent access to shared data (a.k.a. data
races). More precisely, tasks can only share `synchronized` objects, that is,
objects that are protected against concurrent accesses. These include atomic
objects, protected objects (see :ref:`Protected Objects and Deadlocks`), and
suspension objects (see :ref:`Suspension Objects`). As an example, our previous
definition of the ``Account_Management`` task type was not in |SPARK|. Indeed,
data races could occur when accessing the global variable ``Num_Accounts``, as
detected by |GNATprove|:

.. literalinclude:: /examples/tests/bank1/test.out
   :language: none

To avoid this problem, shared variable ``Num_Account`` can be declared atomic:

.. code-block:: ada

   package Account is
      Num_Accounts : Natural := 0 with Atomic;

      task type Account_Management;
   end Account;

With this modification, |GNATprove| now alerts us that the increment of
``Num_Account`` is not legal, as a volatile variable (which is the case of
atomic variables) cannot be read as a subexpression of a larger expression in
|SPARK|:

.. literalinclude:: /examples/tests/account2/test.out
   :language: none

This can be fixed by copying the current value of ``Num_Account`` in a
temporary before the increment:

.. code-block:: ada

         declare
            Tmp : constant Natural := Num_Accounts;
         begin
            Num_Accounts := Tmp + 1;
         end;

But note that even with that fix, there is no guarantee that ``Num_Accounts`` is
incremented by one each time an account is created. Indeed, two tasks may read
the same value of ``Num_Accounts`` and store this value in ``Tmp`` before both
updating it to ``Tmp + 1``. In such a case, two accounts have been created but
``Num_Accounts`` has been increased by 1 only. There is no `data race` in this
program, which is confirmed by running |GNATprove| with no error, but there is
by design a `race condition` on shared data that causes the program to
malfunction. The correct way to fix this in |SPARK| is to use :ref:`Protected
Types and Protected Objects`.

As they cannot cause data races, constants and variables that are constant after
elaboration (see :ref:`Aspect Constant_After_Elaboration`) are considered as
synchronized and can be accessed by multiple tasks. For example, we can declare
a global constant ``Max_Accounts`` and use it inside ``Account_Management``
without risking data races:

.. code-block:: ada

   package Account is
      Num_Accounts : Natural := 0 with Atomic;
      Max_Accounts : constant Natural := 100;

      task type Account_Management;
   end Account;

   package body Account is

      task body Account_Management is
      begin
         loop
            Get_Next_Account_Created;
            declare
               Tmp : constant Natural := Num_Accounts;
            begin
               if Tmp < Max_Accounts then
                  Num_Accounts := Tmp + 1;
               end if;
            end;
         end loop;
      end Account_Management;

   end Account;

.. index:: Part_Of; for concurrency

It is possible for a task to access an unsynchronized global variable only if
this variable is declared in the same package as the task and if there is a
single task accessing this variable. To allow this property to be statically
verified, only tasks of an anonymous task type are allowed to access
unsynchronized variables and the variables accessed should be declared to
belong to the task using aspect ``Part_Of``. Global variables declared to
belong to a task are handled just like local variables of the task, that is,
they can only be referenced from inside the task body.  As an example, we can
state that ``Num_Accounts`` is only accessed by the task object
``Account_Management`` in the following way:

.. code-block:: ada

   package Account is
      task Account_Management;

      Num_Accounts : Natural := 0 with Part_Of => Account_Management;
   end Account;

Task Contracts
--------------

[SPARK]

Dependency contracts can be specified on tasks. As tasks should not terminate
in |SPARK|, such contracts specify the dependencies between outputs and inputs
of the task `updated while the task runs`:

* The `data dependencies` introduced by aspect ``Global`` specify the global
  data read and written by the task.
* The `flow dependencies` introduced by aspect ``Depends`` specify how
  task outputs depend on task inputs.

This is a difference between tasks and subprograms, for which such contracts
describe the dependencies between outputs and inputs `when the subprogram
returns`.

.. index:: Global; in task contract

Data Dependencies on Tasks
^^^^^^^^^^^^^^^^^^^^^^^^^^

Data dependencies on tasks follow the same syntax as the ones on subprograms
(see :ref:`Data Dependencies`). For example, data dependencies can be specified
for task (type or object) ``Account_Management`` as follows:

.. code-block:: ada

   package Account is
      Num_Accounts : Natural := 0 with Atomic;

      task type Account_Management with
        Global => (In_Out => Num_Accounts);
   end Account;

.. index:: Depends; in task contract

Flow Dependencies on Tasks
^^^^^^^^^^^^^^^^^^^^^^^^^^

Flow dependencies on tasks follow the same syntax as the ones on subprograms
(see :ref:`Flow Dependencies`). For example, flow dependencies can be specified
for task (type or object) ``Account_Management`` as follows:

.. code-block:: ada

   package Account is
      Num_Accounts : Natural := 0 with Atomic;

      task type Account_Management with
        Depends => (Account_Management => Account_Management,
                    Num_Accounts       => Num_Accounts);
   end Account;

Notice that the task unit itself is both an input and an output of the task:

* It is an input because task discriminants (if any) and task attributes may be
  read in the task body.

* It is an output so that the task unit may be passed as in out parameter in a
  subprogram call. But note that the task object cannot be modified once
  created.

The dependency of the task on itself can be left implicit as well, as follows:

.. code-block:: ada

   package Account is
      Num_Accounts : Natural := 0 with Atomic;

      task type Account_Management with
        Depends => (Num_Accounts => Num_Accounts);
   end Account;

.. index:: protected object; and deadlock

Protected Objects and Deadlocks
-------------------------------

[Ravenscar/Jorvik]

In Ada, protected objects are used to encapsulate shared data and protect it
against data races (low-level unprotected concurrent access to data) and race
conditions (lack of proper synchronization between reads and writes of shared
data). They coordinate access to the protected data guaranteeing that
read-write accesses are always exclusive while allowing concurrent read-only
accesses. In Ravenscar, only library-level protected objects are allowed.

Protected Types and Protected Objects
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Definitions of protected types resemble package definitions. They are made of
two parts, a declaration (divided into a public part and a private part) and a
body. The public part of a protected type's declaration contains the
declarations of the subprograms that can be used to access the data declared in
its private part. The body of these subprograms are located in the protected
type's body. In Ravenscar, protected objects should be declared at library
level, either as complete objects or as components of other objects. As an
example, here is how a protected type can be used to coordinate concurrent
accesses to the global variable ``Num_Accounts``:

.. code-block:: ada

   package Account is

      protected type Protected_Natural is
         procedure Incr;
         function Get return Natural;
      private
         The_Data : Natural := 0;
      end Protected_Natural;

      Num_Accounts : Protected_Natural;
      Max_Accounts : constant Natural := 100;

      task type Account_Management;
   end Account;

   package body Account is

      protected body Protected_Natural is
         procedure Incr is
         begin
            The_Data := The_Data + 1;
         end Incr;

         function Get return Natural is (The_Data);
      end Protected_Natural;

      task body Account_Management is
      begin
         loop
            Get_Next_Account_Created;
            if Num_Accounts.Get < Max_Accounts then
               Num_Accounts.Incr;
            end if;
         end loop;
      end Account_Management;

   end Account;

Contrary to the previous version using an atomic global variable (see
:ref:`Preventing Data Races`), this version prevents also any race condition
when incrementing the value of ``Num_Accounts``. But note that there is still a
possible race condition between the time the value of ``Num_Accounts`` is read
and checked to be less than ``Max_Accounts`` and the time it is incremented. So
this version does not guarantee that ``Num_Accounts`` stays below
``Max_Accounts``. The correct way to fix this in |SPARK| is to use protected
entries (see :ref:`Protected Subprograms`).

Note that, in |SPARK|, to avoid initialization issues on protected objects,
both private variables and variables belonging to a protected object must be
initialized at declaration (either explicitly or through default
initialization).

Just like for tasks, it is possible to directly declare a protected object if
it is the only one of its type. In this case, an anonymous protected type is
implicitly declared for it. For example, if ``Num_Account`` is the only
``Protected_Natural`` we need, we can directly declare:

.. code-block:: ada

   package Account is

      protected Num_Accounts is
         procedure Incr;
         function Get return Natural;
      private
         The_Data : Natural := 0;
      end Num_Accounts;

   end Account;

   package body Account is

      protected body Num_Accounts is
         procedure Incr is
         begin
            The_Data := The_Data + 1;
         end Incr;

         function Get return Natural is (The_Data);
      end Num_Accounts;

   end Account;

Protected Subprograms
^^^^^^^^^^^^^^^^^^^^^

The access mode granted by protected subprograms depends on their kind:

* Protected procedures provide exclusive read-write access to the private data
  of a protected object.

* Protected functions offer concurrent read-only access to the private data of
  a protected object.

* Protected `entries` are conceptually procedures with a `barrier`. When an
  entry is called, the caller waits until the condition of the barrier is true
  to be able to access the protected object.

So that scheduling is deterministic, Ravenscar requires that at most one entry
is specified in a protected unit and at most one task is waiting on a given
entry at every time. To ensure this, |GNATprove| checks that no two tasks can
call the same protected object's entry. As an example, we could replace the
procedure ``Incr`` of ``Protected_Natural`` to wait until ``The_Data`` is
smaller than ``Max_Accounts`` before incrementing it. As only simple Boolean
variables are allowed as entry barriers in Ravenscar, we add such a Boolean
flag ``Not_Full`` as a component of the protected object:

.. code-block:: ada

   package Account is

      protected type Protected_Natural is
         entry Incr;
         function Get return Natural;
      private
         The_Data : Natural := 0;
         Not_Full : Boolean := True;
      end Protected_Natural;

      Num_Accounts : Protected_Natural;
      Max_Accounts : constant Natural := 100;

      task type Account_Management;
   end Account;

   package body Account is

      protected body Protected_Natural is
         entry Incr when Not_Full is
         begin
            The_Data := The_Data + 1;
            if The_Data = Max_Accounts then
               Not_Full := False;
            end if;
         end Incr;

         function Get return Natural is (The_Data);
      end Protected_Natural;

      task body Account_Management is
      begin
         loop
            Get_Next_Account_Created;
            Num_Accounts.Incr;
         end loop;
      end Account_Management;

   end Account;

This version fixes the remaining race condition on this example, thus ensuring
that every new account created bumps the value of ``Num_Accounts`` by 1, and
that ``Num_Accounts`` stays below ``Max_Accounts``.

To avoid data races, protected subprograms should not access unsynchronized
objects (see :ref:`Tasks and Data Races`). Like for tasks, it is still possible
for subprograms of a protected object of an anonymous protected type to access
an unsynchronized object declared in the same package as long as it is not
accessed by any task or subprogram from other protected objects. In this case,
the unsynchronized object should have a ``Part_Of`` aspect referring to the
protected object. It is then handled as if it was a private variable of the
protected object. This is typically done so that the address in memory of the
variable can be specified, using either aspect ``Address`` or a corresponding
representation clause. Here is how this could be done with ``Num_Account``:

.. code-block:: ada

   package Account is
      protected Protected_Num_Accounts is
         procedure Incr;
         function Get return Natural;
      end Protected_Num_Accounts;

      Num_Accounts : Natural := 0 with
        Part_Of => Protected_Num_Accounts,
        Address => ...
   end Account;

As it can prevent access to a protected object for an unbounded amount of time,
a task should not be blocked or delayed while inside a protected subprogram.
Actions that can block a task are said to be `potentially blocking`. For
example, calling a protected entry, explicitly waiting using a ``delay_until``
statement (note that ``delay`` statements are forbidden in Ravenscar), or
suspending on a suspension object (see :ref:`Suspension Objects`) are
potentially blocking actions. In Ada, it is an error to do a potentially
blocking action while inside a protected subprogram. Note that a call to a
function or a procedure on another protected object is not considered to be
potentially blocking. Indeed, such a call cannot block a task in the absence of
deadlocks (which is enforced in Ravenscar using the priority ceiling protocol,
see :ref:`Avoiding Deadlocks and Priority Ceiling Protocol`).

|GNATprove| verifies that no potentially blocking action is performed from
inside a protected subprogram in a modular way on a per subprogram basis.
Thus, if a subprogram can perform a potentially blocking operation, every call
to this subprogram from inside a protected subprogram will be flagged as a
potential error.  As an example, the procedure Incr_Num_Accounts is potentially
blocking and thus should not be called, directly or indirectly, from a
protected subprogram:

.. code-block:: ada

   package Account is

      protected type Protected_Natural is
         entry Incr;
      private
         The_Data : Natural := 0;
      end Protected_Natural;

      Num_Accounts : Protected_Natural;

      procedure Incr_Num_Accounts;

   end Account;

   package body Account is

      procedure Incr_Num_Accounts is
      begin
         Num_Accounts.Incr;
      end Incr_Num_Accounts;

   end Account;

Avoiding Deadlocks and Priority Ceiling Protocol
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

To ensure exclusivity of read-write accesses, when a procedure or an entry of a
protected object is called, the protected object is locked so that no other
task can access it, be it in a read-write or a read-only mode. In the same way,
when a protected function is called, no other task can access the protected
object in read-write mode.  A `deadlock` happens when two or more tasks are
unable to run because each of them is trying to access a protected object that
is currently locked by another task.

To ensure absence of deadlocks on a single core, Ravenscar requires the use of
the Priority Ceiling Protocol. This protocol ensures that no task can be
blocked trying to access a protected object locked by another task.  It relies
on task's `priorities`. The priority of a task is a number encoding its
urgency. On a single core, scheduling ensures that the current running task can
only be preempted by another task if it has a higher priority.  Using this
property, the Priority Ceiling Protocol works by increasing the priorities of
tasks accessing a protected object to a priority that is at least as high as
the priorities of other tasks accessing this object. This ensures that,
while holding a lock, the currently running task cannot be preempted by a task
which could later be blocked by this lock.

To enforce this protocol, every task is associated with a `base priority`,
either given at declaration using the ``Priority`` aspect or defaulted. This
base priority is static and cannot be modified after the task's declaration. A
task also has an `active priority` which is initially the task's base priority
but will be increased when the task enters a protected action.  For example, we
can set the base priority of ``Account_Management`` to 5 at declaration:

.. code-block:: ada

   package Account is
      task type Account_Management with Priority => 5;
   end Account;

Likewise, each protected object is associated at declaration with a `ceiling
priority` which should be equal or higher than the active priority of any task
accessing it. The ceiling priority of a protected object does not need to be
static, it can be set using a discriminant for example. Still, like for tasks,
Ravenscar requires that it is set once and for all at the object's declaration
and cannot be changed afterwards.  As an example, let us attach a ceiling
priority to the protected object ``Num_Accounts``. As ``Num_Accounts`` will be
used by ``Account_Management``, its ceiling priority should be no lower than 5:

.. code-block:: ada

   package Account is

      protected Num_Accounts with Priority => 7 is
         procedure Incr;
         function Get return Natural;
      private
         The_Data : Natural := 0;
      end Num_Accounts;

      task type Account_Management with Priority => 5;

   end Account;

.. index:: Suspension_Object

Suspension Objects
------------------

[Ravenscar/Jorvik]

The language-defined package ``Ada.Synchronous_Task_Control`` provides a type
for semaphores called `suspension objects`. They allow lighter synchronization
mechanisms than protected objects (see :ref:`Protected Objects and Deadlocks`).
More precisely, a suspension object has a Boolean state which can be set
atomically to True using the ``Set_True`` procedure.  When a task suspends on a
suspension object calling the ``Suspend_Until_True`` procedure, it is blocked
until the state of the suspension object is True. At that point, the state of
the suspension object is set back to False and the task is unblocked. Note that
``Suspend_Until_True`` is potentially blocking and therefore should not be
called directly or indirectly from within :ref:`Protected Subprograms`.  In the
following example, the suspension object ``Semaphore`` is used to make sure
``T1`` has initialized the shared data by the time ``T2`` begins processing it:

.. code-block:: ada

   Semaphore : Suspension_Object;
   task T1;
   task T2;

   task body T1 is
   begin
     Initialize_Shared_Data;
     Set_True (Semaphore);
     loop
       ...
     end loop;
   end T1;

   task body T2 is
   begin
     Suspend_Until_True (Semaphore);
     loop
       ...
     end loop;
   end T2;

In Ada, an exception is raised if a task tries to suspend on a suspension
object on which another task is already waiting on that same suspension
object. Like for verifying that no two tasks can be queued on a protected
entry, this verification is done by |GNATprove| by checking that no two tasks
ever suspend on the same suspension object.  In the following example, the
suspension objects ``Semaphore1`` and ``Semaphore2`` are used to ensure that
``T1`` and ``T2`` never call ``Enter_Protected_Region`` at the same
time. |GNATprove| will successfully verify that only one task can suspend on
each suspension object:

.. code-block:: ada

   Semaphore1, Semaphore2 : Suspension_Object;
   task T1;
   task T2;

   task body T1 is
   begin
     loop
       Suspend_Until_True (Semaphore1);
       Enter_Protected_Region;
       Set_True (Semaphore2);
     end loop;
   end T1;

   task body T2 is
   begin
     loop
       Suspend_Until_True (Semaphore2);
       Enter_Protected_Region;
       Set_True (Semaphore1);
     end loop;
   end T2;

.. index:: state abstraction; and concurrency
           External; and concurrency
           Synchronous_State

State Abstraction and Concurrency
---------------------------------

[SPARK]

Protected objects, as well as suspension objects, are `effectively volatile`
which means that their value as seen from a given task may change at any time
due to some other task accessing the protected object or suspension object. If
they are part of a state abstraction, the volatility of the abstract state must
be specified by using the ``External`` aspect (see :ref:`External State
Abstraction`). Note that task objects, though they can be part of a package's
hidden state, are not effectively volatile and can therefore be components of
normal state abstractions. For example, the package
``Synchronous_Abstractions`` defines two abstract states, one for external
objects, containing the atomic variable ``V``, the suspension object ``S``, and
the protected object ``P``, and one for normal objects, containing the task
``T``:

.. code-block:: ada

   package Synchronous_Abstractions with
     Abstract_State => (Normal_State, (Synchronous_State with External))
   is
   end Synchronous_Abstractions;

   package body Synchronous_Abstractions with
     Refined_State => (Synchronous_State => (P,V,S), Normal_State => T)
   is
     task T;

     S : Suspension_Object;

     V : Natural := 0 with Atomic, Async_Readers, Async_Writers;

     protected P is
       function Read return Natural;
     private
       V : Natural := 0;
     end P;

     protected body P is
       function Read return Natural is (V);
     end P;

     task body T is ...
   end  Synchronous_Abstractions;

To avoid data races, task bodies, as well as protected subprograms, should only
access synchronized objects (see :ref:`Preventing Data Races`). State
abstractions containing only synchronized objects can be specified to be
synchronized using the ``Synchronous`` aspect. Only synchronized state
abstractions can be accessed from task bodies and protected subprograms. For
example, if we want the procedure ``Do_Something`` to be callable from the task
``Use_Synchronized_State``, then the state abstraction ``Synchronous_State``
must be annotated using the ``Synchronous`` aspect:

.. code-block:: ada

   package Synchronous_Abstractions with
     Abstract_State => (Normal_State,
                        (Synchronous_State with Synchronous, External))
   is
     procedure Do_Something with Global => (In_Out => Synchronous_State);
   end Synchronous_Abstractions;

   task body Use_Synchronized_State is
   begin
     loop
       Synchronous_Abstractions.Do_Something;
     end loop;
   end Use_Synchronized_State;

Project-wide Tasking Analysis
-----------------------------

Tasking-related analysis, as currently implemented in |GNATprove|, is subject to
two limitations:

First, the analysis is always done when processing a source file with task
objects or with a subprogram that can be used as a main subprogram of a
partition (i.e. is at library level, has no parameters, and is either a
procedure or a function returning an integer type).

In effect, you might get spurious checks when:

* a subprogram satisfies conditions for being used as a main subprogram of a
  partition but is not really used that way, i.e. it is not specified in the
  Main attribute of the GNAT project file you use to build executables, and
* it "withs" or is "withed" (directly or indirectly) from a library-level
  package that declares some task object, and
* both the fake "main" subprogram and the task object access the same resource in a
  way that violates tasking-related rules (e.g. suspends on the same suspension
  object).

As a workaround, either wrap the fake "main" subprogram in a library-level package
or give it a dummy parameter.

Second, the analysis is only done in the context of all the units "withed"
(directly and indirectly) by the currently analyzed source file.

In effect, you might miss checks when:

* building a library that declares tasks objects in unrelated source files,
  i.e. files that are never "withed" (directly or indirectly) from the same
  file, and those tasks objects access the same resource in a way that violates
  tasking-related rules, or
* using a library that internally declares some tasks objects, they access some
  tasking-sensitive resource, and your main subprogram also accesses this
  resource.

As a workaround, when building library projects add a dummy main subprogram
that "withs" all the library-level packages of your project.

.. index:: Attach_Handler
           interrupt handler

Interrupt Handlers
------------------

SPARK puts no restrictions on the Ada interrupt handling and GNATprove merely
checks that interrupt handlers will be safely executed. In Ada interrupts
handlers are defined by annotating protected procedures, for example:

.. code-block:: ada

   with Ada.Interrupts.Names; use Ada.Interrupts.Names;

   protected P is
      procedure Signal with Attach_Handler => SIGINT;
   end P;

Currently GNATprove emits a check for each handler declaration saying that the
corresponding interrupt might be already reserved. In particular, it might be
reserved by either the system or the Ada runtime; see GNAT pragmas
Interrupt_State and Unreserve_All_Interrupts for details. Once examined, those
checks can be suppressed with pragma Annotate.

If pragma Priority or Interrupt_Priority is explicitly specified for a
protected type, then GNATprove will check that its value is in the range of the
System.Any_Priority or System.Interrupt_Priority, respectively; see Ada RM
D.3(6.1/3).

For interrupt handlers whose bodies are annotated with SPARK_Mode => On,
GNATprove will additionally check that:

* the interrupt handler does not call (directly or indirectly) the
  Ada.Task_Identification.Current_Task routine, which might cause a
  Program_Error runtime exception; see Ada RM C.7.1(17/3);

* all global objects read (either as an Input or a Proof_In) by the interrupt
  handler are initialized at elaboration;

* there are no unsynchronized objects accessed both by the interrupt handler
  and by some task (or by some other interrupt handler);

* there are no protected objects locked both by the interrupt handler and by
  some task (or by some other interrupt handler).
