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
 
.. centered:: **Static Semantics**

1.  An object is said to be *synchronized* if it is

  * a task or protected object; or

  * an object of type Ada.Synchronous_Task_Control.Suspension_Object
    (hereafter called a "suspension object"); or

  * an atomic object; or

  * a variable which is "constant after elaboration" (see TBD); or

  * a constant object.

  [Synchronized objects may be referenced by multiple tasks without causing
  erroneous execution.]

.. centered:: **Legality Rules**

.. _tu-tasks_and_synchronization-01:

1. Task and protected units are in |SPARK|, but their use requires
   the Ravenscar Profile. [In other words, a task or protected unit
   is not in |SPARK| if the Ravenscar profile does not apply to the
   enclosing compilation unit.] Similarly, the use of task or protected units
   also requires a Partition_Elaboration_Policy of Sequential. [This
   is to prevent premature access by tasks to "constant after elaboration"
   variables.]

2. A ''global_item'' occurring in a Global aspect specification of a
   task unit or of a protected operation shall not denote an object
   or state abstraction which is not synchronized unless the
   Part_Of aspect of the object denotes the task or protected unit.

3. A ``global_item`` occurring in the Global aspect specification of
   the main subprogram shall not denote an object or state abstraction
   whose Part_Of aspect denotes a task or protected unit. [In other words,
   the environment task cannot reference objects which "belong" to other
   tasks.]
   
4. A ``global_item`` occurring in the Global aspect specification of the
   main subprogram or of a task unit having a mode of Output or In_Out shall
   not denote a  variable whose Constant_After_Elaboration aspect is True.

5. If a variable declaration is declared within the same declarative
   region as a ``single_task_declaration`` or a
   ``single_protected_declaration``, then the Part_Of aspect of the variable
   may denote the protected or task object. This indicates
   that the object or state abstraction is not part of the visible state
   or private state of its enclosing package. [Loosely speaking, flow
   analysis will treat the object as though it were declared within
   its "owner". This can be useful if, for example, a protected object's
   operations need to reference an object whose Address aspect is specified.
   The protected (as opposed to task) case corresponds to RavenSpark's
   "virtual protected" objects.]

.. centered:: **Verification Rules**

6. Only a single task (including the environment task)
   shall suspend (directly or via intermediate calls)
   on a given suspension object.

7. The end of a task body shall not be reachable. [This follows from
   from Ravenscar's No_Task_Termination restriction.]

8. Flow analysis is responsible for discharging the proof obligation
   associated with the Ada rule that it is a bounded error to invoke
   an operation that is potentially blocking during a protected action.
   [TBD: support for the "Nonblocking" aspect discussed in AI12-0064,
   presumably including rule for overriding for dispatching calls].

.. _etu-tasks_and_synchronization:

