.. _Package Contracts:

Package Contracts
=================

Subprograms are not the only entities to bear contracts in |SPARK|. Package
contracts are made up of various optional parts:

* The `state abstraction` specifies how global variables defined in the package
  are referred to abstractly where they are not visible. Aspect
  ``Abstract_State`` introduces abstract names and aspect ``Refined_State``
  specifies the mapping between these names and global variables.
* The `package initialization` introduced by aspect ``Initializes`` specifies
  which global data (global variables and abstract state) defined in the
  package is initialized at package startup.
* The `package initial condition` introduced by aspect ``Initial_Condition``
  specifies the properties holding after package startup.

Package startup (a.k.a. package `elaboration` in Ada RM) consists in the
evaluation of all declarations in the package specification and implementation,
in particular the evaluation of constant declarations and those variable
declarations which contain an initialization expression, as well as the
statements sometimes given at the end of a package body that are precisely
executed at package startup.

.. _State Abstraction:

State Abstraction
-----------------

[|SPARK|]

The state abstraction of a package specifies a mapping between abstract names
and concrete global variables defined in the package. State abstraction allows
to define :ref:`Subprogram Contracts` at an abstract level that does not depend
on a particular choice of implementation (see :ref:`State Abstraction and
Contracts`), which is better both for maintenance (no need to change contracts)
and scalability of analysis (contracts can be much smaller).

Basic State Abstraction
^^^^^^^^^^^^^^^^^^^^^^^

One abstract name may be mapped to more than one concrete variable, but no two
abstract names can be mapped to the same concrete variable. When state
abstraction is specified on a package, all non-visible global variables defined
in the private part of the package specification and in its implementation
should be mapped to abstract names. Thus, abstract names correspond to a
partitioning of the non-visible global variables defined in the package.

The simplest use of state abstraction is to define a single abstract name
(conventionally called ``State``) to denote all non-visible global variables
defined in the package. For example, consider package ``Account`` defining a
global variable ``Total`` in its implementation, which is abstracted as
``State``:

.. code-block:: ada

   package Account with
     Abstract_State => State
   is
      ...
   end Account;

   package body Account with
     Refined_State => (State => Total)
   is
      Total : Integer;
      ...
   end Account;

The aspect ``Refined_State`` maps each abstract name to a list of concrete
global variables defined in the package. The list can be simply ``null`` to
serve as placeholder for future definitions of global variables. Instead of
concrete global variables, one can also use abstract names for the state of
nested packages and private child packages, whose state is considered to be
also defined in the parent package.

If global variable ``Total`` is defined in the private part of ``Account``'s
package specification, then the declaration of ``Total`` must use the special
aspect ``Part_Of`` to declare its membership in abstract state ``State``:

.. code-block:: ada

   package Account with
     Abstract_State => State
   is
      ...
   private
     Total : Integer with Part_Of => State;
     ...
   end Account;

This ensures that ``Account``'s package specification can be checked by
|GNATprove| even if its implementation is not in |SPARK|, or not available for
analysis, or not yet developed.

A package with state abstraction must have a package body that states how
abstract states are refined in aspect ``Refined_State``, unless the package
body is not in |SPARK|. If there is no other reason for the package to have a
body, then one should use ``pragma Elaborate_Body`` in the package spec to make
it legal for the package to have a body on which to express state refinement.

In general, an abstract name corresponds to multiple global variables defined
in the package. For example, we can imagine adding global variables to log
values passed in argument to procedure ``Add_To_Total``, that are also mapped to
abstract name ``State``:

.. code-block:: ada

   package Account with
     Abstract_State => State
   is
      ...
   end Account;

   package body Account with
     Refined_State => (State => (Total, Log, Log_Size))
   is
      Total    : Integer;
      Log      : Integer_Array;
      Log_Size : Natural;
      ...
   end Account;

We can also imagine defining different abstract names for the total and the log:

.. code-block:: ada

   package Account with
     Abstract_State => (State, Internal_State)
   is
      ...
   end Account;

   package body Account with
     Refined_State => (State => Total,
                       Internal_State => (Log, Log_Size))
   is
      Total    : Integer;
      Log      : Integer_Array;
      Log_Size : Natural;
      ...
   end Account;

The abstract names defined in a package are visible everywhere the package name
itself is visible:

* in the scope where the package is declared, for a locally defined package
* in units that have a clause ``with <package>;``
* in units that have a clause ``limited with <package>;``

The last case allows subprograms in two packages to mutually reference the
abstract state of the other package in their data and flow dependencies.

Special Cases of State Abstraction
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Global constants with a statically known value are not part of a package's
state. On the contrary, `constant with variable inputs` are constants whose
value depends on the value of either a variable or a subprogram
parameter. Since they participate in the flow of information between variables,
constants with variable inputs are treated like variables: they are part of a
package's state, and they must be listed in its state refinement whenever they
are not visible. For example, constant ``Total_Min`` is not part of the state
refinement of package ``Account`` below, while constant with variable inputs
``Total_Max`` is part of it:

.. code-block:: ada

   package body Account with
     Refined_State => (State => (Total, Total_Max))
   is
      Total     : Integer;
      Total_Min : constant Integer := 0;
      Total_Max : constant Integer := Compute_Total_Max(...);
      ...
   end Account;

Global variables are not always the only constituents of a package's state. For
example, if a package P contains a nested package N, then N's state is part of
P's state. As a consequence, if N is hidden, then its state must be listed in
P's refinement. For example, we can nest ``Account`` in the body of the
``Account_Manager`` package as follows:

.. code-block:: ada

   package Account_Manager with
     Abstract_State => State
   is
      ...
   end Account_Manager;

   package body Account_Manager with
     Refined_State => (State => Account.State)
   is
      package Account with
        Abstract_State => State
      is
         ...
      end Account;
      ...
   end Account_Manager;

State In The Private Part
^^^^^^^^^^^^^^^^^^^^^^^^^

Global variables and nested packages which themselves contain state may be
declared in the private part of a package. For each such global variable and
nested package state, it is mandatory to identify, using aspect ``Part_Of``,
the abstract state of the enclosing package of which it is a constituent:

.. code-block:: ada

   package Account_Manager with
     Abstract_State => (Totals, Details)
   is
      ...
   private
      Total_Accounts : Integer with Part_Of => Totals;

      package Account with
        Abstract_State => (State with Part_Of => Details)
      is
         Total : Integer with Part_Of => Totals;
         ...
      end Account;
      ...
   end Account_Manager;

The purpose of using ``Part_Of`` is to enforce that each constituent of an
abstract state is known at the declaration of the constituent (not having to
look at the package body), which is useful for both code understanding and tool
analysis (including compilation).

As the state of a private child package is logically part of its parent
package, aspect ``Part_Of`` must also be specified in that case:

.. code-block:: ada

   private package Account_Manager.Account with
     Abstract_State => (State with Part_Of => Details)
   is
      Total : Integer with Part_Of => Totals;
      ...
   end Account_Manager.Account;

Aspect ``Part_Of`` can also be specified on a generic package instantiation
inside a private part, to specify that all the state (visible global variables
and abstract states) of the package instantiation is a constituent of an
abstract state of the enclosing package:

.. code-block:: ada

   package Account_Manager with
     Abstract_State => (Totals, Details)
   is
      ...
   private
      package Account is new Generic_Account (Max_Total) with Part_Of => Details;
      ...
   end Account_Manager;

.. _Package Initialization:

Package Initialization
----------------------

[|SPARK|]

The package initialization specifies which global data (global variables,
constant with variable inputs, and
abstract state) defined in the package is initialized at package startup. The
corresponding global variables may either be initialized at declaration, or by
the package body statements. Thus, package initialization can be seen as the
output data dependencies of the package elaboration procedure generated by the
compiler.

For example, we can specify that the state of package ``Account`` is
initialized at package startup as follows:

.. code-block:: ada

   package Account with
     Abstract_State => State,
     Initializes    => State
   is
      ...
   end Account;

Then, unless ``Account``'s implementation is not in |SPARK|, it should
initialize the corresponding global variable ``Total`` either at declaration:

.. code-block:: ada

   package body Account with
     Refined_State => (State => Total)
   is
      Total : Integer := 0;
      ...
   end Account;

or in the package body statements:

.. code-block:: ada

   package body Account with
     Refined_State => (State => Total)
   is
      Total : Integer;
      ...
   begin
      Total := 0;
   end Account;

These initializations need not correspond to direct assignments, but may be
performed in a call, for example here to procedure ``Init_Total`` as seen in
:ref:`State Abstraction and Dependencies`. A mix of initializations at
declaration and in package body statements is also possible.

Package initializations also serve as dependency contracts for global
variables' initial values. That is, if the initial value of a global variable,
state abstraction, or constant with variable inputs listed in a package
initialization depends on the value of a variable defined outside the
package, then this dependency must be listed in the package's initialization.
For example, we can initialize ``Total`` by reading the value of an external
variable:

.. code-block:: ada

   package Account with
     Abstract_State => State,
     Initializes    => (State => External_Variable)
   is
      ...
   end Account;

   package body Account with
     Refined_State => (State => Total)
   is
      Total : Integer := External_Variable;
      ...
   end Account;

.. _Package Initial Condition:

Package Initial Condition
-------------------------

[|SPARK|]

The package initial condition specifies the properties holding after package
startup.  Thus, package initial condition can be seen as the postcondition of
the package elaboration procedure generated by the compiler.  For example, we
can specify that the value of ``Total`` defined in package ``Account``'s
implementation is initially zero:

.. code-block:: ada

   package Account with
     Abstract_State    => State,
     Initial_Condition => Get_Total = 0
   is
      function Get_Total return Integer;
      ...
   end Account;

This is ensured either by initializing ``Total`` with value zero at
declaration, or by assigning the value zero to ``Total`` in the package body
statements, as seen in :ref:`Package Initialization`.

When the program is compiled with assertions (for example with switch
``-gnata`` in |GNAT Pro|), the initial condition of a package is checked at run
time after package startup. An exception is raised if the initial condition
fails.

When a package is analyzed with |GNATprove|, it checks that the initial
condition of a package cannot fail. |GNATprove| also analyzes the initial
condition expression to ensure that it is free from run-time errors, like any
other assertion.

.. _Interfaces to the Physical World:

Interfaces to the Physical World
--------------------------------

[|SPARK|]

Volatile Variables
^^^^^^^^^^^^^^^^^^

Most embedded programs interact with the physical world or other programs
through so-called `volatile` variables, which are identified as volatile to
protect them from the usual compiler optimizations. In |SPARK|, volatile
variables are also analyzed specially, so that possible changes to their value
from outside the program are taken into account, and so that changes to their
value from inside the program are also interpreted correctly (in particular for
checking flow dependencies).

For example, consider package ``Volatile_Or_Not`` which defines a volatile
variable ``V`` and a non-volatile variable ``N``, and procedure
``Swap_Then_Zero`` which starts by swapping the values of ``V`` and ``N``
before zeroing them out:

.. literalinclude:: /gnatprove_by_example/examples/volatile_or_not.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/volatile_or_not.adb
   :language: ada
   :linenos:

Compare the difference in contracts between volatile variable ``V`` and
non-volatile variable ``N``:

* The :ref:`Package Initialization` of package ``Volatile_Or_Not`` mentions
  ``V`` although this variable is not initialized at declaration or in the
  package body statements. This is because a volatile variable is assumed to be
  initialized.

* The :ref:`Flow Dependencies` of procedure ``Swap_Then_Zero`` are very
  different for ``V`` and ``N``. If both variables were not volatile, the
  correct contract would state that both input values are not used with ``null
  => (V, N)`` and that both output values depend on no inputs with ``(V, N) =>
  null``. The difference lies with the special treatment of volatile variable
  ``V``: as its value may be read at any time, the intermediate value ``N``
  assigned to ``V`` on line 8 of ``volatile_or_not.adb`` needs to be mentioned
  in the flow dependencies for output ``V``.

|GNATprove| checks that ``Volatile_Or_Not`` and ``Swap_Then_Zero`` implement
their contract, and it issues a warning on the first assignment to ``N``:

.. literalinclude:: /gnatprove_by_example/results/volatile_or_not.flow
   :language: none

This warning points to a real issue, as the intermediate value of ``N`` is not
used before ``N`` is zeroed out on line 12. But note that no warning is issued
on the similar first assignment to ``V``, because the intermediate value of
``V`` may be read outside the program before ``V`` is zeroed out on line 11.

Note that in real code, the memory address of the volatile variable is set
through aspect ``Address`` or the corresponding representation clause, so that
it can be read or written outside the program.

.. _Properties of Volatile Variables:

Properties of Volatile Variables
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Not all volatile variables are read and written outside the program, sometimes
they are only read or only written outside the program. For example, the log
introduced in :ref:`State Abstraction` could be implemented as an output port
for the program logging the information, and as an input port for the program
performing the logging. Two aspects are defined in |SPARK| to distinguish these
different properties of volatile variables:

* Aspect ``Async_Writers`` indicates that the value of the variable may be
  changed at any time (asynchronously) by hardware or software outside the
  program.

* Aspect ``Async_Readers`` indicates that the value of the variable may be read
  at any time (asynchronously) by hardware or software outside the program.

Aspect ``Async_Writers`` has an effect on |GNATprove|'s proof: two successive
reads of such a variable may return different results. Aspect ``Async_Readers``
has an effect on |GNATprove|'s flow analysis: an assignment to such a variable
always has a potential effect, even if the value is never read in the program,
since an external reader might actually read the value assigned.

These aspects are well suited to model respectively a sensor and a display, but
not an input stream or an actuator, for which the act of reading or writing has
an effect that should be reflected in the flow dependencies. Two more aspects
are defined in |SPARK| to further refine the previous properties of volatile
variables:

* Aspect ``Effective_Reads`` indicates that reading the value of the variable
  has an effect (for example, removing a value from an input stream). It can
  only be specified on a variable that also has ``Async_Writers`` set.

* Aspect ``Effective_Writes`` indicates that writing the value of the variable
  has an effect (for example, sending a command to an actuator). It can only be
  specified on a variable that also has ``Async_Readers`` set.

Both aspects ``Effective_Reads`` and ``Effective_Writes`` have an effect on
|GNATprove|'s flow analysis: reading the former or writing the latter is
modelled as having an effect on the value of the variable, which needs to be
reflected in flow dependencies. Because reading a variable with
``Effective_Reads`` set has an effect on its value, such a variable cannot be
only a subprogram input, it must be also an output.

For example, the program writing in a log each value passed as argument to
procedure ``Add_To_Total`` may model the output port ``Log_Out`` as a volatile
variable with ``Async_Readers`` and ``Effective_Writes`` set:

.. literalinclude:: /gnatprove_by_example/examples/logging_out.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/logging_out.adb
   :language: ada
   :linenos:

while the logging program may model the input port ``Log_In`` as a volatile
variable with ``Async_Writers`` and ``Effective_Reads`` set:

.. literalinclude:: /gnatprove_by_example/examples/logging_in.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/logging_in.adb
   :language: ada
   :linenos:

|GNATprove| checks the specified data and flow dependencies on both programs.

A volatile variable on which none of the four aspects ``Async_Writers``,
``Async_Readers``, ``Effective_Reads`` or ``Effective_Writes`` is set is
assumed to have all four aspects set to ``True``. A volatile variable on which
some of the four aspects are set to ``True`` is assumed to have the remaining
ones set to ``False``. See SPARK RM 7.1.3 for details.

.. _External State Abstraction:

External State Abstraction
^^^^^^^^^^^^^^^^^^^^^^^^^^

Volatile variables may be part of :ref:`State Abstraction`, in which case the
volatility of the abstract name must be specified by using aspect ``External``
on the abstract name, as follows:

.. code-block:: ada

   package Account with
     Abstract_State => (State with External)
   is
      ...
   end Account;

An external state may represent both volatile variables and non-volatile ones,
for example:

.. code-block:: ada

   package body Account with
     Refined_State => (State => (Total, Log, Log_Size))
   is
      Total    : Integer;
      Log      : Integer_Array with Volatile;
      Log_Size : Natural with Volatile;
      ...
   end Account;

The different :ref:`Properties of Volatile Variables` may also be specified in the
state abstraction, which is then used by |GNATprove| to refine the
analysis. For example, the program writing in a log seen in the previous
section can be rewritten to abstract global variables as follows:

.. literalinclude:: /gnatprove_by_example/examples/logging_out_abstract.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/logging_out_abstract.adb
   :language: ada
   :linenos:

while the logging program seen in the previous section may be rewritten to
abstract global variables as follows:

.. literalinclude:: /gnatprove_by_example/examples/logging_in_abstract.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/logging_in_abstract.adb
   :language: ada
   :linenos:

|GNATprove| checks the specified data and flow dependencies on both programs.

An external abstract state on which none of the four aspects ``Async_Writers``,
``Async_Readers``, ``Effective_Reads`` or ``Effective_Writes`` is set is
assumed to have all four aspects set to ``True``. An external abstract state on
which some of the four aspects are set to ``True`` is assumed to have the
remaining ones set to ``False``. See SPARK RM 7.1.2 for details.
