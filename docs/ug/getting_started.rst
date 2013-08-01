.. _getting started:

****************************
Getting Started with |SPARK|
****************************

We begin with a very simple guide aimed at getting new users up and running
with the |SPARK| tools. A small |SPARK| example program will be used for
illustration.

As a prerequisite, it is assumed that the |SPARK| tools have already been
installed. For more information on how to do this see the "AdaCore
Installation Procedures" under GNAT Tracker.

The key tools that we will use in this example are |GNATprove| and GPS.
To begin with, launch GPS with a new default project and check that the
"Prove" menu is present in the menu bar.

Before writing and verifying any code, there is one switch that needs to
be set in GPS. Under ``Project > Edit Project Properties > Switches > GNATprove``
add the string ``--mode=flow`` to the box at the bottom of the window
(which shows the switches to be used, and should be empty beforehand).
This switch tells |GNATprove| to operate in flow analysis mode, which
we will use to begin with. [Note that for Release 1 it is expected that
the default mode will be to peform both flow analysis and proof, so this
flag will not need to be set for this example. Note also that the switch
``-gnatd.V`` is currently needed under the ``Ada`` tab but this should also
become unnecessary in Release 1.]

Now open a new file in GPS and type the following short program into it.
Save this file as ``main.adb``.

.. code-block:: ada

   procedure Main (X, Y : in Natural; Z : out Natural)
     with Depends => (Z => (X, Y))
   is
   begin
      Z := X - X;
   end Main;

The program is intended to calculate the difference between ``X`` and ``Y``
and store the result in ``Z``.
This is reflected in the Depends aspect which states that the output value
of Z depends on the input values of X and Y, but as you may have noticed 
there is a bug in the code. To analyse this program select ``Prove > Prove File``
from the menu in GPS and click on ``Execute`` in the resulting dialog box.
|GNATprove| executes in flow analysis mode and reports:

.. code-block:: bash

   1:20 warning: unused initial value of "Y"
   1:20 warning: unused variable "Y"
   2:8  warning: missing dependency "null => Y"
   2:20 warning: incorrect dependency "Z => Y"

These warnings are informing us that there is a discrepany between the program's
contract (which says that the value of ``Z`` is obtained from the values of ``X``
and ``Y``) and the executable code (in which the value of ``Z`` is derived only
from the value of ``X``, and ``Y`` is unused). In this case the contract is
correct and the code is wrong, so fix the code by changing the assignment
statement to ``Z := X - Y;`` and re-run the analysis. This time it should
report no warnings or errors.

Having established that the program is free from flow errors, now let's run the
tools in proof mode to check for run-time errors. Under
``Project > Edit Project Properties > Switches > GNATprove`` remove the string
``--mode=flow`` that was added earlier, save this change and re-run the analysis.
|GNATprove| now attempts to show, using formal verification, that the program
is free from run-time errors. But it finds a problem and highlights the
assignment statement in red, reporting:

.. code-block:: bash

   5:11 range check not proved

This means that the tools are unable to show that the result of subtracting one
``Natural`` number from another will be within the range of the type ``Natural``,
which is hopefully not too surprising! There are various ways in which this could be
addressed depending on what the requirements are for this subprogram, but for
now let's change the type of parameter ``Z`` from ``Natural`` to ``Integer``.
If the analysis is re-run with this change in place then |GNATprove| will
report no errors or warnings. All checks are proved so we can be confident that
no exceptions will be raised by the execution of this code.

This short example was intended to give a flavour of the types of analysis that can
be performed with the |SPARK| tools. A more in-depth example is presented later in
:ref:`writing and verifying spark programs`.
