.. _getting started:

****************************
Getting Started with |SPARK|
****************************

We begin with a very simple guide aimed at getting new users up and running
with the |SPARK| tools. A small |SPARK| example program will be used for
illustration.

As a prerequisite, it is assumed that the |SPARK| tools have already been
installed. As a minimum you should install:

 - |GNATprove|
 - GPS.

Note that GPS is not strictly required for |SPARK| as all the commands can be
invoked from the command line, or from Eclipse using the GNATbench plug-in, but
the instructions in this section assume that GPS is being used. If you are a
supported user, you can get more information on how to install the tools in
"AdaCore Installation Procedures" under the "Download" tab in GNAT Tracker, or
by contacting AdaCore for further advice.

The key tools that we will use in this example are |GNATprove| and GPS.
To begin with, launch GPS with a new default project and check that the
:menuselection:`SPARK` menu is present in the menu bar.

.. note::

   For SPARK 2005 users, this menu will appear under the name
   :menuselection:`SPARK 2014`, to avoid any confusion with the existing
   :menuselection:`SPARK` menu for SPARK 2005 toolset.

Now open a new file in GPS and type the following short program into it.
Save this file as ``main.adb``.

.. code-block:: ada

   pragma SPARK_Mode;

   procedure Main (X, Y : in Natural; Z : out Natural)
     with Depends => (Z => (X, Y))
   is
   begin
      Z := X - X;
   end Main;

The program is intended to calculate the difference between ``X`` and ``Y`` and
store the result in ``Z``.  This is reflected in the Depends aspect which
states that the output value of Z depends on the input values of X and Y, but,
as you may have noticed, there is a bug in the code. To analyze this program,
select :menuselection:`SPARK --> Examine File` from the menu in
GPS. |GNATprove| executes in flow analysis mode and reports:

.. code-block:: bash

   main.adb:3:20: warning: unused initial value of "Y"
   main.adb:3:20: warning: unused variable "Y"
   main.adb:4:8: warning: missing dependency "null => Y"
   main.adb:4:20: warning: incorrect dependency "Z => Y"

These warnings are informing us that there is a discrepancy between the program's
contract (which says that the value of ``Z`` is obtained from the values of ``X``
and ``Y``) and the executable code (in which the value of ``Z`` is derived only
from the value of ``X``, and ``Y`` is unused). In this case the contract is
correct and the code is wrong, so fix the code by changing the assignment
statement to ``Z := X - Y;`` and re-run the analysis. This time it should
report no warnings or errors.

Having established that the program is free from flow errors, now let's run the
tools in proof mode to check for run-time errors.  Select :menuselection:`SPARK
--> Prove File` from the menu in GPS, and click on ``Execute`` in the
resulting dialog box.  |GNATprove| now attempts to show, using formal
verification, that the program is free from run-time errors. But it finds a
problem and highlights the assignment statement in red, reporting:

.. code-block:: bash

   main.adb:7:11: warning: range check might fail

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
:ref:`spark tutorial`.
