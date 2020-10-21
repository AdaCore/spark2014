.. _getting started:

****************************
Getting Started with |SPARK|
****************************

We begin with a very simple guide aimed at getting new users up and running
with the |SPARK| tools. A small |SPARK| example program will be used for
illustration.

.. note::

   The online version of this User's Guide applies to the latest development
   version of the |SPARK| toolset. If you're using an official release, some of
   the described features may not apply. Refer to the version of the SPARK 2014
   User's Guide shipping with your release, available through
   :menuselection:`Help --> SPARK` in GNAT Studio and GNATbench IDEs, or under
   ``share/doc/spark`` in your |SPARK| installation.

As a prerequisite, it is assumed that the |SPARK| tools have already been
installed. As a minimum you should install:

 - |SPARK| Pro, |SPARK| Discovery or |SPARK| Community
 - GNAT Studio or the GNATbench plug-in of Eclipse

|SPARK| Pro is the most complete toolset for |SPARK|. |SPARK| Discovery is a
reduced toolset that still allows to perform all analyses presented in this
User's Guide, but is less powerful than |SPARK| Pro. Compared to |SPARK| Pro,
|SPARK| Discovery:

 * only comes with one automatic prover instead of three
 * does not include the static analyzer |CodePeer|
 * does not generate counterexamples for failed proofs
 * has limited proof support for programs using modular arithmetic or
   floating-point arithmetic
 * comes without a lemma library for more difficult proofs

|SPARK| Community is a version packaged for free software developers,
hobbyists, and students, which retains most of the capabilities of |SPARK|
Pro. |SPARK| Community does not include the static analyzer |CodePeer|.

Note that GNAT Studio is not strictly required for |SPARK| as all the commands can be
invoked from the command line, or from Eclipse using the GNATbench plug-in, but
the instructions in this section assume that GNAT Studio is being used. If you are a
supported user, you can get more information on how to install the tools in
"AdaCore Installation Procedures" under the "Download" tab in GNAT Tracker, or
by contacting AdaCore for further advice.

The key tools that we will use in this example are |GNATprove| and GNAT Studio.
To begin with, launch GNAT Studio with a new default project and check that the
:menuselection:`SPARK` menu is present in the menu bar.

.. note::

   For SPARK 2005 users, this menu will appear under the name
   :menuselection:`SPARK 2014`, to avoid any confusion with the existing
   :menuselection:`SPARK` menu for SPARK 2005 toolset.

Now open a new file in GNAT Studio and type the following short program into it.
Save this file as ``diff.adb``.

.. literalinclude:: /examples/tests/diff/diff.adb
   :language: ada
   :linenos:

The program is intended to calculate the difference between ``X`` and ``Y`` and
store the result in ``Z``.  This is reflected in the aspect ``Depends`` which
states that the output value of Z depends on the input values of X and Y, but,
as you may have noticed, there is a bug in the code. Note the use of aspect
``SPARK_Mode`` to identify this as |SPARK| code to be analysed with the |SPARK|
tools.  To analyze this program, select :menuselection:`SPARK --> Examine File`
from the menu in GNAT Studio. |GNATprove| executes in flow analysis mode and reports:

.. literalinclude:: /examples/tests/diff/test.out
   :language: none

These messages are informing us that there is a discrepancy between the
program's contract (which says that the value of ``Z`` is obtained from the
values of ``X`` and ``Y``) and its implementation (in which the value of ``Z``
is derived only from the value of ``X``, and ``Y`` is unused). In this case the
contract is correct and the code is wrong, so fix the code by changing the
assignment statement to ``Z := X - Y;`` and re-run the analysis. This time it
should report no messages.

Having established that the program is free from flow errors, now let's run the
tools in proof mode to check for run-time errors.  Select :menuselection:`SPARK
--> Prove File` from the menu in GNAT Studio, and click on ``Execute`` in the resulting
dialog box.  |GNATprove| now attempts to show, using formal verification, that
the program is free from run-time errors. But it finds a problem and highlights
the assignment statement in red, reporting:

.. literalinclude:: /examples/tests/diff2/test.out
   :language: none

This means that the tools are unable to show that the result of subtracting one
``Natural`` number from another will be within the range of the type
``Natural``, which is hopefully not too surprising! There are various ways in
which this could be addressed depending on what the requirements are for this
subprogram, but for now let's change the type of parameter ``Z`` from
``Natural`` to ``Integer``.  If the analysis is re-run with this change in
place then |GNATprove| will report no issues. All checks are proved
so we can be confident that no exceptions will be raised by the execution of
this code.

This short example was intended to give a flavor of the types of analysis that
can be performed with the |SPARK| tools. A more in-depth example is presented
later in :ref:`spark tutorial`.
