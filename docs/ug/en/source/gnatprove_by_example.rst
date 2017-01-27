|GNATprove| by Example
======================

|GNATprove| is based on advanced technology for modular static analysis and
deductive verification. It is very different both from compilers, which do very
little analysis of the code, and static analyzers, which execute symbolically
the program. |GNATprove| does a very powerful local analysis of the program,
but it generally does not cross subprogram boundaries. Instead, it uses the
:ref:`Subprogram Contracts` provided by users to analyze calls. |GNATprove|
also requires sometimes that users direct the analysis with :ref:`Assertion
Pragmas`. Thus, it is essential to understand how |GNATprove| uses contracts
and assertion pragmas. This section aims at providing a deeper insight into how
|GNATprove|'s flow analysis and proof work, through a step-by-step exploration
of small code examples.

All the examples presented in this section, as well as some code snippets
presented in the :ref:`Overview of SPARK Language`, are available in the
example called ``gnatprove_by_example`` distributed with the |SPARK|
toolset. It can be found in the ``share/examples/spark`` directory below the
directory where the toolset is installed, and can be accessed from the IDE
(either GPS or GNATBench) via the :menuselection:`Help --> SPARK --> Examples`
menu item.

.. toctree::
   :maxdepth: 1

   /gnatprove_by_example/basic
   /gnatprove_by_example/loop
   /gnatprove_by_example/manual_proof
