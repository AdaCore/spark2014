
Use Alternative Compiler
------------------------

:ID: UC.Compiler.UseAlternative
:Overview: Although customers may want to analyse their code using the SPARK 2014 flow analysis and formal verification features, they may not want or be able to compile that code using GNAT.
:Target Rel: |rel 1|
:Priority: Required
:Part of: Base Product
:Current users:
:Future users:

Precondition
^^^^^^^^^^^^

#. Chosen compiler does not support SPARK 2014.

#. Code can be (transformed such that it can be) subjected to flow analysis and/or formal verification using the
   GNAT toolset (or some other tool that implements SPARK 2014). '''NB Add a use case to cover this
   transformation?'''

#. Code can be compiled and built using GNAT toolset.

Scenario
^^^^^^^^

#. Confirm that the code does not contain any SPARK 2014 language features or -- if it does --
   confirm that those language features can be removed while preserving behaviour.

#. Transform the code if necessary to remove all SPARK 2014 language features, while preserving behaviour.

#. Compile and build with alternative compiler.

Scenario Notes
^^^^^^^^^^^^^^

#. For a transformation that removes code to be 'behaviour-preserving' no code that is removed
   can be executable unless it is part of an assertion statement.

#. One of the preconditions is that code can be compiled with GNAT since then we know
   any errors found with the alternative compiler must be due to the presence of SPARK 2014 code.

#. This use case allows the use of either aspects or pragmas to represent the
   SPARK 2014 language features. In the latter case the code does not need to be transformed
   as unknown pragmas are ignored while in the former case the code would need to be
   transformed to strip out the aspects.

#. This use case allows the use of either an alternative Ada 2012 compiler or a compiler for an earlier
   version of Ada.

Postcondition
^^^^^^^^^^^^^

#. Code has been successfully compiled.

#. Executable or executables generated as necessray.

Exceptions and alternative flows
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

#. Code contains SPARK 2014 features within behaviour-affecting code. In this case, it is not
   possible to transform the code base while preserving behaviour.

#. Any other alternative flows are then be covered by the alternative compiler itself. This includes
   the case that the code on which compilation is attempted still contains SPARK 2014 language features.

Special Requirements
^^^^^^^^^^^^^^^^^^^^
None


