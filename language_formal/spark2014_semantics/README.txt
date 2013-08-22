
SPARK Formalization Tool Chain

==========
 Overview 
==========
The tool chain consists of two major tools:
- Jago: which performs two kinds of translation, (1) type translation, which translates gnat2xml-generated XML Schema to (inductive) type definitions in Coq and OCaml, and (2) Program Translation, which translates SPARK programs from gnat2xml-generated AST XML to Coq and OCaml code that constructs the AST;

- Verified Interpreter: which is developed and proved correct in Coq with respect to SPARK 2014 reference semantics;


=================
 Coq Source Code
=================
Coq source code for SPARK subset formalization are organized in the following modules:

- language.v: defines the SPARK 2014 language subset that we are working on now, which will be extended with more language features;

- values.v: defines the basic values (bool and integer) and a set of value operations that are used to define the language semantics;

- environment.v: defines stack, symbol table and type of program execution states;

- util.v: defines some general-purpose tactics;

- checks.v: all SPARK checking rules are formalized here;

- semantics.v: defines the language reference semantics and its corresponding functional semantics, with proof showing their semantical equivalence;

- wellformedness.v: defines the well-formness for the SPARK program, including well-typed, well-defined and well-checked;

- propertyProof.v: proves that any well-formed program, if it can terminate, then it either terminates in a valid state or a run time error that's captured by run time checks;

- test.v: gives several tests cases to familiarize oneself with the SPARK 2014 semantics and shows that well-formed program will run correct;


=================
 Getting Started
=================
(Note: I have revised my Jago tool and committed the changes to the repository. But when I tested its development version downloaded from http://www.sireum.org/download, it still gives the old output. I will fix it.)

1. Download and install Sireum (development release) by following the instructions at: http://www.sireum.org/download

Note: before run "sireum", make sure that "...\Coq\bin", "...\jdk7\bin" and "...\jdk7\jre\bin" are in the PATH, otherwise, sireum will terminate in error;

2. Type and Program Translation

2.1. command: "sireum bakar type -t Coq" will translate XML Schema into type definition in Coq; 
	      "sireum bakar type -t Ocaml" will translate XML Schema into type definition in Ocaml;

2.2. command: "sireum bakar program -p Coq <SPARK_Source_File> [<Destination_File>]" translate the SPARK program into Coq AST;
              "sireum bakar program -p Ocaml <SPARK_Source_File> [<Destination_File>]" translate the SPARK program into Ocaml AST;

3. Up to now, we have only formalized the language semantics at the intra-procedure level, to test our Verified Interpreter, we have to extract the procedure body, starting from the keyword "Procedure", from the Jago generated Coq AST tree, and then run this procedure in Coq with the following command:
    "Eval compute in (f_eval_subprogram <execution_steps> <initial_stack> <procedure_in_Coq_AST>)."
For example:
    "Eval compute in (f_eval_subprogram 100 nil f)." means that run the procedure f, starting from empty stack, within 100 execution steps.

Please see test.v for some small examples.


============
 Next Steps
============
1. Extend the language subset with more SPARK features, for example, functional call, Pre/Post contract and loop invariants;
2. Add run time checks optimizations and prove its correctness;
3. Develop verified static analysis and translation tools based on current language formalization work;






