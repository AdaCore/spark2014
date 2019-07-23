################
Tool Interaction
################

Besides the use of :ref:`manual_proof` and :ref:`counterexamples`, there are
other features for tool interaction in GNATprove, which are described here.

Explanations for Unproved Checks
================================

When a check is not proved, ``gnat2why`` attempts to recover a simple
explanation pointing out a missing contract or intermediate assertion whose
absence justifies (with high probability) the failure to prove the check.

The function ``Get_Explanation`` in :file:`flow_error_messages.adb` implements
this feature. It traverses the GNAT AST, starting from the node associated to
the check and walking its way in reverse order of execution, towards the start
of the enclosing subprogram or package.

First, it identifies which variables are associated with the check by calling
``Get_Variables_From_Node``. The idea of the traversal is to find a program
point where one of these variables is initialized/modified in a way that the
prover cannot know about it:
 - a call where this variable is modified, but the postcondition of the called
   subprogram does not mention it,
 - a loop where this variable is modified, but the loop invariant does not
   mention it, or
 - the start of the enclosing subprogram taking the variable as input (either
   as parameter or global), but the precondition of the subprogram does not
   mention it.

Various heuristics are used to minimize the risk of incorrect explanations. For
example, the traversal drops from the set of checked variables those that are
assigned to from an expression that does not depend on any variables.

The anaysis is currently limited to full variables. It could be beneficial in
the future to separately track components in the same way that flow analysis
tracks them.
