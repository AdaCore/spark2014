Restrictions and Profiles
=========================

A list of restrictions by section and their effect:


6.1 Subprogram Declarations
    
 ``1.`` No_Default_Subprogram_Parameters

  Prohibits the use of default subprogram parameters, that is, a ``parameter_specification`` cannot have a ``default_expression``.


6.1.4 Mode Refinement

 ``1.`` Moded_Variables_Are_Entire 
 
  Asserts that a ``moded_item`` cannot be a subcomponent name.

 ``2.`` No_Conditional_Modes

  Prohibits the use of a ``conditional_mode`` in a ``mode_specification``.

6.1.5 Global Aspects

 ``1.`` No_Scope_Holes

  A subprogram, P, shall not declare an entity of the same name as a
  ``moded_item`` or the name of the object of which the ``moded_item``
  is a subcomponent in its ``global_aspect`` within a
  ``loop_statement`` or ``block_statement`` whose nearest enclosing
  program unit is P.
  
 ``2.`` Global_Aspects_Required

  Prohibits the use of a ``conditional_mode`` in a ``mode_specification``.
