limited with Initializes_Illegal_5.Pr_Child;

package Initializes_Illegal_5
  --  TU: 9. An ``initialization_item`` shall have a an ``input_list`` if and
  --  only if its initialization is dependent on visible variables and
  --  state anbstractions not declared within the package containing the
  --  Initializes aspect. Then the ``names`` in the ``input_list`` shall
  --  denote variables and state abstractions which are used in
  --  determining the initial value of the state abstraction or variable
  --  denoted by the ``name`` of the ``initialization_item`` but are not
  --  constituents of the state abstraction.
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => (State => Initializes_Illegal_5.Pr_Child.Pr_Var)
is
   function F1 return Integer
     with Global => State;
end Initializes_Illegal_5;
