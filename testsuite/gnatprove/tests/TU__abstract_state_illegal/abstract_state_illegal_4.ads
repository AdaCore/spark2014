package Abstract_State_Illegal_4
  --  TU: 9. A state abstraction which is declared with an ``option_list`` that
  --  includes a Part_Of ``name_value_option`` indicates that it is a
  --  constituent (see :ref:`state_refinement`) exclusively of the state
  --  abstraction denoted by the ``abstract_state`` of the
  --  ``name_value_option`` (see :ref:`package_hierarchy`).
  with SPARK_Mode,
       Abstract_State => State
is
   procedure P;
end Abstract_State_Illegal_4;
