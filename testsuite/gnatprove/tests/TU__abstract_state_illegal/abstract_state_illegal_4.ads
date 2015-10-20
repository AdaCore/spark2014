package Abstract_State_Illegal_4
  --  TU: 9. If a state abstraction which is declared with an
  --  ``option_list`` that includes a Part_Of ``name_value_option``
  --  whose ``name`` denote a state abstraction, this indicates that
  --  it is a constituent (see :ref:`state_refinement`) of the denoted
  --  state abstraction. [Alternatively, the name may denote a task
  --  or protected unit (see section :ref:`tasks-and-synchronization`).]
  with SPARK_Mode,
       Abstract_State => State
is
   procedure P;
end Abstract_State_Illegal_4;
