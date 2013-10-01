package Functions_Illegal
  with SPARK_Mode
is
   G_Var : Integer;

   function Cant_Have_Global_Out return Integer
     --  TU: 5. A function declaration shall not have a
     --  ``parameter_specification`` with a mode of **out** or **in out**. This
     --  rule also applies to a ``subprogram_body`` for a function for which no
     --  explicit declaration is given.
     with Global => (Output => G_Var);


   function Cant_Have_Global_In_Out return Integer
     --  TU: 5. A function declaration shall not have a
     --  ``parameter_specification`` with a mode of **out** or **in out**. This
     --  rule also applies to a ``subprogram_body`` for a function for which no
     --  explicit declaration is given.
     with Global => (In_Out => G_Var);

end Functions_Illegal;
