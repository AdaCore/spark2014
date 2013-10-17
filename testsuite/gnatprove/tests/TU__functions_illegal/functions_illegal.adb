package body Functions_Illegal
  with SPARK_Mode
is
   function Cant_Have_Global_Out return Integer is
   begin
      G_Var := 5;
      return 5;
   end Cant_Have_Global_Out;

   function Cant_Have_Global_In_Out return Integer is
   begin
      G_Var := G_Var + 1;
      return G_Var;
   end Cant_Have_Global_In_Out;

   function Only_Body_Func_Cant_Have_Global_Out return Integer
     --  TU: 5. A function declaration shall not have a
     --  ``parameter_specification`` with a mode of **out** or **in out**. This
     --  rule also applies to a ``subprogram_body`` for a function for which no
     --  explicit declaration is given.
     with Global => (Output => G_Var)
   is
   begin
      G_Var := 5;
      return 5;
   end Only_Body_Func_Cant_Have_Global_Out;

   function Only_Body_Func_Cant_Have_Global_In_Out return Integer
     --  TU: 5. A function declaration shall not have a
     --  ``parameter_specification`` with a mode of **out** or **in out**. This
     --  rule also applies to a ``subprogram_body`` for a function for which no
     --  explicit declaration is given.
     with Global => (In_Out => G_Var)
   is
   begin
      G_Var := G_Var + 1;
      return G_Var;
   end Only_Body_Func_Cant_Have_Global_In_Out;
end Functions_Illegal;
