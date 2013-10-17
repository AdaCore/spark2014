package body Initializes_Illegal_4
  with SPARK_Mode
is
   package body Pac1
     with Refined_State => (State => (Y,
                                      Z))
   is
      Y : Integer;
      Z : Integer := 5;  -- Z should not be initialized
   begin
      X := 10;  --  X should not be initialized
   end Pac1;

   package body Pac2
     with Refined_State => (State  => Body_Var,
                            State2 => (Body_Var2,
                                       Body_Var3))
   is
      Body_Var, Body_Var2, Body_Var3 : Integer;
   begin
      Body_Var  := 0;
      Body_Var2 := Body_Var;  --  Body_Var2 should not be initialized
   end Pac2;

   package body Pac3
     with Refined_State => (State => Body_Var)
   is
      function F1 return Integer is (G_Var2);

      Body_Var : Integer := G_Var - F1;  --  Body_Var should only depend on
                                         --  G_Var for its initialization
   end Pac3;
end Initializes_Illegal_4;
