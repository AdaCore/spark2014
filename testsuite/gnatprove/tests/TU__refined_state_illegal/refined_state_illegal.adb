package body Refined_State_Illegal
  with SPARK_Mode
is
   package body Pac1
      with Refined_State  => (S => (Var1, null))
   is
      Var1 : Natural;

      procedure P1 is begin null; end P1;
   end Pac1;


   package body Pac3
   is
      Var1 : Boolean;

      function F1 return Boolean
      is
         (Var1);
   end Pac3;


   package body Pac4
      with Refined_State => (S => null)
   is
      procedure P1 is begin null; end P1;
   end Pac4;


   package body Pac5
      with Refined_State => (S => F1)
   is
      function F1 return Boolean
      is
         (True);
   end Pac5;


   package body Pac6
      with Refined_State => (S => (Rec, Rec.A))
   is
      Rec : Record_T;

      procedure P1 is begin null; end P1;
   end Pac6;


   package body Pac7
      with Refined_State => (S1 => Var1)
   is
      Var1 : Boolean;

      procedure P1 is begin null; end P1;
   end Pac7;


   package body Pac8
      with Refined_State => (S1 => Pr_Var1,
                             S2 => (Pr_Var1, Pr_Var2))
   is
      procedure P1 is begin null; end P1;
   end Pac8;


   package body Pac9
      with Refined_State => (S => null)
   is
      Var1 : Integer := 10;

      function F1 return Integer
         with Refined_Global => Var1
      is
      begin
         return Var1;
      end F1;
   end Pac9;


   package body Pac10
      with Refined_State => (S1 => Var)
   is
      Var : Integer;

      procedure P1 is begin null; end P1;
   end Pac10;
end Refined_State_Illegal;
