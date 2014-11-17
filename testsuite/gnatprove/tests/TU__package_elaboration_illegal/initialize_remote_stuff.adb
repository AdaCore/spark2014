with Remote; use Remote;
pragma Elaborate_All(Remote);

package body Initialize_Remote_Stuff
  with SPARK_Mode
is
   procedure Initialize_Remote_Var is
   begin
      Var := 0;
   end Initialize_Remote_Var;

   procedure Initialize_Remote_State is
   begin
      Init_State;
   end Initialize_Remote_State;

begin
   Var := 0;                --  Cannot initialize remote variabler.
   Init_State;              --  Cannot initialize remote state.
   Initialize_Remote_Var;   --  Cannot initialize remote variable.
   Initialize_Remote_State; --  Cannot initialize remote state.
end Initialize_Remote_Stuff;
