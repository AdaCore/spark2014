separate (Pack)
package body Inner
  with Refined_State => (Inner_State => Inner_Body_Var)
is
   Inner_Body_Var : Integer;

   procedure Initialize_Inner
     with Refined_Global  => (Output => (Inner_Body_Var, Inner_Var),
                              Input  => Var),
          Refined_Depends => (Inner_Body_Var => null,
                              Inner_Var      => Var)
   is
   begin
      Inner_Body_Var := 0;
      Inner_Var      := Var;
   end Initialize_Inner;
begin
   Initialize_Inner;
end Inner;
