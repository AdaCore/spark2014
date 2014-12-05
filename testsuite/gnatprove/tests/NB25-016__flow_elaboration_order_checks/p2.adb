package body P2
  with Refined_State => (State => Hidden_Var)
is
   Hidden_Var : Integer;

   procedure P is
   begin
      Hidden_Var := P1.Read_From_State;
   end P;
begin
   P;
end P2;
