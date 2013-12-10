package body Pack
   with Refined_State => (State => X)
is
   X : Integer := 3;

   function Is_Valid return Boolean is (X = 3)
      with Refined_Global => X;

   procedure P
      with Refined_Global => X
   is
   begin
      null;
   end P;
begin
   X := 3;
end Pack;
