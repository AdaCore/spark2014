package body P with
  Refined_State => (State => S)
is
   S : Integer;
   procedure PP with
     Refined_Global => (In_Out => S)
   is
   begin
      S := S + 1;
   end PP;
end P;
