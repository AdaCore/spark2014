package body P with
  Refined_State => (State  => S,
                    State2 => S2,
                    State3 => S3,
                    State4 => S4)
is
   S  : Integer;
   S2 : Integer := 2;
   S3 : Integer;
   S4 : Integer;

   procedure PP with
     Refined_Global => (In_Out => S)
   is
   begin
      S := S + 1;
   end PP;

   procedure PP2 with
     Refined_Global => (Output => S3)
   is
   begin
      S3 := 5;
   end PP2;

   procedure PP3 is
   begin
      S4 := 5;
   end PP3;
end P;
