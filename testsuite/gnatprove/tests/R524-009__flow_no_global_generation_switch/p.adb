package body P with Refined_State => (State => A) is
   A : Integer;

   procedure Initialize is
   begin
      A := 0;
   end Initialize;
end P;
