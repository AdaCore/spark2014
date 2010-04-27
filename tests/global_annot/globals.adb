package body Globals is

   --  Global variables used to show state annotations
   B2     : Integer := 41;
   B1, B3 : Integer;

   procedure Proc (Cond : Boolean) is
      R2, W2, RW2 : Integer;

      procedure S is
      begin
         if Cond then
            W2 := R2;
         else
            W2 := RW2;
         end if;
         RW2 := RW1;
         W1  := W2;
      end S;
   begin
      if Cond then
         R2  := 0;
         RW2 := RW1;
      else
         R2  := R1;
         RW2 := 0;
      end if;
      S;
   end Proc;

begin

   D3 := 0;
   B3 := 314;

end Globals;
