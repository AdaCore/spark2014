package body Globals is

   --  Global variables used to show state annotations
   B2 : Integer := 41;
   B1 : Integer;
   B3 : Integer := 314;

   procedure Proc (Cond : Boolean) is
      R2, W2, RW2 : Integer;

      --  Local procedure used to show global annotations
      procedure S is
      begin
         if Cond then
            W2 := R2;
         else
            W2 := RW2;
         end if;
         RW2 := RW1;
         W1  := R1;
      end S;

   begin
      R2  := R1;
      RW2 := RW1;
      S;
      if Cond then
         RW1 := RW2;
      end if;
      B1 := W2;
   end Proc;

end Globals;
