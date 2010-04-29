package body Globals is

   procedure P1a (Cond : Boolean) is
   begin
      if Cond then
         W1 := R1;
      else
         W1 := RW1;
      end if;
      RW1 := W1;
   end P1a;

   procedure P1b (Cond : Boolean) is
   begin
      if Cond then
         RW1 := R1;
      end if;
      W1 := RW1;
   end P1b;

   procedure P2a (Cond : Boolean) is

      procedure S is
      begin
         if Cond then
            W1 := R1;
         else
            W1 := RW1;
         end if;
      end S;

   begin
      S;
      RW1 := W1;
   end P2a;

   procedure P2b (Cond : Boolean) is

      procedure S is
      begin
         if Cond then
            RW1 := R1;
         end if;
      end S;

   begin
      S;
      W1 := RW1;
   end P2b;

end Globals;
