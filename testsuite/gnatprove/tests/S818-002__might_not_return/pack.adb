package body Pack with SPARK_Mode is

   procedure Jump (B : Boolean) is
   begin
      raise Program_Error;
   end Jump;

   procedure Call_Jump (B : Boolean) is
   begin
      if B then
         Jump (False);
      end if;
   end Call_Jump;

   procedure Proc is
      B : Boolean := False;
   begin
      Call_Jump (B);
      Call_Jump (not B);
      pragma Assert (B);
   end Proc;

   procedure Call_Jump2 (B : Boolean) renames Call_Jump;

   procedure Effect (B : Boolean) is
   begin
      if B then
         X := not X;
         Jump (False);  --  this will certainly not return
      else
         Y := not Y;
         Call_Jump (B); --  this might not return
      end if;
   end Effect;

end Pack;
