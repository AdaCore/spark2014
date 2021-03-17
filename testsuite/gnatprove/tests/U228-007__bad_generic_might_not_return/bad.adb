package body Bad with SPARK_Mode is

   procedure Jump is
   begin
      raise Program_Error;
   end Jump;

   function Call_Jump_Fun return Boolean is
   begin
      Jump;
      return True;
   end Call_Jump_Fun;

   procedure Call_Jump_Gen (B : Boolean) is
   begin
      if B then
         Jump;
      end if;
      raise Constraint_Error;
   end Call_Jump_Gen;

   procedure Call_Jump is new Call_Jump_Gen;

   function Silent_Call_Jump return Boolean is
   begin
      Call_Jump (True);
      return True;
   end Silent_Call_Jump;

   procedure Proc (X : T) is
   begin
      Call_Jump (True);
   end Proc;

end Bad;
