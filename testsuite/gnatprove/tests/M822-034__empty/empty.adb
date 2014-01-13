package body Empty is
   pragma SPARK_Mode;

   procedure P is
   begin
      null;
   end P;

   procedure Q is
      pragma SPARK_Mode (Off);
   begin
      pragma Assert (False);
   end Q;

end Empty;
