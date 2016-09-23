procedure P with SPARK_Mode is

   type mod_64 is mod 2 ** 64;

   procedure PPP (X : mod_64) with Pre => True is
   begin
      pragma Assert (X < X + 1);  --@ASSERT:FAIL
      pragma Assert (X < mod_64'Last);
   end PPP;

begin

   PPP (mod_64'last);
end P;
