with Lili;

package body User is

   pragma SPARK_Mode (Off);  --  access type

   package Events is new Lili (Integer);

   procedure P is
   begin
      null;
   end P;
end User;
