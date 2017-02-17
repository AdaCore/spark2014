package body Strlit with SPARK_Mode is

   function DoSome return Integer is
      X : Mod_String (1..10) := "1234567890";
      Y : Mod_String := "1234567890";
      Z : Mod_String := "123456789a";
      F : Five := "12345";
   begin
      pragma Assert (Y'First = 0);
      return Z'Length;
   end DoSome;
end Strlit;
