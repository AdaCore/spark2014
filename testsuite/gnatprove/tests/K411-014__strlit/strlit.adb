package body Strlit is

   function DoSome return Integer is
      X : String(1..10) := "1234567890";
      Y : String := "1234567890";
      Z : String := "123456789a";
      F : Five := "12345";
   begin
      return Z'Length;
   end DoSome;
end Strlit;
