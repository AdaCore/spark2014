package body Bar is

   function Id (B : Boolean) return Boolean is (B);

   procedure Hello is
   begin
      pragma Assert (Id (True));
   end Hello;

end Bar;
