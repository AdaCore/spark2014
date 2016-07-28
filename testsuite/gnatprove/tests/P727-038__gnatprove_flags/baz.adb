package body Baz is

   function Id (B : Boolean) return Boolean is (B);

   procedure Hello is
   begin
      pragma Assert (Id (True));
   end Hello;

end Baz;
