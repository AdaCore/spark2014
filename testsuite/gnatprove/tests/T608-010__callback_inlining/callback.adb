procedure Callback is

   X : Integer := 0;

   procedure Set (X : in out Integer) is
   begin
      if X = 1 then
         raise Program_Error; -- @RAISE:FAIL
      end if;
      X := 42;
   end Set;

   type Ptr is access procedure (X : in out Integer);

   G : Ptr := Set'Access;

begin
   Set (X);
   pragma Assert (X = 42); -- @ASSERT:PASS
   X := 1;
   G (X);
end Callback;
