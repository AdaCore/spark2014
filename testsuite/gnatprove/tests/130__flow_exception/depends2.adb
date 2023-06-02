procedure Depends2
  with Global => null
is
   procedure Test (X : Integer; Y : in out Integer)
     with Exceptional_Cases => (Program_Error => True),
          Depends => (Y => X, null => Y)
   is
   begin
      if X > 0 then
         Y := X;
      else
         raise Program_Error;
      end if;
   end Test;

   Z : Integer := 456;
begin
   Test (123, Z);
exception
   when Program_Error =>
      pragma Assert (Z = 456);
end;
