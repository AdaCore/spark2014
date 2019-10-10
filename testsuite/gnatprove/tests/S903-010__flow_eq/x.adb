procedure X is
   type Y is new Natural;
   function "=" (Left, Right : Y) return Boolean with Pre => True;
   pragma Annotate (GNATprove, Terminating, "=");

   function "=" (Left, Right : Y) return Boolean is
   begin
      while True loop
         null;
      end loop;
      return True;
   end;

   A, B : Y := 0;
begin
   pragma Assert (A = B);
end;
