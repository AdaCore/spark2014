procedure Foo is
   X : Boolean := False;
begin
   declare
      generic
      procedure Bar;

      procedure Bar is
      begin
         null;
      end;

   begin
      pragma Assert (X);
   end;
end;
