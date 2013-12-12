package body Foo
is

   procedure Fail with No_Return, Global => null;
   pragma Import (C, Fail);

   procedure P (Y :    Integer;
                X: out Integer)
   is
   begin
      if Y >= 0 then
         X := 0;
      else
         Fail;
      end if;
   end P;

end Foo;
