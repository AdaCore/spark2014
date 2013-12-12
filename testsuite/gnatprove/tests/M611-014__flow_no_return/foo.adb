package body Foo
is

   procedure Fail with No_Return, Global => null;
   pragma Import (C, Fail);

   --  ok
   procedure Test_01 (Y :    Integer;
                      X: out Integer)
   is
   begin
      if Y >= 0 then
         X := 0;
      else
         Fail;
      end if;
   end Test_01;

   procedure Test_02 (Y :    Integer;
                      X: out Integer)
   is
   begin
      if Y >= 0 then
         X := 0;
      else
         Fail;
         X := Y;  --  dead code
      end if;
   end Test_02;

end Foo;
