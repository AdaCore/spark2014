package body Foo
is

   procedure Fail with No_Return, Global => null;
   pragma Import (C, Fail);

   --  ok
   procedure Test_01 (Y :     Integer;
                      X : out Integer)
   is
   begin
      if Y >= 0 then
         X := 0;
      else
         Fail;
      end if;
   end Test_01;

   procedure Test_02 (Y :    Integer;
                      X : out Integer)
   is
   begin
      if Y >= 0 then
         X := 0;
      else
         Fail;
         X := Y;  --  dead code
      end if;
   end Test_02;

   --  ok
   function Test_03 (Y : Integer) return Integer
   is
   begin
      if Y >= 0 then
         return 0;
      else
         Fail;
      end if;
   end Test_03;

   --  ok
   function Test_04 (Y : Integer) return Integer
   is
      R : Integer;
   begin
      if Y >= 0 then
         R := 0;
      else
         Fail;
      end if;
      return R;
   end Test_04;

   function Test_05 (Y : Integer) return Integer
   is
      R : Integer;
   begin
      if Y >= 0 then
         R := 0;
      else
         Fail;
         R := -1; -- dead code
      end if;
      return R;
   end Test_05;

end Foo;
