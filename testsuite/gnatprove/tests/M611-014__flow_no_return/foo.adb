package body Foo
is

   procedure Fail with No_Return, Global => null;
   pragma Import (C, Fail);

   --  ok
   procedure Test_01 (Y :     Integer;
                      X : out Integer)
   is
   begin
      if Y < 0 then
         Fail;
      end if;
      X := 0;
   end Test_01;

   --  ok
   function Test_03 (Y : Integer) return Integer
   is
   begin
      if Y < 0 then
         Fail;
      end if;
      return 0;
   end Test_03;

   --  ok
   function Test_04 (Y : Integer) return Integer
   is
      R : Integer;
   begin
      if Y < 0 then
         Fail;
      end if;
      R := 0;
      return R;
   end Test_04;

   procedure Nr_Test_01 with No_Return
   is
   begin
      null;
   end Nr_Test_01;

   procedure Nr_Test_02 with No_Return
   is
      X : Integer := 55;
   begin
      loop
         X := X + 1;
         X := X / 2;
      end loop;
      X := 0;
   end Nr_Test_02;

   procedure Nr_Test_03 with No_Return
   is
      X : Integer := 55;
   begin
      loop
         X := X + 1;
         exit when X = 100;
      end loop;
      X := 0;
   end Nr_Test_03;

   procedure Nr_Test_04 with No_Return
   is
   begin
      Fail;
   end Nr_Test_04;

end Foo;
