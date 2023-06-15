procedure Main with SPARK_Mode is

   --  The termination of loops is checked

   procedure Do_Loop (B : Boolean) with
     Always_Terminates => not B
   is
   begin
      if not B then
         return;
      end if;
      loop
         null;
      end loop;
   end Do_Loop;

   procedure Bad_Do_Loop (B : Boolean) with
     Always_Terminates => not B
   is
   begin
      if B then
         return;
      end if;
      loop
         null;
      end loop;
   end Bad_Do_Loop;

   procedure Do_Loop with
     Always_Terminates => False
   is
   begin
      loop
         null;
      end loop;
   end Do_Loop;

   --  The termination of non-terminating procedure calls is checked

   procedure Call_1 (B : Boolean) with
     Always_Terminates => not B
   is
   begin
      if not B then
         return;
      end if;
      Do_Loop;
   end Call_1;

   procedure Call_2 (B : Boolean) with
     Always_Terminates => not B
   is
   begin
      Do_Loop (B);
   end Call_2;

   procedure Call_3 (B : Boolean) with
     Always_Terminates
   is
   begin
      if not B then
         Do_Loop (B);
      end if;
   end Call_3;

   function Call_4 (B : Boolean) return Boolean is
   begin
      if not B then
         Do_Loop (B);
      end if;
      return True;
   end Call_4;

   procedure Bad_Call_1 (B : Boolean) with
     Always_Terminates => not B
   is
   begin
      if B then
         return;
      end if;
      Do_Loop;
   end Bad_Call_1;

   procedure Bad_Call_2 (B : Boolean) with
     Always_Terminates => not B
   is
   begin
      Do_Loop (not B);
   end Bad_Call_2;

   procedure Bad_Call_3 (B : Boolean) with
     Always_Terminates
   is
   begin
      Do_Loop (B);
   end Bad_Call_3;

   function Bad_Call_4 (B : Boolean) return Boolean is
   begin
      Do_Loop (B);
      return True;
   end Bad_Call_4;

   --  Test inherited Always_Terminates annotations

   package Nested_1 with Always_Terminates is
      procedure Call (B : Boolean);
      procedure Bad_Call (B : Boolean);
   end Nested_1;

   package body Nested_1 is
      procedure Call (B : Boolean) is
      begin
         if not B then
            Do_Loop (B);
         end if;
      end Call;

      procedure Bad_Call (B : Boolean) is
      begin
         Do_Loop (B);
      end Bad_Call;

      procedure Bad_Call_2 (B : Boolean) is
      begin
         Do_Loop (B);
      end Bad_Call_2;
   end Nested_1;

   --  Check that we detect RTE in termination conditions

   procedure Bad_Pre (A, B : Integer) with
     Import,
     Global => null,
     Always_Terminates => A / B > 1;  -- DIVISION_CHECK:FAIL

   procedure OK_Pre (A, B : Integer) with
     Import,
     Global => null,
     Pre => A /= Integer'First and B /= 0,
     Always_Terminates => A / B > 1;  -- DIVISION_CHECK:PASS

   --  Check that we detect cases of statically non-terminating calls in
   --  procedures with dynamic termination conditions:
   --  * call through access
   --  * dispatching calls
   --  * recursive calls with no variants

   procedure Call_Access (B : Boolean; F : not null access function return Integer) with
     Always_Terminates => not B
   is
      C : Integer := F.all;
   begin
      if B then
         loop
            null;
         end loop;
      end if;
   end Call_Access;

   package Nested_2 is
      type Root is tagged null record;
      function Disp (X : Root) return Integer is (1);
   end Nested_2;

   procedure Call_Disp (B : Boolean; X : Nested_2.Root'Class) with
     Always_Terminates => not B
   is
      C : Integer := X.Disp;
   begin
      if B then
         loop
            null;
         end loop;
      end if;
   end Call_Disp;

   procedure Call_Rec (B : Boolean) with
     Always_Terminates => not B;

   function Rec return Integer with Pre => True;

   function Rec return Integer is
   begin
      Call_Rec (False);
      return 15;
   end Rec;

   procedure Call_Rec (B : Boolean) is
      C : Integer := Rec;
   begin
      if B then
         loop
            null;
         end loop;
      end if;
   end Call_Rec;

begin
   null;
end Main;
