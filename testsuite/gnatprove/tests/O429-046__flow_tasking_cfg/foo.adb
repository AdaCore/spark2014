with Ada.Real_Time; use Ada.Real_Time;

package body Foo is

   B : Boolean := False;

   protected type Thing (D : Natural) is
      -- only subprogram/entry decl here
      function P_Func return Boolean;

      procedure P_Proc (F : Boolean; G : out Boolean);

      entry Ent (N : Natural)
        with Pre => N > 10 and B,
             Post => B;
   private
      -- only place data can appear
      A : Boolean := False;
      X : Boolean := D > 5;
   end Thing;

   protected body Thing is
      -- only bodies here
      function P_Func return Boolean is
      begin
         return A or D = 3;
      end P_Func;

      procedure P_Proc (F : Boolean; G : out Boolean) is
      begin
         A := F;
         G := X;
      end P_Proc;

      entry Ent (N : Natural) when A is
      begin
         X := False;
      end Ent;
   end Thing;

   Po_1 : Thing (12);

   task type Test_Task_01 (D : Natural);

   task body Test_Task_01 is
   begin
      Po_1.P_Proc (D > 8, B);
      loop
         B := Po_1.P_Func;
         Po_1.Ent (42);
         B := not B;
      end loop;
   end Test_Task_01;

   procedure Test_Delay_01 is Now : constant Time := Clock;
   begin
      delay until Now + Seconds (5);
   end Test_Delay_01;

end Foo;
