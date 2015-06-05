with Ada.Real_Time; use Ada.Real_Time;

package body Foo
is

   B : Boolean := False;

   protected type Thing is
      -- only procedure decl here
      function Test return Boolean with Global => null;
      entry Ent (N : Natural)
        with Pre => N > 10 and B,
             Post => B;
   private
      -- only place data can appear
      A : Boolean := False;
      X : Boolean := True; -- D > 5;
   end Thing;

   protected body Thing is
      -- only bodies here
      function Test return Boolean is
      begin
         return A;
      end Test;

      entry Ent (N : Natural) when A is
      begin
         X := False;
      end Ent;
   end Thing;

   Po_1 : Thing;

   task type Test_Task_01 (D : Natural);

   task body Test_Task_01 is
   begin
      B := D > 8;
      loop
         --B := Po_1.Test;
         --Po_1.Ent;
         B := not B;
      end loop;
   end Test_Task_01;

   procedure Test_Delay_01
   is
   begin
      delay until Clock + Seconds (5);
   end Test_Delay_01;




end Foo;
