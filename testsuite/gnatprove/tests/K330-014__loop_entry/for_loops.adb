with Ada.Assertions; use Ada.Assertions;
with Ada.Text_IO;    use Ada.Text_IO;
with Utils;          use Utils;

procedure For_Loops is pragma SPARK_Mode (On);
   Counter : Natural := 1;

begin
   Put_Line ("For loops");

   --  Loop does not execute, the condition is false

   begin
      Test1 : for I in Sum_Of (3) .. 2 loop
      --                        6 .. 2
         pragma Loop_Invariant (Sum_Of (Counter)'Loop_Entry (Test1) > 0);
         --                                                        1 > 0
         Put_Line ("ERROR 1: loop should not execute");
      end loop Test1;
   end;

   --  Loop executes

   begin
      Test2 : for I in 2 .. Sum_Of (3) loop
      --               2 .. 6
         --  The invariant assertion must fail

         pragma Loop_Invariant (Sum_Of (Counter)'Loop_Entry (Test2) < 0);
         --                                                       1 < 0

         Put_Line ("ERROR 2: invariant did not fail");
      end loop Test2;
   end;

   --  Inner loop does not execute, the range is null. The loop with special
   --  expansion is the outer.

   begin
      Test3a : for X in 1 .. Sum_Of (Counter) loop
      --                1 .. 3
         Test3b : for Y in Sum_Of (5) .. 3 loop
         --                        15 .. 3
            pragma Loop_Invariant (Counter'Loop_Entry (Test3a) = 1);

            Put_Line ("ERROR 3: loop should not execute");
         end loop Test3b;
      end loop Test3a;
   end;

   --  Inner loop does not execute, the range is null. The loop with special
   --  expansion is the inner.

   begin
      Test4a : for X in 1 .. Sum_Of (Counter) loop
      --                1 .. 3
         Test4b : for Y in Sum_Of (4) .. 3 loop
         --                        10 .. 3
            Put_Line ("ERROR 4: loop should not execute");

            pragma Loop_Invariant (Counter'Loop_Entry (Test4b) = 1);
         end loop Test4b;
      end loop Test4a;
   end;

end For_Loops;
