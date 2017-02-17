with Ada.Assertions; use Ada.Assertions;
with Ada.Text_IO;    use Ada.Text_IO;
with Utils;          use Utils;

procedure While_Loops is pragma SPARK_Mode (On);
   Counter : Natural := 1;

begin
   Put_Line ("While loops");

   --  Loop does not execute, the condition is false

   begin
      Test1 : while Sum_Of (Counter) > 5 loop
      --                           1 > 5
         Put_Line ("ERROR 1: loop should not execute");

         pragma Loop_Invariant (Sum_Of (Counter)'Loop_Entry (Test1) > 0);
         --                                                       1 > 0
         Counter := Counter + 1;  --  to avoid warning
      end loop Test1;
   end;

   --  Loop executes

   begin
      Test2 : while Sum_Of (Counter) < 2 loop
      --                           1 < 2

         --  The invariant assertion must fail

         pragma Loop_Invariant (Sum_Of (Counter)'Loop_Entry (Test2) < 0);
         --                                                       1 < 0

         Put_Line ("ERROR 2: invariant did not fail");
         Counter := Counter + 1;  --  to avoid warning
      end loop Test2;
   end;

   --  Inner loop does not execute, the condition is false. The loop with
   --  special expansion is the outer.

   begin
      Test3a : while Sum_Of (Counter) < 4 loop
      --                            3 < 4
         Test3b : while Sum_Of (2) < 0 loop
         --                      3 < 0
            pragma Loop_Invariant (Counter'Loop_Entry (Test3a) > 0);

            Put_Line ("ERROR 3: loop should not execute");
         end loop Test3b;

         Counter := Counter + 1;
      end loop Test3a;
   end;

   --  Inner loop does not execute, the condition is false. The loop with
   --  special expansion is the inner.

   begin
      Test4a : while Sum_Of (Counter) < 4 loop
      --                            6 < 7
         Test4b : while Sum_Of (2) < 0 loop
         --                      3 < 0
            pragma Loop_Invariant (Counter'Loop_Entry (Test4b) > 0);

            Put_Line ("ERROR 4: loop should not execute");
         end loop Test4b;

         Counter := Counter + 1;
      end loop Test4a;
   end;

end While_Loops;
