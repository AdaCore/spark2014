with Ada.Containers.Doubly_Linked_Lists;
with Ada.Assertions; use Ada.Assertions;
with Ada.Text_IO;    use Ada.Text_IO;
with Utils;          use Utils;

procedure Iterator_Loops is pragma SPARK_Mode (Off); --  standard lists
   package DLL is new Ada.Containers.Doubly_Linked_Lists (Integer, "=");

   L       : DLL.List;
   Counter : Natural := 1;

begin
   Put_Line ("Iterator loops");

   --  Loop does not execute, the iterator has no elements

   begin
      Test1 : for Element in DLL.Iterate (L) loop
         pragma Loop_Invariant (Sum_Of (Counter)'Loop_Entry (Test1) > 0);
         --                                                       1 > 0
         Put_Line ("ERROR 1: loop should not execute");
      end loop Test1;
   end;

   --  Loop executes

   DLL.Append (L, 1);
   DLL.Append (L, 2);

   begin
      Test2 : for Element in DLL.Iterate (L) loop

         --  The invariant assertion must fail

         pragma Loop_Invariant (Sum_Of (Counter)'Loop_Entry (Test2) < 0);
         --                                                        1 < 0
         Put_Line ("ERROR 2: invariant did not fail");
      end loop Test2;
   end;

end Iterator_Loops;
