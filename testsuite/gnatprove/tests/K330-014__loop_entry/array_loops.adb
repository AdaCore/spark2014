with Ada.Assertions; use Ada.Assertions;
with Ada.Text_IO;    use Ada.Text_IO;
with Utils;          use Utils;

procedure Array_Loops is pragma SPARK_Mode (Off); --  iterator on array
   type Test_Array is array (Natural range <>, Natural range <>) of Natural;
   Counter : Natural := 1;

begin
   Put_Line ("Array loops");

   --  Loop does not execute, second dimension is null

   declare
      TA : Test_Array (1 .. Sum_Of (2), Sum_Of (3) .. 2) :=
             (others => (others => 1));
   begin
      Test1 : for Element of TA loop
         pragma Loop_Invariant (Sum_Of (Counter)'Loop_Entry (Test1) > 0);
         --                                                       1 > 0
         Put_Line ("ERROR 1: loop should not execute");
      end loop Test1;
   end;

   --  Loop executes

   declare
      TA : Test_Array (1 .. Sum_Of (2), Sum_Of (1) .. Sum_Of (3)) :=
             (others => (others => 2));
   begin
      Test2 : for Element of TA loop
         pragma Loop_Invariant
           (Sum_Of (Counter)'Loop_Entry (Test2) < Sum_Of (Counter));
         Counter := Counter + 1;
      end loop Test2;
   end;

end Array_Loops;
