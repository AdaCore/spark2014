with Ada.Assertions; use Ada.Assertions;
with Ada.Text_IO;    use Ada.Text_IO;
with Utils;          use Utils;

procedure Optional is pragma SPARK_Mode (On);
   type Test_Array is array (Natural range <>) of Natural;
   type Test_2D_Array is array (Natural range <>, Natural range <>) of Natural;

begin
   Put_Line ("Optional");

   declare
      TA : Test_Array (1 .. 5) := (others => 0);

   begin
      for Index in TA'Range loop
         pragma Loop_Invariant (TA'Loop_Entry (Index) = 0);

         TA (Index) := 1;
      end loop;
   end;

   declare
      TA : Test_2D_Array (1 .. 3, 1 .. 2) := (others => (others => 0));

   begin
      TA (Sum_Of (2), 2) := 1;

      for Outer in TA'First (1) .. TA'Last (1) loop
         for Inner in TA'First (2) .. TA'Last (2) loop
            pragma Loop_Invariant (TA'Loop_Entry (Outer, Inner) = 0);
            null;
         end loop;
      end loop;
      Put_Line ("ERROR 2: should not get here");
   end;

end Optional;
