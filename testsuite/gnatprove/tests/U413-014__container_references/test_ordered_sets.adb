with Ada.Containers; use Ada.Containers;
with SPARK.Containers.Formal.Ordered_Sets;

procedure Test_Ordered_Sets with SPARK_Mode is
   package Int_Sets is new SPARK.Containers.Formal.Ordered_Sets (Integer);
   use Int_Sets;

   procedure Test (S : aliased in out Set) with
     Pre => Length (S) = 4
     and then Contains (S, 1)
     and then Contains (S, 2)
     and then Contains (S, 3)
     and then Contains (S, 4)
   is
   begin
      declare
         F : constant Cursor := Find (S, 3);
         C : constant access constant Integer := Constant_Reference (S, F);
      begin
         pragma Assert (C.all = 3);
      end;
   end Test;

   S : aliased Set (100);
begin
   Insert (S, 1);
   Insert (S, 2);
   Insert (S, 3);
   Insert (S, 4);
   Test (S);
end Test_Ordered_Sets;
