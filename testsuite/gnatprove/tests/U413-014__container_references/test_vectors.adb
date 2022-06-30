with Ada.Containers; use Ada.Containers;
with SPARK.Containers.Formal.Vectors;

procedure Test_Vectors with SPARK_Mode is
   package Int_Vectors is new SPARK.Containers.Formal.Vectors (Positive, Integer);
   use Int_Vectors;

   procedure Test (V : aliased in out Vector) with
     Pre => Length (V) = 4
     and then Element (V, 1) = 1
     and then Element (V, 2) = 2
     and then Element (V, 3) = 3
     and then Element (V, 4) = 4
   is
   begin
      declare
         C : constant access constant Integer := Constant_Reference (V, 3);
      begin
         pragma Assert (C.all = 3);
      end;
      declare
         V_Acc : access Vector := V'Access;
         E     : constant access Integer := Reference (V_Acc, 3);
      begin
         pragma Assert (E.all = 3);
         E.all := 5;
      end;
      pragma Assert (Length (V) = 4);
      pragma Assert (Element (V, 1) = 1);
      pragma Assert (Element (V, 2) = 2);
      pragma Assert (Element (V, 3) = 5);
      pragma Assert (Element (V, 4) = 4);
   end Test;

   V : aliased Vector (100);
begin
   Append (V, 1);
   Append (V, 2);
   Append (V, 3);
   Append (V, 4);
   Test (V);
end Test_Vectors;
