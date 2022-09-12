with Ada.Containers; use Ada.Containers;
with SPARK.Containers.Formal.Hashed_Maps;

procedure Test_Hashed_Maps with SPARK_Mode is
   function Hash (Id : Positive) return Hash_Type is (Hash_Type (Id));
   package Int_Maps is new SPARK.Containers.Formal.Hashed_Maps (Positive, Integer, Hash);
   use Int_Maps;

   procedure Test (M : aliased in out Map) with
     Pre => Length (M) = 4
     and then Contains (M, 1)
     and then Contains (M, 2)
     and then Contains (M, 3)
     and then Contains (M, 4)
     and then Element (M, 1) = 1
     and then Element (M, 2) = 2
     and then Element (M, 3) = 3
     and then Element (M, 4) = 4
   is
      F : constant Cursor := Find (M, 3);
   begin
      declare
         C : constant access constant Integer := Constant_Reference (M, F);
      begin
         pragma Assert (C.all = 3);
      end;
      declare
         C : constant access constant Integer := Constant_Reference (M, 3);
      begin
         pragma Assert (C.all = 3);
      end;
      declare
         M_Acc : access Map := M'Access;
         E     : constant access Integer := Reference (M_Acc, 3);
      begin
         pragma Assert (E.all = 3);
         E.all := 5;
      end;
      pragma Assert (Length (M) = 4);
      pragma Assert (Contains (M, 1));
      pragma Assert (Contains (M, 2));
      pragma Assert (Contains (M, 3));
      pragma Assert (Contains (M, 4));
      pragma Assert (Element (M, 1) = 1);
      pragma Assert (Element (M, 2) = 2);
      pragma Assert (Element (M, 3) = 5);
      pragma Assert (Element (M, 4) = 4);
      pragma Assert (Element (M, F) = 5);
      pragma Assert (Key (M, F) = 3);
      declare
         M_Acc : access Map := M'Access;
         E     : constant access Integer := Reference (M_Acc, F);
      begin
         pragma Assert (E.all = 5);
         E.all := 7;
      end;
      pragma Assert (Length (M) = 4);
      pragma Assert (Contains (M, 1));
      pragma Assert (Contains (M, 2));
      pragma Assert (Contains (M, 3));
      pragma Assert (Contains (M, 4));
      pragma Assert (Element (M, 1) = 1);
      pragma Assert (Element (M, 2) = 2);
      pragma Assert (Element (M, 3) = 7);
      pragma Assert (Element (M, 4) = 4);
      pragma Assert (Element (M, F) = 7);
      pragma Assert (Key (M, F) = 3);
   end Test;

   M : aliased Map (100, Default_Modulus (100));
begin
   Insert (M, 1, 1);
   Insert (M, 2, 2);
   Insert (M, 3, 3);
   Insert (M, 4, 4);
   Test (M);
end Test_Hashed_Maps;
