package test_record_cnt_ex with SPARK_Mode is
   package Hide_Id is
      function Id (X : Integer) return Integer;
   private
      pragma SPARK_Mode (Off);
      function Id (X : Integer) return Integer is (X);
   end Hide_Id;
   use Hide_Id;

   type Root is tagged record
      F1 : Integer;
   end record;

   package Nested_1 is
      type Hidden_1 is new Root with private;
      C : constant Hidden_1;
   private
      type Hidden_1 is new Root with record
         F2 : Integer;
      end record;
      C : constant Hidden_1 := (F1 => 1, F2 => 2);
   end Nested_1;

   type Two_F2 is new Nested_1.Hidden_1 with record
      F2 : Integer;
   end record;

   X_1 : Two_F2 := (Nested_1.C with F2 => 3);
   Y_1 : Two_F2 := (Nested_1.C with F2 => Id (3));
   pragma Assert (X_1 = Y_1); --@ASSERT:FAIL
   --  missing Nested_1.F2
   --  expected (e.g. when X_1 = (F1 => 1, Nested_1.F2 => 2, F2 => 3) and Y_1 = (F1 => 1, Nested_1.F2 => 2, F2 => 0))

   package Nested_2 is
      type Hidden_2 is new Root with private;
      C : constant Hidden_2;
   private
      pragma SPARK_Mode (Off);
      type Hidden_2 is new Root with record
         Bad : Integer;
      end record;
      C : constant Hidden_2 := (F1 => 1, Bad => 2);
   end Nested_2;

   type Hidden_Info is new Nested_2.Hidden_2 with record
      F2 : Integer;
   end record;

   X_2 : Hidden_Info := (Nested_2.C with F2 => 4);
   Y_2 : Hidden_Info := (Nested_2.C with F2 => Id (4));
   pragma Assert (X_2 = Y_2); --@ASSERT:FAIL
   --  missing hidden state from Nested_2
   --  expected (e.g. when X_1 = (F1 => 0, F2 => 4, others => ?) and Y_1 = (F1 => 1, F2 => 0, others => ?))

   package Nested_3 with Abstract_State => null, Initializes => null is
      type Complex (B : Boolean) is tagged private;
      type No_F is tagged private;
      type F_Present is tagged private;
      X, Y : constant No_F;
      W, Z : constant F_Present;
   private
      type Complex (B : Boolean) is tagged record
         G : Integer;
         case B is
         when True =>
            F : Integer;
         when False => null;
         end case;
      end record;

      type No_F is new Complex (False) with null record;
      type F_Present is new Complex (True) with null record;
      X : constant No_F := (B => False, G => 7);
      Y : constant No_F := (B => False, G => Id (7));
      W : constant F_Present := (B => True, G => 3, F => 6);
      Z : constant F_Present := (B => True, G => 3, F => Id (6));
   end Nested_3;

   type No_F is new Nested_3.No_F with record
      G : Integer;
   end record;
   type F_Present is new Nested_3.F_Present with record
      G : Integer;
   end record;
   X : constant No_F := (Nested_3.X with G => 8);
   Y : constant No_F := (Nested_3.Y with G => 8);
   W : constant F_Present := (Nested_3.W with G => 8);
   Z : constant F_Present := (Nested_3.Z with G => 8);

   pragma Assert (X = Y); --@ASSERT:FAIL
   --  the current value given for 'G' should be labelled Nested_3.G and visible
   --  G should be displayed as well, but not Nested_3.F.
   --  expected (e.g. when X = (B => ?, Nested_3.G => 7, G => 8) and Y = (B => ?, Nested_3.G => 0, G => 8))
   pragma Assert (Z = W); --@ASSERT:FAIL
   --  As before except that Nested_3.F should be displayed too
   --  expected (e.g. when W = (B => ?, Nested_3.G => 3, Nested_3.F => 6, G => 8) and Z = (B => ?, Nested_3.G => 3, Nested_3.F => 0, G => 8))
end test_record_cnt_ex;
