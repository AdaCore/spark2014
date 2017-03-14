package Test_Eq with SPARK_Mode is
   type My_Rec is record
      F1 : Integer;
      F2 : Integer;
   end record;

   B : Boolean := True;

   function "=" (X, Y : My_Rec) return Boolean is (B and X.F1 = Y.F1);

   type R is record
      G : My_Rec;
   end record;

   procedure P with Global => null; --  This contract is wrong!
end Test_Eq;
