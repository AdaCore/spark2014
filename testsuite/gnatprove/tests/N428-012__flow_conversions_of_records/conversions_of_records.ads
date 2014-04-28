package Conversions_Of_Records
  with SPARK_Mode
is
   type Rec_A is record
      X : Integer;
   end record;

   subtype Rec_B is Rec_A;

   procedure Conv (R  : in     Rec_A;
                   X1 :    out Integer;
                   X2 :    out Integer);
end Conversions_Of_Records;
