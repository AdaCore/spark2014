procedure Test_First_Bound_Rejected with SPARK_Mode is
 
   procedure Test_9 with Global => null is
      type Int_Array is array (Positive range <>) of Integer;
      function Id (X : Integer) return Integer is (X);
      subtype My_Arr is Int_Array (1 .. <>);
      subtype My_Arr_Bad is My_Arr (Id (7) .. <>); --a check should fail here
   begin
      null;
   end Test_9;

   procedure Test_11 with Global => null is
      type Int_Array is array (Positive range <>) of Integer;
      function Id (X : Integer) return Integer is (X);
      subtype My_Arr is Int_Array (1 .. <>);
      subtype My_Arr_1 is My_Arr (Id (1) .. <>);
   begin
      null;
   end Test_11;

begin
   Test_11;
end Test_First_Bound_Rejected;
