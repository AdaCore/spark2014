package body P with
  SPARK_Mode
is
   package body Nested_1 is
      function Id (X : Integer) return Integer is (X);
   end Nested_1;

   package body Nested_2 is
      function Id (X : Integer) return Integer with
        Refined_Post => Id'Result = X
      is
      begin
         return X;
      end Id;
   end Nested_2;

end P;
