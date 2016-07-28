package Recursive_Through_Type with SPARK_Mode is
   subtype Bad_Ty is Integer with
     Dynamic_Predicate => Bad_F (Integer (Bad_Ty));

   function Bad_F (X : Integer) return Boolean is (X in Bad_Ty) with
   Post => False;  --@POSTCONDITION:FAIL

end Recursive_Through_Type;
