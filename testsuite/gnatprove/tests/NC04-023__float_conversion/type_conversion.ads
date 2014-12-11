package type_conversion
   with SPARK_Mode => On
is

   function Float_to_Long_Float (X : Float) return Long_Float
   is (Long_Float (X))
      with Pre  => (X >= Float'First and
                    X <= Float'Last),
           Post => (Float_to_Long_Float'Result >= Long_Float (Float'First) and --@POSTCONDITION:PASS
                    Float_to_Long_Float'Result <= Long_Float (Float'Last));

end type_conversion;
