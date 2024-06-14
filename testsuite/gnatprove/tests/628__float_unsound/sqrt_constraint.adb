procedure Sqrt_Constraint with SPARK_Mode => On is

   FAILING_CONSTANT_C : constant Float := 1.234567;

   subtype Small_Float_T is Float range -16_000.0 .. 16_000.0;

   function Bad_Conversion
     (Input : Float)
      return Float is (Input / FAILING_CONSTANT_C);

   subtype Failing_Type_T is
       Float range
       0.0 ..  Bad_Conversion (Small_Float_T'Last) *
                Bad_Conversion (Small_Float_T'Last);

   Maximal_Float : constant Float :=
           Small_Float_T'First * Small_Float_T'First +
            Small_Float_T'First * Small_Float_T'First;

   Failing_Assignment : Failing_Type_T;

begin
    Failing_Assignment := Maximal_Float; --@RANGE_CHECK:FAIL
end Sqrt_Constraint;
