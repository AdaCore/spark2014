procedure Function_Result with SPARK_Mode is
   type Rec (D : Integer) is record
      Value : Integer;
   end record;
   subtype Fixed is Rec (0);

   function Make return Fixed with
     Post => Make'Result.Value = 42,
     Potentially_Invalid => Make'Result
   is
   begin
      return (D => 0, Value => 42);
   end Make;

   X : Fixed := Make with Potentially_Invalid;
begin
   pragma Assert (X.D = 0);
   pragma Assert (X.Value'Valid);
   pragma Assert (X.Value = 42);
   pragma Assert (X.Value /= 42); --@ASSERT:FAIL
end Function_Result;
