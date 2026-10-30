procedure Plain_Record with SPARK_Mode is
   type Rec (D : Integer) is record
      Value : Integer;
   end record;
   X : Rec (0) := (D => 0, Value => 0) with Potentially_Invalid;
begin
   pragma Assert (X.D = 0);
   pragma Assert (X.Value'Valid);
   pragma Assert (X.Value = 0);
   pragma Assert (X.Value /= 0); --@ASSERT:FAIL
end Plain_Record;
