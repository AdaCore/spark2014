procedure Array_Control with SPARK_Mode is
   type Rec (D : Integer) is record
      Value : Integer;
   end record;
   type Arr is array (Positive range <>) of Rec (0);
   X : Arr (1 .. 2) := (others => (D => 0, Value => 42))
     with Potentially_Invalid;
begin
   pragma Assert (X'First = 1 and X'Last = 2);
   pragma Assert (X (1).D = 0);
   pragma Assert (X (1).Value'Valid);
   pragma Assert (X (2).Value = 42);
   pragma Assert (X (2).Value = 0); --@ASSERT:FAIL
end Array_Control;
