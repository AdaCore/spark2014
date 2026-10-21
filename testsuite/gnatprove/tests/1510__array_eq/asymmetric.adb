procedure Asymmetric with SPARK_Mode is
   type R is record
      V : Integer;
   end record;
   function "=" (L, R : Asymmetric.R) return Boolean is (L.V <= R.V);
   type Arr is array (Positive range <>) of R;
   A : constant Arr := (1 => (V => 0));
   B : constant Arr := (1 => (V => 1));
begin
   pragma Assert (A = B);
   pragma Assert (B = A); -- @ASSERT:FAIL
end Asymmetric;
