procedure Dyn is
   function F return Integer is (1);
   X : String (F .. F) := (F - 1 => '0'); --@RANGE_CHECK:FAIL
begin
   null;
end Dyn;
