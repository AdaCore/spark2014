procedure Base_Repr with SPARK_Mode is
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      V : Integer;
      N : List;
   end record;

   function Length (L : access List_Cell) return Natural is
     (if L = null then 0
      else 1 + Length (L.N)); --@OVERFLOW_CHECK:FAIL
begin
   null;
end Base_Repr;
