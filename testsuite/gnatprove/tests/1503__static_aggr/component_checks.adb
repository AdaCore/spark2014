procedure Component_Checks (Choice : Positive; Bound : Positive; Value : Integer)
  with SPARK_Mode
is
   subtype Dynamic_Range is Integer range 1 .. Bound;
   type Dynamic_Array is array (1 .. 1) of Dynamic_Range;

   subtype Even is Integer range 0 .. 10
     with Dynamic_Predicate => Even mod 2 = 0;
   type Even_Array is array (1 .. 1) of Even;

   type Positive_Array is array (1 .. 1) of Positive;
begin
   case Choice is
      when 1 =>
         declare
            D : constant Dynamic_Array := [2]; -- @RANGE_CHECK:FAIL
         begin
            pragma Assert (D (1) = 2);
         end;
      when 2 =>
         declare
            E : constant Even_Array := [3]; -- @PREDICATE_CHECK:FAIL
         begin
            pragma Assert (E (1) = 3);
         end;
      when others =>
         declare
            P : constant Positive_Array := [Value]; -- @RANGE_CHECK:FAIL
         begin
            pragma Assert (P (1) = Value);
         end;
   end case;
end Component_Checks;
