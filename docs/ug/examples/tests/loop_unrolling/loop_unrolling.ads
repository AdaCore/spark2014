package Loop_Unrolling with
  SPARK_Mode
is
   subtype Index is Integer range 1 .. 10;
   type Arr is array (Index) of Integer;

   procedure Init (A : out Arr) with
     Post => (for all J in Index => A(J) = J);

   function Sum (A : Arr) return Integer with
     Pre  => (for all J in Index => A(J) = J),
     Post => Sum'Result = (A'First + A'Last) * A'Length / 2;

end Loop_Unrolling;
