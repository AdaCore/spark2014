package Math with
  SPARK_Mode
is
   subtype Value is Integer range 0 .. 10_000;
   type Index is range 1 .. 100;
   type Values is array (Index) of Value;

   function Sorted (V : Values) return Boolean is
     (for all J in Index'First .. Index'Last - 1 => V(J) <= V(J+1));

   subtype Sorted_Values is Values with
     Dynamic_Predicate => Sorted (Sorted_Values);

   procedure Shift_Right (V : in out Sorted_Values);

   procedure Div_All (V : in out Sorted_Values);

   procedure Div_All2 (V : in out Sorted_Values);

end Math;
