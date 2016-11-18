package A with SPARK_Mode => On is

   type Index_Type is range 1 .. 10;
   type Element_Type is new Integer range 53 .. 100;
   type Element_Float is digits 6 range 15.0 .. 1.0E35;
   type Array_Type is array (Index_Type) of Element_Type;
   type Array_Float is array (Index_Type) of Element_Float;

   procedure Test (A : Array_Type) with
     Pre => (for all I in A'First + 1 .. A'Last =>
               A (I - 1) < A (I));

   procedure Test_Float (A : Array_Float) with
     Pre => (for all I in A'First + 1 .. A'Last =>
               A (I - 1) < A (I));

end A;
