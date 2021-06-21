with Ada.Numerics.Elementary_Functions; use Ada.Numerics.Elementary_Functions;

package Norm with SPARK_Mode is

   Max_Exact_Integer_Computation : constant := 2.0 ** 23;
   --  Upper bound of the interval on which integer computations are exact
   Float_Sqrt : constant Float := 2.0 ** 63;
   --  Safe bound for multiplication

   Max_Index : constant := 100;
   --  Number of elements in an array of values
   subtype Extended_Index is Natural range 0 .. Max_Index;
   subtype Index is Positive range 1 .. Max_Index;

   Max_Value : constant := 289.0;
   pragma Assert
     (Max_Exact_Integer_Computation / Float (Max_Index) >= Max_Value ** 2);
   pragma Assert
     (Max_Exact_Integer_Computation / Float (Max_Index)
      < (Max_Value + 1.0) ** 2);
   --  Biggest integer value for which the sum of squares is garanteed to be
   --  exact. We don't use Sqrt here to have a static value.

   subtype Value is Float range -Max_Value .. Max_Value;
   type Value_Array is array (Index) of Value;

   function Sum_Of_Squares_Rec
     (Values : Value_Array;
      I      : Extended_Index) return Float
   with
     Subprogram_Variant => (Decreases => I),
     Post => Sum_Of_Squares_Rec'Result =
         (if I = 0 then 0.0
          else Sum_Of_Squares_Rec (Values, I - 1) + Values (I) ** 2)
       and then Sum_Of_Squares_Rec'Result in
           0.0 .. Max_Value ** 2 * Float (I);

   Max_Norm : constant := 2890.0;
   pragma Assert (Max_Norm ** 2 = Float (Max_Index) * Max_Value ** 2);
   --  Maximum value the norm can take. We don't use Sqrt here to have a static
   --  value.

   subtype Norm_Type is Float range 0.0 .. Max_Norm;
   function Norm (Values : Value_Array) return Norm_Type with
     Post => Norm'Result = Sqrt (Sum_Of_Squares_Rec (Values, Max_Index));

end Norm;
