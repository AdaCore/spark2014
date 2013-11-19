package Swap_Add_Max_14
  with SPARK_Mode
is
   subtype Index      is Integer range 1..100;
   type    Array_Type is array (Index) of Integer;

   procedure Swap (X, Y : in out Integer)
     with Post => (X = Y'Old and Y = X'Old);

   function Add (X, Y : Integer) return Integer
     with Pre  => (if X >= 0 and Y >= 0 then X <= Integer'Last - Y
                   elsif X < 0 and Y < 0 then X >= Integer'First - Y),
          -- The precondition may be written as X + Y in Integer if
          -- an extended arithmetic mode is selected
          Post => Add'Result = X + Y;

   function Max (X, Y : Integer) return Integer
     with Post => Max'Result = (if X >= Y then X else Y);

   function Divide (X, Y : Integer) return Integer
     with Pre  => Y /= 0 and X > Integer'First and Y > Integer'First,
          Post => Divide'Result = X / Y;

   procedure Swap_Array_Elements(I, J : Index; A: in out Array_Type)
     with Post => A = A'Old'Update (I => A'Old (J),
                                    J => A'Old (I));
end Swap_Add_Max_14;
