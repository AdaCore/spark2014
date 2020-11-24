package P
  with SPARK_Mode => On
is
   subtype Sqrt_Domain is Integer range 0 .. 2**31 - 1;
   subtype Sqrt_Range  is Integer range 0 .. 46340;
   subtype Big is Long_Long_Integer;

   --  truncated natural square root, binary chop search
   function Sqrt_Binary (X : in Sqrt_Domain) return Sqrt_Range
     with Post => Sqrt_Binary'Result * Sqrt_Binary'Result <= X
       and then Big (X) < Big (Sqrt_Binary'Result + 1) * Big (Sqrt_Binary'Result + 1);

   --  truncated natural square root, Von Neumann's algorithm
   function Sqrt_Von_Neumann (X : in Sqrt_Domain) return Sqrt_Range
     with Post => Sqrt_Von_Neumann'Result * Sqrt_Von_Neumann'Result <= X
       and then Big (X) < Big (Sqrt_Von_Neumann'Result + 1) * Big (Sqrt_Von_Neumann'Result + 1);

end P;
