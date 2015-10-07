package const is

   type My_Int is range 0 .. 1000;

   Global_Constant : constant My_Int := 0;

   subtype U is My_Int
     with Dynamic_Predicate => (Global_Constant + U) mod 2 = 0;
   --  all elements of S are even, but with a global constant
end;
