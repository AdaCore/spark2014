package const is

   type My_Int is range 0 .. 1000;

   Global_Variable : My_Int := 0;

   subtype U is My_Int
     with Dynamic_Predicate => (Global_Variable + U) mod 2 = 0;
   --  all elements of S are even, but with a global variable
end;
