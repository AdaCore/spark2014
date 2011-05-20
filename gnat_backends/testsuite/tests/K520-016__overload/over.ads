package Over is
   type My_Int is range 1 .. 10;
   function F (X : Integer) return Integer
      with Post => (F'Result = X);
   function F (Z : My_Int) return My_Int;

   procedure G;
end Over;
