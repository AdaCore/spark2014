package Math_Utils is

   type Index is range 1 .. 1_000;
   type Vector is array (Index range <>) of Integer;

   function Max (V : Vector) return Integer
     with
       SPARK_Mode,
       Depends => (Max'Result => V),
       Pre  => V'Length > 0,
       Post => (for all E of V => Max'Result >= E)
                 and
               (for some Element of V => Max'Result = Element);
end Math_Utils;
