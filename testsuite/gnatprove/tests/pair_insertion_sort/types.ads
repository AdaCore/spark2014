package Types with
  SPARK_Mode
is
   subtype Index is Integer range 0 .. Integer'Last - 1;
   type Arr is array (Index range <>) of Integer
     with Predicate => Arr'First = 0;
end Types;
