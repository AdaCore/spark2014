-- -------------------------------------------------------------------------- --
-- cartesian.ads                Dependable Computing
-- -------------------------------------------------------------------------- --

-- This package illustrates difficulties we've had in proving cartesian product
-- of two arrays.

package cartesian with SPARK_Mode is

   -- An array of integers with unspecified Natural indices
   type integer_array is array (Natural range <>) of Integer;

   -- A pair of integers
   type pair_type is array (Positive range 1 .. 2) of Integer;

   -- An array of pairs of integers, with unspecified Natural indices
   type integer_product_type is array (Natural range <>) of pair_type;


   -- Predicate to test if an element is in an array.
   function in_array(element: integer;
                     arr: integer_array) return Boolean
   is
      (for some i in arr'Range =>
          arr(i) = element);

   -- Predicate to test if an element is in an array.
   function in_array(element: pair_type;
                     arr: integer_product_type) return Boolean
   is
      (for some i in arr'Range =>
          arr(i) = element);

   -- Convenience predicate to test if a left,right pair is in an array.
   function in_array(left: Integer;
                     right: Integer;
                     arr: integer_product_type) return Boolean
   is
      (in_array(pair_type'(left, right), arr));


   -- Compute the cartesian product of two arrays.
   function cartesian_product(array1: integer_array;
                              array2: integer_array) return integer_product_type
   with
     -- This precondition is for convenience, for making sure there are no
     -- overflow errors.
     Pre => (array1'Length < 255 and array2'Length < 255),

     -- This is half of the postcondition (all from input in output)
     Post => ((for all i in array1'Range =>
                 (for all j in array2'Range =>
                    in_array(pair_type'(array1(i), array2(j)),
                             cartesian_product'Result))));

     -- TODO: other half of postcondition (only from input in output)
end cartesian;
