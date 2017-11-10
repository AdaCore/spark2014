-- -------------------------------------------------------------------------- --
-- cartesian.ads                Dependable Computing
-- -------------------------------------------------------------------------- --

-- This package illustrates difficulties we've had in proving cartesian product
-- of two arrays.
package body cartesian with SPARK_Mode is

   -- Compute the cartesian product of two arrays.
   function cartesian_product(array1: integer_array;
                              array2: integer_array) return integer_product_type
   is
      result_length: constant Natural := array1'Length * array2'Length;

      result: integer_product_type(1 .. result_length) :=
        (others => pair_type'(0,0));

      result_index: Natural := 0;
   begin
      for index1 in array1'Range loop
         for index2 in array2'Range loop
            result_index := result_index + 1;

            result(result_index) := pair_type'(array1(index1), array2(index2));

            -- Prove that our index math is correct, inductively
            pragma Loop_Invariant(result_index = (index1 - array1'First) * array2'Length + (index2 - array2'First) + 1);

            -- Prove that we've made the correct assignment up to this point in
            -- the inner loop.
            pragma Loop_Invariant((for all j in array2'First .. index2 =>
                                     result((index1 - array1'First)*array2'Length + (j - array2'First) + 1)(1) = array1(index1)));
            pragma Loop_Invariant((for all j in array2'First .. index2 =>
                                     result((index1 - array1'First)*array2'Length + (j - array2'First) + 1)(2) = array2(j)));
         end loop;

            -- Prove that our index math is correct, inductively
         pragma Loop_Invariant(result_index = (index1 - array1'First + 1) * array2'Length);

         -- These both restate the inner loop and do so inductively. (They work
         -- as asserts, too). With these both enabled, the array index check
         -- fails on the second of the next two invariants, unless the timeout
         -- is very large.
--           pragma Loop_Invariant((for all j in array2'Range =>
--                                    result((index1 - array1'First)*array2'Length + (j - array2'First) + 1)(1) = array1(index1)));
--           pragma Loop_Invariant((for all j in array2'Range =>
--                                    result((index1 - array1'First)*array2'Length + (j - array2'First) + 1)(2) = array2(j)));

         -- TODO: Neither of these prove, although they should, as they are
         -- obviously true from the above. Additionally, with the above enabled,
         -- the array-index check fails for the second of these, unless the
         -- timeout is very large.
         --
         -- Note that these don't prove with all provers, at level 4, with a
         -- huge timeout (3600).
         --
         -- The issue may be related to the frame condition.
         pragma Loop_Invariant((for all i in array1'First .. index1 =>
                                  (for all j in array2'Range =>
                                     result((i - array1'First)*array2'Length + (j - array2'First) + 1)(1) = array1(i))));
         pragma Loop_Invariant((for all i in array1'First .. index1 =>
                                  (for all j in array2'Range =>
                                     result((i - array1'First)*array2'Length + (j - array2'First) + 1)(2) = array2(j))));
      end loop;

      -- Follow from the loop invariants and prove our postcondition.
      pragma Assert((for all i in array1'Range =>
                       (for all j in array2'Range =>
                          result((i - array1'First)*array2'Length + (j - array2'First) + 1)(1) = array1(i))));
      pragma Assert((for all i in array1'Range =>
                       (for all j in array2'Range =>
                          result((i - array1'First)*array2'Length + (j - array2'First) + 1)(2) = array2(j))));

      return result;
   end cartesian_product;


end cartesian;
