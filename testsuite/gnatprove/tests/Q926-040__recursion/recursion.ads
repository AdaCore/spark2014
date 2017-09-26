-- Example package for discussion with AdaCore. The problem explored centers
-- around apparent inability of the prover to reason about the recursive
-- function.
package recursion with SPARK_Mode is
   -- Simple array type for demonstration. Use of Positive means that the count
   -- is bounded above by Natural (note that an array with a Natural range need
   -- not have a Natural length).
   type example_array is array (Positive range <>) of Boolean;


   -- Count the number of true items in an array recursively. The postcondition
   -- given does not directly express the count, but merely states that the
   -- count is bounded above by index - first + 1, which is the number of items
   -- examined thus far.
   function count_true_recursive(arr: example_array;
                                 index: Positive) return Natural with
     Pre => (arr'First < arr'Last and arr'First <= index and index <= arr'Last),
     Post => (count_true_recursive'Result <= (index - arr'First + 1));
--   pragma Annotate (GNATprove, Terminating, count_true_recursive);

   -- Count the number of true tems in an array using a loop. As above, the
   -- postcondition merely states that the count is bounded above by the length
   -- of the array.
   function count_true_loop(arr: example_array) return Natural with
     Pre => (arr'First < arr'Last),
     Post => (count_true_loop'Result <= arr'Length);

end recursion;
