package body recursion with SPARK_Mode is

   -- Count the number of true items in an array recursively. The postcondition
   -- given does not directly express the count, but merely states that the
   -- count is bounded above by index - first + 1, which is the number of items
   -- examined thus far.
   function count_true_recursive(arr: example_array;
                                 index: Positive) return Natural is
      count: Natural;
      current_increment: Natural;
   begin
      if arr(index) then
         current_increment := 1;
      else
         current_increment := 0;
      end if;

      if index = arr'First then
         count := current_increment;
      else

         -- This is the recusive call. Comment this and uncomment the direct
         -- assignment of zero when the Assert below is uncommented to restore
         -- the proof.
         count := current_increment + count_true_recursive(arr, index - 1);

         -- This eliminates the recursive call and makes the postcondition
         -- trivially true. Comment the above and uncomment this when the
         -- Assert below is uncommented to restore the proof.
         -- count := 0;
      end if;

      return count;
   end count_true_recursive;

   -- Count the number of true tems in an array using a loop. As above, the
   -- postcondition merely states that the count is bounded above by the length
   -- of the array.
   function count_true_loop(arr: example_array) return Natural is
      count: Natural := 0;
   begin
      for index in arr'Range loop
         pragma Loop_Invariant(count < (index - arr'First + 1));

         -- This assert is a simple restatement of the postcondition of the
         -- recursive function, above. When uncommented and when the recursive
         -- call is made, above, this assert fails to prove - even though the
         -- provers do not suggest that there is a problem with the recursive
         -- function or the postcondition.
         -- pragma Assert(count_true_recursive(arr, index) <= (index - arr'First + 1));

         if arr(index) then
            count := count + 1;
         end if;
      end loop;

      return count;
   end count_true_loop;

end recursion;
