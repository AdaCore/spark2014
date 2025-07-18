pragma SPARK_Mode (On);

package body disjoint_union_simple is

   -- 2 procedures doing the same assignments to a union,
   -- the first using the discriminant, the second without.

   procedure doStuff (output : out myUnion) is
   begin
      output := (discr => 1, field2 => 1); -- @DISCRIMINANT_CHECK:FAIL
   end doStuff;
   -- Discriminant check might fail if output is constrained.

   procedure doStuff2 (output : out myUnion) is
   begin
      output.field2 := 1; -- @DISCRIMINANT_CHECK:FAIL
   end doStuff2;
   -- Discriminant isn't initialized in this procedure. The success of the
   -- assignment depends on what the discriminant happens to be in the object
   -- provided by the caller.

end disjoint_union_simple;
