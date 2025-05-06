pragma SPARK_Mode (On);

package body disjoint_union is

   -- 2 procedures doing the same assignments to a union,
   -- the first using the discriminant, the second without.

   procedure doStuff (output : out myUnion; num : in Integer) is
   begin
      case (num) is
         when 0 =>
            output := (discr => 0, record1 => (1, (1, 2, 3))); -- @DISCRIMINANT_CHECK:FAIL

         when 1 =>
            output := (discr => 1, record2 => (1, (1, 2, 3, 4))); -- @DISCRIMINANT_CHECK:FAIL

         when others =>
            output := (discr => 1, record2 => (0, (0, 0, 0, 0))); -- @DISCRIMINANT_CHECK:FAIL
      end case;
   end doStuff;
   -- Discriminant check might fail if output is constrained.

   procedure doStuff2 (output : out myUnion; num : in Integer) is
   begin
      case (num) is
         when 0 =>
            output.record1.field1 := 1; -- @DISCRIMINANT_CHECK:FAIL
            output.record1.field2 := (1, 2, 3); -- @DISCRIMINANT_CHECK:FAIL

         when 1 =>
            output.record2.field1 := 1; -- @DISCRIMINANT_CHECK:FAIL
            output.record2.field2 := (1, 2, 3, 4); -- @DISCRIMINANT_CHECK:FAIL

         when others =>
            output.record2.field1 := 0; -- @DISCRIMINANT_CHECK:FAIL
            output.record2.field2 := (others => 0); -- @DISCRIMINANT_CHECK:FAIL
      end case;
   end doStuff2;
   -- Discriminant isn't initialized in this procedure. The success of the
   -- assignment depends on what the discriminant happens to be in the object
   -- provided by the caller.

end disjoint_union;
