-- This test is similar to Q531-032__uncheck_union except that:
-- * It uses a pure Ada union instead of the C-style unchecked union.
-- * The precondition about 'Constrained for doStuff is removed to trigger a
--   potential discriminant check failure.
-- * The data structure is simplified to not contain arrays or records.

pragma SPARK_Mode (On);

package disjoint_union_simple is

   type myUnion (discr : Integer := 0) is record
      case discr is
         when 0 =>
            field1 : aliased Integer := 0;
         when others =>
            field2 : aliased Integer := 0;
      end case;
   end record;

   procedure doStuff (output : out myUnion);

   procedure doStuff2 (output : out myUnion);

end disjoint_union_simple;
