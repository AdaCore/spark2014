-- This test is similar to Q531-032__uncheck_union except that:
-- * It uses a pure Ada union instead of the C-style unchecked union.
-- * The precondition about 'Constrained for doStuff is removed to trigger a
--   potential discriminant check failure.
-- * The data structure is simplified to not contain arrays.

pragma SPARK_Mode (On);

package disjoint_union is

   type small_array is array (0 .. 2) of Integer;
   type big_array is array (0 .. 3) of Integer;

   type small_record is record
      field1 : aliased Integer := 0;
      field2 : aliased small_array := (0, 0, 0);
   end record;

   type big_record is record
      field1 : aliased Integer := 0;
      field2 : aliased big_array := (0, 0, 0, 0);
   end record;

   type myUnion (discr : Integer := 0) is record
      case discr is
         when 0 =>
            record1 : aliased small_record;

         when others =>
            record2 : aliased big_record;
      end case;
   end record;

   procedure doStuff (output : out myUnion; num : in Integer);

   procedure doStuff2 (output : out myUnion; num : in Integer);

end disjoint_union;
