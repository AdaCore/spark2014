pragma SPARK_Mode(On);

package use_unchecked_union is

   type small_array is array (0..2) of Integer;
   type big_array is array (0..3) of Integer;

   type small_record is record
      field1 : aliased Integer := 0;
      field2 : aliased small_array := (0,0,0);
   end record;

   type big_record is record
      field1 : aliased Integer := 0;
      field2 : aliased big_array := (0,0,0,0);
   end record;


   type myUnion (discr : Integer := 0) is record
      case discr is
         when 0 =>
            record1 : aliased small_record;
         when others =>
            record2 : aliased big_record;
      end case;
   end record;
--     pragma Unchecked_Union(myUnion);

   procedure doStuff (output : out myUnion;
                      num : in Integer)
   with Pre => not output'Constrained;

   procedure doStuff2 (output : out myUnion;
                      num : in Integer)
     with Pre => output.discr = num;

   procedure doStuff3 (output : out myUnion);

end use_unchecked_union;
