with Ada.Containers.Formal_Vectors;

package Fail is
   pragma SPARK_Mode (On);

   pragma Elaborate_Body;

   type X is limited private;

private

   Max : constant := 3;
   subtype T is integer range 1 .. Max;
   package My_Lists is new Ada.Containers.Formal_Vectors (T, Integer);
   subtype List is My_Lists.Vector (Max);

   type X is record
      Y : List;
   end record;

end Fail;
