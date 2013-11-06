with Ada.Containers.Formal_Vectors;

package Fail is
   pragma SPARK_Mode (On);

   pragma Elaborate_Body;

   type X is private;

private

   Max : constant := 3;
   subtype T is integer range 1 .. Max;
   function Eq (E1 : T; E2 : T) return Boolean is (E1 = E2);
   package My_Lists is new Ada.Containers.Formal_Vectors (T, Integer, Eq);
   subtype List is My_Lists.Vector (Max);

   type X is record
      Y : List;
   end record;

end Fail;
