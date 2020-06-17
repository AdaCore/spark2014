with Ada.Containers.Ordered_Sets;
with Ada.Containers.Ordered_Maps;

package Reproducer is

   package Int64_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Integer);

   package Int64_Set_Maps is new Ada.Containers.Ordered_Maps
     (Key_Type     => Integer,
      Element_Type => Int64_Sets.Set,
      "="          => Int64_Sets."=");

end Reproducer;
