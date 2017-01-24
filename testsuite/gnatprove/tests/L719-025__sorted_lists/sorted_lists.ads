with Ada.Containers.Formal_Doubly_Linked_Lists;
with Ada.Containers; use Ada.Containers;

package Sorted_Lists is pragma SPARK_Mode (On);

   type Element_Type is new Integer range 1 .. 100;

   function My_Eq (I1 : Element_Type; I2 : Element_Type) return Boolean is
     (I1 = I2);

   function My_Lt (I1 : Element_Type; I2 : Element_Type) return Boolean is
     (I1 < I2);

   package My_Lists is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Element_Type);
   use My_Lists; use Formal_Model;

   package My_Sort is new Generic_Sorting ("<" => My_Lt);

   procedure My_Insert (Container : in out List;
                        New_Item  :        Element_Type;
                        Position  :    out Cursor) with
     Pre  => Length (Container) < Container.Capacity,
     Post =>
       Has_Element (Container, Position) and then
     Element (Container, Position) = New_Item and then
     (for all I in 1 .. P.Get (Positions (Container), Position) - 1 =>
        Element (Model (Container), I) = Element (Model (Container'Old), I))
     and then
     (for all I in P.Get (Positions (Container), Position) .. Length (Container) - 1 =>
        Element (Model (Container), I + 1) = Element (Model (Container'Old), I))
     and then
       (if My_Sort.Is_Sorted (Container'Old) then My_Sort.Is_Sorted (Container));

end Sorted_Lists;
