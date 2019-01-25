with Ada.Containers.Formal_Vectors;
with Ada.Containers; use Ada.Containers;

package Sorted_Vectors is pragma SPARK_Mode (On);
   pragma Unevaluated_Use_Of_Old (Allow);

   type Element_Type is new Integer range 1 .. 100;

   function My_Lt (I1 : Element_Type; I2 : Element_Type) return Boolean is
     (I1 < I2);

   subtype Index_Type is Integer range 1 .. 100;

   package My_Vectors is new Ada.Containers.Formal_Vectors
     (Index_Type, Element_Type);
   use My_Vectors; use Formal_Model;

   package My_Sort is new Generic_Sorting ("<" => My_Lt);

   procedure My_Insert (Container : in out Vector;
                        New_Item  :        Element_Type;
                        Position  :    out Index_Type) with
     Pre  => Length (Container) < Container.Capacity,
     Post =>
       Position in First_Index (Container) .. Integer (Length (Container)) and then
     Length (Container) = Length (Container)'Old + 1 and then
     Element (Container, Position) = New_Item and then
     ((for all I in 1 .. Position - 1 =>
            Element (Container, I) = Element (Model (Container)'Old, I)) and
         (for all I in Position + 1 .. Integer (Length (Container)) =>
               Element (Container, I) = Element (Model (Container)'Old, I - 1)) and
           (if My_Sort.Formal_Model.M_Elements_Sorted (Model (Container)'Old)
                then My_Sort.Is_Sorted (Container)));

end Sorted_Vectors;
