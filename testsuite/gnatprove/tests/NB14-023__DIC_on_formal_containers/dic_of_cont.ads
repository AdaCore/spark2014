with Ada.Containers; use Ada.Containers;
with Ada.Containers.Formal_Doubly_Linked_Lists;
with Ada.Containers.Formal_Hashed_Maps;
with Ada.Containers.Formal_Hashed_Sets;
with Ada.Containers.Formal_Ordered_Maps;
with Ada.Containers.Formal_Ordered_Sets;
with Ada.Containers.Formal_Vectors;

package DIC_Of_Cont with SPARK_Mode is
   function Hash (Key : Natural) return Hash_Type is (Hash_Type (Key));
   package My_DLLI is new
     Formal_Doubly_Linked_Lists (Element_Type => Natural);
   package My_HAMA is new
     Formal_Hashed_Maps (Key_Type => Natural,
                         Element_Type => Natural,
                         Hash => Hash,
                         Equivalent_Keys => "=");
   package My_HASE is new
     Formal_Hashed_Sets (Element_Type => Natural,
                         Hash => Hash,
                         Equivalent_Elements => "=");
   package My_ORMA is new
     Formal_Ordered_Maps (Key_Type => Natural,
                          Element_Type => Natural);
   package My_ORSE is new
     Formal_Ordered_Sets (Element_Type => Natural);
   package My_FOVE is new
     Formal_Vectors (Index_Type => Positive,
                     Element_Type => Natural);

   procedure Main (Capacity : Count_Type);
end DIC_Of_Cont;
