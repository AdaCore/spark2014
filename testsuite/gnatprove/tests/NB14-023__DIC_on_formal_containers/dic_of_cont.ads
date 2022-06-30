with Ada.Containers; use Ada.Containers;
with SPARK.Containers.Formal.Doubly_Linked_Lists;
with SPARK.Containers.Formal.Hashed_Maps;
with SPARK.Containers.Formal.Hashed_Sets;
with SPARK.Containers.Formal.Ordered_Maps;
with SPARK.Containers.Formal.Ordered_Sets;
with SPARK.Containers.Formal.Vectors;

package DIC_Of_Cont with SPARK_Mode is
   function Hash (Key : Natural) return Hash_Type is (Hash_Type (Key));
   package My_DLLI is new
     SPARK.Containers.Formal.Doubly_Linked_Lists (Element_Type => Natural);
   package My_HAMA is new
     SPARK.Containers.Formal.Hashed_Maps (Key_Type => Natural,
                                          Element_Type => Natural,
                                          Hash => Hash,
                                          Equivalent_Keys => "=");
   package My_HASE is new
     SPARK.Containers.Formal.Hashed_Sets (Element_Type => Natural,
                                          Hash => Hash,
                                          Equivalent_Elements => "=");
   package My_ORMA is new
     SPARK.Containers.Formal.Ordered_Maps (Key_Type => Natural,
                                           Element_Type => Natural);
   package My_ORSE is new
     SPARK.Containers.Formal.Ordered_Sets (Element_Type => Natural);
   package My_FOVE is new
     SPARK.Containers.Formal.Vectors (Index_Type => Positive,
                                      Element_Type => Natural);

   procedure Main (Capacity : Count_Type);
end DIC_Of_Cont;
