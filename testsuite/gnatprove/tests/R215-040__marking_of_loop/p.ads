with SPARK.Containers.Formal.Doubly_Linked_Lists;

package P with SPARK_Mode is

   package My_Lists is new
     SPARK.Containers.Formal.Doubly_Linked_Lists (Element_Type => Natural);

   package Not_In_SPARK with SPARK_Mode => Off is
      subtype Bad_Int is Natural;
   end Not_In_SPARK;

   procedure Dummy (L : My_Lists.List);

end;
