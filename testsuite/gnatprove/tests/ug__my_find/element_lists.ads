with SPARK.Containers.Formal.Doubly_Linked_Lists;

package Element_Lists with
  SPARK_Mode
is
   type Element_Type is new Integer;

   package Lists is new SPARK.Containers.Formal.Doubly_Linked_Lists (Element_Type);

end Element_Lists;
